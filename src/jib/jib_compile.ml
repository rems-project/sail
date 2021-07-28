(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Ast
open Ast_defs
open Ast_util
open Jib
open Jib_util
open Type_check
open Value2

open Anf

let opt_memo_cache = ref false

let optimize_aarch64_fast_struct = ref false

let (gensym, reset_gensym_counter) = symbol_generator "gs"
let ngensym () = name (gensym ())

(**************************************************************************)
(* 4. Conversion to low-level AST                                         *)
(**************************************************************************)

(** We now use a low-level AST called Jib (see language/bytecode.ott)
   that is only slightly abstracted away from C. To be succint in
   comments we usually refer to this as Sail IR or IR rather than
   low-level AST repeatedly.

   The general idea is ANF expressions are converted into lists of
   instructions (type instr) where allocations and deallocations are
   now made explicit. ANF values (aval) are mapped to the cval type,
   which is even simpler still. Some things are still more abstract
   than in C, so the type definitions follow the sail type definition
   structure, just with typ (from ast.ml) replaced with
   ctyp. Top-level declarations that have no meaning for the backend
   are not included at this level.

   The convention used here is that functions of the form compile_X
   compile the type X into types in this AST, so compile_aval maps
   avals into cvals. Note that the return types for these functions
   are often quite complex, and they usually return some tuple
   containing setup instructions (to allocate memory for the
   expression), cleanup instructions (to deallocate that memory) and
   possibly typing information about what has been translated. **)

(* FIXME: This stage shouldn't care about this *)
let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

let rec is_bitvector = function
  | [] -> true
  | AV_lit (L_aux (L_zero, _), _) :: avals -> is_bitvector avals
  | AV_lit (L_aux (L_one, _), _) :: avals -> is_bitvector avals
  | _ :: _ -> false

let rec value_of_aval_bit = function
  | AV_lit (L_aux (L_zero, _), _) -> Sail2_values.B0
  | AV_lit (L_aux (L_one, _), _) -> Sail2_values.B1
  | _ -> assert false

let is_ct_enum = function
  | CT_enum _ -> true
  | _ -> false

let is_ct_variant = function
  | CT_variant _ -> true
  | _ -> false

let is_ct_tup = function
  | CT_tup _ -> true
  | _ -> false

let is_ct_list = function
  | CT_list _ -> true
  | _ -> false

let is_ct_vector = function
  | CT_vector _ -> true
  | _ -> false

let is_ct_struct = function
  | CT_struct _ -> true
  | _ -> false

let is_ct_ref = function
  | CT_ref _ -> true
  | _ -> false

let iblock1 = function
  | [instr] -> instr
  | instrs -> iblock instrs

let ctor_bindings = List.fold_left (fun map (uid, ctyp) -> UBindings.add uid ctyp map) UBindings.empty

(** The context type contains two type-checking
   environments. ctx.local_env contains the closest typechecking
   environment, usually from the expression we are compiling, whereas
   ctx.tc_env is the global type checking environment from
   type-checking the entire AST. We also keep track of local variables
   in ctx.locals, so we know when their type changes due to flow
   typing. *)
type ctx =
  { records : (ctyp UBindings.t) Bindings.t;
    enums : IdSet.t Bindings.t;
    variants : (ctyp UBindings.t) Bindings.t;
    valspecs : (ctyp list * ctyp) Bindings.t;
    local_env : Env.t;
    tc_env : Env.t;
    locals : (mut * ctyp) Bindings.t;
    letbinds : int list;
    no_raw : bool;
  }

let initial_ctx env =
  { records = Bindings.empty;
    enums = Bindings.empty;
    variants = Bindings.empty;
    valspecs = Bindings.empty;
    local_env = env;
    tc_env = env;
    locals = Bindings.empty;
    letbinds = [];
    no_raw = false;
  }

module type Config = sig
  val convert_typ : ctx -> typ -> ctyp
  val optimize_anf : ctx -> typ aexp -> typ aexp
  val unroll_loops : int option
  val specialize_calls : bool
  val ignore_64 : bool
  val struct_value : bool
  val use_real : bool
  val branch_coverage : out_channel option
  val track_throw : bool
end

let name_or_global ctx id =
  if Env.is_register id ctx.local_env || IdSet.mem id (Env.get_toplevel_lets ctx.local_env) then
    global id
  else
    name id

module Make(C: Config) = struct

let ctyp_of_typ ctx typ = C.convert_typ ctx typ

let rec chunkify n xs =
  match Util.take n xs, Util.drop n xs with
  | xs, [] -> [xs]
  | xs, ys -> xs :: chunkify n ys

let coverage_branch_count = ref 0

let coverage_loc_args l =
  match Reporting.simp_loc l with
  | None -> None
  | Some (p1, p2) ->
     Some (Printf.sprintf "\"%s\", %d, %d, %d, %d"
             (String.escaped p1.pos_fname) p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum (p2.pos_cnum - p2.pos_bol))
 
let coverage_branch_reached l =
  let branch_id = !coverage_branch_count in
  incr coverage_branch_count;
  branch_id,
  (match C.branch_coverage with
   | Some _ ->
      begin match coverage_loc_args l with
      | None -> []
      | Some args ->
         [iraw (Printf.sprintf "sail_branch_reached(%d, %s);" branch_id args)]
      end
   | _ -> []
  )

let append_into_block instrs instr =
  match instrs with
  | [] -> instr
  | _ -> iblock (instrs @ [instr])

let rec find_aexp_loc (AE_aux (e, _, l)) =
  match Reporting.simp_loc l with
  | Some _ -> l
  | None ->
    match e with
    | AE_cast (e',_) -> find_aexp_loc e'
    | _ -> l

let coverage_branch_taken branch_id aexp =
  match C.branch_coverage with
  | None -> []
  | Some out -> begin
     match coverage_loc_args (find_aexp_loc aexp) with
     | None -> []
     | Some args ->
        Printf.fprintf out "%s\n" ("B " ^ args);
        [iraw (Printf.sprintf "sail_branch_taken(%d, %s);" branch_id args)]
    end

let coverage_function_entry id l =
  match C.branch_coverage with
  | None -> []
  | Some out -> begin
     match coverage_loc_args l with
     | None -> []
     | Some args ->
        Printf.fprintf out "%s\n" ("F " ^ args);
        [iraw (Printf.sprintf "sail_function_entry(\"%s\", %s);" (string_of_id id) args)]
    end

let rec compile_aval l ctx = function
  | AV_cval (cval, typ) ->
     let ctyp = cval_ctyp cval in
     let ctyp' = ctyp_of_typ ctx typ in
     if not (ctyp_equal ctyp ctyp') then
       let gs = ngensym () in
       [iinit l ctyp' gs cval], V_id (gs, ctyp'), [iclear ctyp' gs]
     else
       [], cval, []

  | AV_id (id, typ) ->
     begin match Bindings.find_opt id ctx.locals with
     | Some (_, ctyp) ->
        [], V_id (name id, ctyp), []
     | None ->
        [], V_id (name_or_global ctx id, ctyp_of_typ ctx (lvar_typ typ)), []
     end

  | AV_ref (id, typ) ->
     [], V_lit (VL_ref (string_of_id id), CT_ref (ctyp_of_typ ctx (lvar_typ typ))), []

  | AV_lit (L_aux (L_string str, _), typ) ->
     [], V_lit ((VL_string (String.escaped str)), ctyp_of_typ ctx typ), []

  | AV_lit (L_aux (L_num n, _), typ) when C.ignore_64 ->
     [], V_lit ((VL_int n), ctyp_of_typ ctx typ), []

  | AV_lit (L_aux (L_num n, _), typ) when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
     let gs = ngensym () in
     [iinit l CT_lint gs (V_lit (VL_int n, CT_fint 64))],
     V_id (gs, CT_lint),
     [iclear CT_lint gs]

  | AV_lit (L_aux (L_num n, _), typ) ->
     let gs = ngensym () in
     [iinit l CT_lint gs (V_lit (VL_string (Big_int.to_string n), CT_string))],
     V_id (gs, CT_lint),
     [iclear CT_lint gs]

  | AV_lit (L_aux (L_zero, _), _) -> [], V_lit (VL_bit Sail2_values.B0, CT_bit), []
  | AV_lit (L_aux (L_one, _), _) -> [], V_lit (VL_bit Sail2_values.B1, CT_bit), []

  | AV_lit (L_aux (L_true, _), _) -> [], V_lit (VL_bool true, CT_bool), []
  | AV_lit (L_aux (L_false, _), _) -> [], V_lit (VL_bool false, CT_bool), []

  | AV_lit (L_aux (L_real str, _), _) ->
     if C.use_real then
       [], V_lit (VL_real str, CT_real), []
     else
       let gs = ngensym () in
       [iinit l CT_real gs (V_lit (VL_string str, CT_string))],
       V_id (gs, CT_real),
       [iclear CT_real gs]

  | AV_lit (L_aux (L_unit, _), _) -> [], V_lit (VL_unit, CT_unit), []

  | AV_lit (L_aux (L_undef, _), typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     [], V_lit (VL_undefined, ctyp), []

  | AV_lit (L_aux (_, l) as lit, _) ->
     raise (Reporting.err_general l ("Encountered unexpected literal " ^ string_of_lit lit ^ " when converting ANF represention into IR"))

  | AV_tuple avals ->
     let elements = List.map (compile_aval l ctx) avals in
     let cvals = List.map (fun (_, cval, _) -> cval) elements in
     let setup = List.concat (List.map (fun (setup, _, _) -> setup) elements) in
     let cleanup = List.concat (List.rev (List.map (fun (_, _, cleanup) -> cleanup) elements)) in
     let tup_ctyp = CT_tup (List.map cval_ctyp cvals) in
     let gs = ngensym () in
     setup
     @ [idecl l tup_ctyp gs]
     @ List.mapi (fun n cval -> icopy l (CL_tuple (CL_id (gs, tup_ctyp), n)) cval) cvals,
     V_id (gs, CT_tup (List.map cval_ctyp cvals)),
     [iclear tup_ctyp gs]
     @ cleanup

  | AV_record (fields, typ) when C.struct_value ->
     let ctyp = ctyp_of_typ ctx typ in
     let gs = ngensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup,
       ((id, []), cval),
       field_cleanup
     in
     let field_triples = List.map compile_fields (Bindings.bindings fields) in
     let setup = List.concat (List.map (fun (s, _, _) -> s) field_triples) in
     let fields = List.map (fun (_, f, _) -> f) field_triples in
     let cleanup = List.concat (List.map (fun (_, _, c) -> c) field_triples) in
     [idecl l ctyp gs],
     V_struct (fields, ctyp),
     [iclear ctyp gs]

  | AV_record (fields, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let gs = ngensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup
       @ [icopy l (CL_field (CL_id (gs, ctyp), (id, []))) cval]
       @ field_cleanup
     in
     [idecl l ctyp gs]
     @ List.concat (List.map compile_fields (Bindings.bindings fields)),
     V_id (gs, ctyp),
     [iclear ctyp gs]

  | AV_vector ([], typ) ->
     let vector_ctyp = ctyp_of_typ ctx typ in
     begin match ctyp_of_typ ctx typ with
     | CT_fbits (0, ord) ->
           [], V_lit (VL_bits ([], ord), vector_ctyp), []
        | _ ->
        let gs = ngensym () in
        [idecl l vector_ctyp gs;
         iextern (CL_id (gs, vector_ctyp)) (mk_id "internal_vector_init", []) [V_lit (VL_int Big_int.zero, CT_fint 64)]],
        V_id (gs, vector_ctyp),
        [iclear vector_ctyp gs]
     end

  (* Convert a small bitvector to a uint64_t literal. *)
  | AV_vector (avals, typ) when is_bitvector avals && (List.length avals <= 64 || C.ignore_64) ->
     begin
       let bitstring = List.map value_of_aval_bit avals in
       let len = List.length avals in
       match destruct_bitvector ctx.tc_env typ with
       | Some (_, Ord_aux (Ord_inc, _)) ->
          [], V_lit (VL_bits (bitstring, false), CT_fbits (len, false)), []
       | Some (_, Ord_aux (Ord_dec, _)) ->
          [], V_lit (VL_bits (bitstring, true), CT_fbits (len, true)), []
       | Some _ ->
          raise (Reporting.err_general l "Encountered order polymorphic bitvector literal")
       | None ->
          raise (Reporting.err_general l "Encountered vector literal without vector type")
     end

  (* Convert a bitvector literal that is larger than 64-bits to a
     variable size bitvector, converting it in 64-bit chunks. *)
  | AV_vector (avals, typ) when is_bitvector avals ->
     let len = List.length avals in
     let bitstring avals = VL_bits (List.map value_of_aval_bit avals, true) in
     let first_chunk = bitstring (Util.take (len mod 64) avals) in
     let chunks = Util.drop (len mod 64) avals |> chunkify 64 |> List.map bitstring in
     let gs = ngensym () in
     [iinit l (CT_lbits true) gs (V_lit (first_chunk, CT_fbits (len mod 64, true)))]
     @ List.map (fun chunk -> ifuncall l (CL_id (gs, CT_lbits true))
                                (mk_id "append_64", [])
                                [V_id (gs, CT_lbits true); V_lit (chunk, CT_fbits (64, true))]) chunks,
     V_id (gs, CT_lbits true),
     [iclear (CT_lbits true) gs]

  (* If we have a bitvector value, that isn't a literal then we need to set bits individually. *)
  | AV_vector (avals, Typ_aux (Typ_app (id, [_; A_aux (A_order ord, _)]), _))
       when string_of_id id = "bitvector" && List.length avals <= 64 ->
     let len = List.length avals in
     let direction = match ord with
       | Ord_aux (Ord_inc, _) -> false
       | Ord_aux (Ord_dec, _) -> true
       | Ord_aux (Ord_var _, _) -> raise (Reporting.err_general l "Polymorphic vector direction found")
     in
     let gs = ngensym () in
     let ctyp = CT_fbits (len, direction) in
     let mask i = VL_bits (Util.list_init (63 - i) (fun _ -> Sail2_values.B0) @ [Sail2_values.B1] @ Util.list_init i (fun _ -> Sail2_values.B0), direction) in
     let aval_mask i aval =
       let setup, cval, cleanup = compile_aval l ctx aval in
       match cval with
       | V_lit (VL_bit Sail2_values.B0, _) -> []
       | V_lit (VL_bit Sail2_values.B1, _) ->
          [icopy l (CL_id (gs, ctyp)) (V_call (Bvor, [V_id (gs, ctyp); V_lit (mask i, ctyp)]))]
       | _ ->
          setup
          @ [iextern (CL_id (gs, ctyp))
                     (mk_id "update_fbits", [])
                     [V_id (gs, ctyp); V_lit (VL_int (Big_int.of_int i), CT_constant (Big_int.of_int i)); cval]]
          @ cleanup
     in
     [idecl l ctyp gs;
      icopy l (CL_id (gs, ctyp)) (V_lit (VL_bits (Util.list_init len (fun _ -> Sail2_values.B0), direction), ctyp))]
     @ List.concat (List.mapi aval_mask (List.rev avals)),
     V_id (gs, ctyp),
     []

  (* Compiling a vector literal that isn't a bitvector *)
  | AV_vector (avals, Typ_aux (Typ_app (id, [_; A_aux (A_order ord, _); A_aux (A_typ typ, _)]), _))
       when string_of_id id = "vector" ->
     let len = List.length avals in
     let direction = match ord with
       | Ord_aux (Ord_inc, _) -> false
       | Ord_aux (Ord_dec, _) -> true
       | Ord_aux (Ord_var _, _) -> raise (Reporting.err_general l "Polymorphic vector direction found")
     in
     let vector_ctyp = CT_vector (direction, ctyp_of_typ ctx typ) in
     let gs = ngensym () in
     let aval_set i aval =
       let setup, cval, cleanup = compile_aval l ctx aval in
       setup
       @ [iextern (CL_id (gs, vector_ctyp))
                  (mk_id "internal_vector_update", [])
                  [V_id (gs, vector_ctyp); V_lit (VL_int (Big_int.of_int i), CT_fint 64); cval]]
       @ cleanup
     in
     [idecl l vector_ctyp gs;
      iextern (CL_id (gs, vector_ctyp)) (mk_id "internal_vector_init", []) [V_lit (VL_int (Big_int.of_int len), CT_fint 64)]]
     @ List.concat (List.mapi aval_set (if direction then List.rev avals else avals)),
     V_id (gs, vector_ctyp),
     [iclear vector_ctyp gs]

  | AV_vector _ as aval ->
     raise (Reporting.err_general l ("Have AVL_vector: " ^ Pretty_print_sail.to_string (pp_aval aval) ^ " which is not a vector type"))

  | AV_list (avals, Typ_aux (typ, _)) ->
     let ctyp = match typ with
       | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> ctyp_of_typ ctx typ
       | _ -> raise (Reporting.err_general l "Invalid list type")
     in
     let gs = ngensym () in
     let mk_cons aval =
       let setup, cval, cleanup = compile_aval l ctx aval in
       setup @ [iextern (CL_id (gs, CT_list ctyp)) (mk_id "cons", [ctyp]) [cval; V_id (gs, CT_list ctyp)]] @ cleanup
     in
     [idecl l (CT_list ctyp) gs]
     @ List.concat (List.map mk_cons (List.rev avals)),
     V_id (gs, CT_list ctyp),
     [iclear (CT_list ctyp) gs]

let optimize_call l ctx clexp id args arg_ctyps ret_ctyp =
  let call () =
    let setup = ref [] in
    let cleanup = ref [] in
    let cast_args =
      List.map2
        (fun ctyp cval ->
          let have_ctyp = cval_ctyp cval in
          if is_polymorphic ctyp then
            V_poly (cval, have_ctyp)
          else if C.specialize_calls || ctyp_equal ctyp have_ctyp then
            cval
          else
            let gs = ngensym () in
            setup := iinit l ctyp gs cval :: !setup;
            cleanup := iclear ctyp gs :: !cleanup;
            V_id (gs, ctyp))
        arg_ctyps args
    in
    if C.specialize_calls || ctyp_equal (clexp_ctyp clexp) ret_ctyp then
      !setup @ [ifuncall l clexp id cast_args] @ !cleanup
    else
      let gs = ngensym () in
      List.rev !setup
      @ [idecl l ret_ctyp gs;
         ifuncall l (CL_id (gs, ret_ctyp)) id cast_args;
         icopy l clexp (V_id (gs, ret_ctyp));
         iclear ret_ctyp gs]
      @ !cleanup
  in
  if not C.specialize_calls && Env.is_extern (fst id) ctx.tc_env "c" then
    let extern = Env.get_extern (fst id) ctx.tc_env "c" in
    begin match extern, List.map cval_ctyp args, clexp_ctyp clexp with
    | "slice", [CT_fbits _; CT_lint; _], CT_fbits (n, _) ->
       let start = ngensym () in
       [iinit l (CT_fint 64) start (List.nth args 1);
        icopy l clexp (V_call (Slice n, [List.nth args 0; V_id (start, CT_fint 64)]))]
    | "sail_unsigned", [CT_fbits _], CT_fint 64 ->
       [icopy l clexp (V_call (Unsigned 64, [List.nth args 0]))]
    | "sail_signed", [CT_fbits _], CT_fint 64 ->
       [icopy l clexp (V_call (Signed 64, [List.nth args 0]))]
    | "set_slice", [_; _; CT_fbits (n, _); CT_fint 64; CT_fbits (m, _)], CT_fbits (n', _) when n = n' ->
       [icopy l clexp (V_call (Set_slice, [List.nth args 2; List.nth args 3; List.nth args 4]))]
    | _, _, _ ->
       call ()
    end
  else call ()

let compile_funcall l ctx id args =
  let setup = ref [] in
  let cleanup = ref [] in

  let quant, Typ_aux (fn_typ, _) =
    (* If we can't find a function in local_env, fall back to the
       global env - this happens when representing assertions, exit,
       etc as functions in the IR. *)
    try Env.get_val_spec id ctx.local_env with Type_error _ -> Env.get_val_spec id ctx.tc_env
  in
  let arg_typs, ret_typ = match fn_typ with
    | Typ_fn (arg_typs, ret_typ, _) -> arg_typs, ret_typ
    | _ -> assert false
  in
  let ctx' = { ctx with local_env = add_typquant (id_loc id) quant ctx.tc_env } in
  let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ in

  assert (List.length arg_ctyps = List.length args);

  let setup_arg ctyp aval =
    let arg_setup, cval, arg_cleanup = compile_aval l ctx aval in
    setup := List.rev arg_setup @ !setup;
    cleanup := arg_cleanup @ !cleanup;
    cval
  in

  let setup_args = List.map2 setup_arg arg_ctyps args in

  List.rev !setup,
  begin fun clexp ->
  iblock1 (optimize_call l ctx clexp (id, []) setup_args arg_ctyps ret_ctyp)
  end,
  !cleanup

let rec apat_ctyp ctx (AP_aux (apat, _, _)) =
  match apat with
  | AP_tup apats -> CT_tup (List.map (apat_ctyp ctx) apats)
  | AP_global (_, typ) -> ctyp_of_typ ctx typ
  | AP_cons (apat, _) -> CT_list (apat_ctyp ctx apat)
  | AP_wild typ | AP_nil typ | AP_id (_, typ) -> ctyp_of_typ ctx typ
  | AP_app (_, _, typ) -> ctyp_of_typ ctx typ
  | AP_as (_, _, typ) -> ctyp_of_typ ctx typ

let rec compile_match ctx (AP_aux (apat_aux, env, l)) cval case_label =
  let ctx = { ctx with local_env = env } in
  let ctyp = cval_ctyp cval in
  match apat_aux with
  | AP_id (pid, _) when Env.is_union_constructor pid ctx.tc_env ->
     [ijump l (V_ctor_kind (cval, pid, [], cval_ctyp cval)) case_label],
     [],
     ctx

  | AP_global (pid, typ) ->
     let global_ctyp = ctyp_of_typ ctx typ in
     [icopy l (CL_id (global pid, global_ctyp)) cval], [], ctx

  | AP_id (pid, _) when is_ct_enum ctyp ->
     begin match Env.lookup_id pid ctx.tc_env with
     | Unbound -> [idecl l ctyp (name pid); icopy l (CL_id (name pid, ctyp)) cval], [], ctx
     | _ -> [ijump l (V_call (Neq, [V_id (name pid, ctyp); cval])) case_label], [], ctx
     end

  | AP_id (pid, typ) ->
     let id_ctyp = ctyp_of_typ ctx typ in
     let ctx = { ctx with locals = Bindings.add pid (Immutable, id_ctyp) ctx.locals } in
     [idecl l id_ctyp (name pid); icopy l (CL_id (name pid, id_ctyp)) cval], [iclear id_ctyp (name pid)], ctx

  | AP_as (apat, id, typ) ->
     let id_ctyp = ctyp_of_typ ctx typ in
     let instrs, cleanup, ctx = compile_match ctx apat cval case_label in
     let ctx = { ctx with locals = Bindings.add id (Immutable, id_ctyp) ctx.locals } in
     instrs @ [idecl l id_ctyp (name id); icopy l (CL_id (name id, id_ctyp)) cval], iclear id_ctyp (name id) :: cleanup, ctx

  | AP_tup apats ->
     begin
       let get_tup n = V_tuple_member (cval, List.length apats, n) in
       let fold (instrs, cleanup, n, ctx) apat ctyp =
         let instrs', cleanup', ctx = compile_match ctx apat (get_tup n) case_label in
         instrs @ instrs', cleanup' @ cleanup, n + 1, ctx
       in
       match ctyp with
       | CT_tup ctyps ->
          let instrs, cleanup, _, ctx = List.fold_left2 fold ([], [], 0, ctx) apats ctyps in
          instrs, cleanup, ctx
       | _ -> failwith ("AP_tup with ctyp " ^ string_of_ctyp ctyp)
     end

  | AP_app (ctor, apat, variant_typ) ->
     begin match ctyp with
     | CT_variant (_, ctors) ->
        let ctor_ctyp = UBindings.find (ctor, []) (ctor_bindings ctors) in
        let pat_ctyp = apat_ctyp ctx apat in
        (* These should really be the same, something has gone wrong if they are not. *)
        if ctyp_equal ctor_ctyp (ctyp_of_typ ctx variant_typ) then
          raise (Reporting.err_general l (Printf.sprintf "%s is not the same type as %s" (string_of_ctyp ctor_ctyp) (string_of_ctyp (ctyp_of_typ ctx variant_typ))))
        else ();
        let unifiers, ctor_ctyp =
          if is_polymorphic ctor_ctyp then
            let unifiers = List.map ctyp_suprema (ctyp_unify ctor_ctyp pat_ctyp) in
            unifiers, ctyp_suprema pat_ctyp
          else
            [], ctor_ctyp
        in
        let instrs, cleanup, ctx = compile_match ctx apat (V_ctor_unwrap (ctor, cval, unifiers, ctor_ctyp)) case_label in
        [ijump l (V_ctor_kind (cval, ctor, unifiers, pat_ctyp)) case_label]
        @ instrs,
        cleanup,
        ctx
     | ctyp ->
        raise (Reporting.err_general l (Printf.sprintf "Variant constructor %s : %s matching against non-variant type %s : %s"
                                                       (string_of_id ctor)
                                                       (string_of_typ variant_typ)
                                                       (string_of_cval cval)
                                                       (string_of_ctyp ctyp)))
     end

  | AP_wild _ -> [], [], ctx

  | AP_cons (hd_apat, tl_apat) ->
     begin match ctyp with
     | CT_list ctyp ->
        let hd_setup, hd_cleanup, ctx = compile_match ctx hd_apat (V_call (List_hd, [cval])) case_label in
        let tl_setup, tl_cleanup, ctx = compile_match ctx tl_apat (V_call (List_tl, [cval])) case_label in
        [ijump l (V_call (Eq, [cval; V_lit (VL_empty_list, CT_list ctyp)])) case_label] @ hd_setup @ tl_setup, tl_cleanup @ hd_cleanup, ctx
     | _ ->
        raise (Reporting.err_general l "Tried to pattern match cons on non list type")
     end

  | AP_nil _ -> [ijump l (V_call (Neq, [cval; V_lit (VL_empty_list, ctyp)])) case_label], [], ctx

let unit_cval = V_lit (VL_unit, CT_unit)

let rec compile_alexp ctx alexp =
  match alexp with
  | AL_id (id, typ) ->
     let ctyp = match Bindings.find_opt id ctx.locals with
       | Some (_, ctyp) -> ctyp
       | None -> ctyp_of_typ ctx typ
     in
     CL_id (name_or_global ctx id, ctyp)
  | AL_addr (id, typ) ->
     let ctyp = match Bindings.find_opt id ctx.locals with
       | Some (_, ctyp) -> ctyp
       | None -> ctyp_of_typ ctx typ
     in
     CL_addr (CL_id (name_or_global ctx id, ctyp))
  | AL_field (alexp, field_id) ->
     CL_field (compile_alexp ctx alexp, (field_id, []))
     
let rec compile_aexp ctx (AE_aux (aexp_aux, env, l)) =
  let ctx = { ctx with local_env = env } in
  match aexp_aux with
  | AE_let (mut, id, binding_typ, binding, (AE_aux (_, body_env, _) as body), body_typ) ->
     let binding_ctyp = ctyp_of_typ { ctx with local_env = body_env } binding_typ in
     let setup, call, cleanup = compile_aexp ctx binding in
     let letb_setup, letb_cleanup =
       [idecl l binding_ctyp (name id);
        iblock1 (setup @ [call (CL_id (name id, binding_ctyp))] @ cleanup)],
       [iclear binding_ctyp (name id)]
     in
     let ctx = { ctx with locals = Bindings.add id (mut, binding_ctyp) ctx.locals } in
     let setup, call, cleanup = compile_aexp ctx body in
     letb_setup @ setup, call, cleanup @ letb_cleanup

  | AE_app (id, vs, _) ->
     compile_funcall l ctx id vs

  | AE_val aval ->
     let setup, cval, cleanup = compile_aval l ctx aval in
     setup, (fun clexp -> icopy l clexp cval), cleanup

  (* Compile case statements *)
  | AE_case (aval, cases, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let aval_setup, cval, aval_cleanup = compile_aval l ctx aval in
     (* Get the number of cases, because we don't want to check branch
        coverage for matches with only a single case. *)
     let num_cases = List.length cases in
     let branch_id, on_reached = coverage_branch_reached l in
     let case_return_id = ngensym () in
     let finish_match_label = label "finish_match_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _, _)
           | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _, _) -> true
         | _ -> false
       in
       let case_label = label "case_" in
       let destructure, destructure_cleanup, ctx = compile_match ctx apat cval case_label in
       let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, body_call, body_cleanup = compile_aexp ctx body in
       let gs = ngensym () in
       let case_instrs =
         destructure
         @ (if not trivial_guard then
              guard_setup @ [idecl l CT_bool gs; guard_call (CL_id (gs, CT_bool))] @ guard_cleanup
              @ [iif l (V_call (Bnot, [V_id (gs, CT_bool)])) (destructure_cleanup @ [igoto case_label]) [] CT_unit]
            else [])
         @ (if num_cases > 1 then coverage_branch_taken branch_id body else [])
         @ body_setup
         @ [body_call (CL_id (case_return_id, ctyp))] @ body_cleanup @ destructure_cleanup
         @ [igoto finish_match_label]
       in
       if is_dead_aexp body then
         [ilabel case_label]
       else
         [iblock case_instrs; ilabel case_label]
     in
     aval_setup
     @ (if num_cases > 1 then on_reached else [])
     @ [idecl l ctyp case_return_id]
     @ List.concat (List.map compile_case cases)
     @ [imatch_failure ()]
     @ [ilabel finish_match_label],
     (fun clexp -> icopy l clexp (V_id (case_return_id, ctyp))),
     [iclear ctyp case_return_id]
     @ aval_cleanup

  (* Compile try statement *)
  | AE_try (aexp, cases, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let aexp_setup, aexp_call, aexp_cleanup = compile_aexp ctx aexp in
     let try_return_id = ngensym () in
     let post_exception_handlers_label = label "post_exception_handlers_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _, _)
         | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _, _) -> true
         | _ -> false
       in
       let try_label = label "try_" in
       let exn_cval = V_id (current_exception, ctyp_of_typ ctx (mk_typ (Typ_id (mk_id "exception")))) in
       let destructure, destructure_cleanup, ctx = compile_match ctx apat exn_cval try_label in
       let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, body_call, body_cleanup = compile_aexp ctx body in
       let gs = ngensym () in
       let case_instrs =
         destructure @ [icomment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [idecl l CT_bool gs; guard_call (CL_id (gs, CT_bool))] @ guard_cleanup
              @ [ijump l (V_call (Bnot, [V_id (gs, CT_bool)])) try_label]
              @ [icomment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id (try_return_id, ctyp))] @ body_cleanup @ destructure_cleanup
         @ [igoto post_exception_handlers_label]
       in
       [iblock case_instrs; ilabel try_label]
     in
     assert (ctyp_equal ctyp (ctyp_of_typ ctx typ));
     [idecl l ctyp try_return_id;
      itry_block (aexp_setup @ [aexp_call (CL_id (try_return_id, ctyp))] @ aexp_cleanup);
      ijump l (V_call (Bnot, [V_id (have_exception, CT_bool)])) post_exception_handlers_label;
      icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool false, CT_bool))]
     @ List.concat (List.map compile_case cases)
     @ [(* fallthrough *)
        icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool));
        ilabel post_exception_handlers_label],
     (fun clexp -> icopy l clexp (V_id (try_return_id, ctyp))),
     []

  | AE_if (aval, then_aexp, else_aexp, if_typ) ->
     if is_dead_aexp then_aexp then
       compile_aexp ctx else_aexp
     else if is_dead_aexp else_aexp then
       compile_aexp ctx then_aexp
     else
       let if_ctyp = ctyp_of_typ ctx if_typ in
       let branch_id, on_reached = coverage_branch_reached l in
       let compile_branch aexp =
         let setup, call, cleanup = compile_aexp ctx aexp in
         fun clexp -> coverage_branch_taken branch_id aexp @ setup @ [call clexp] @ cleanup
       in
       let setup, cval, cleanup = compile_aval l ctx aval in
       setup,
       (fun clexp ->
         append_into_block on_reached
           (iif l cval
              (compile_branch then_aexp clexp)
              (compile_branch else_aexp clexp)
              if_ctyp)),
       cleanup

  (* FIXME: AE_record_update could be AV_record_update - would reduce some copying. *)
  | AE_record_update (aval, fields, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let ctors = match ctyp with
       | CT_struct (_, ctors) -> List.fold_left (fun m (k, v) -> UBindings.add k v m) UBindings.empty ctors
       | _ -> raise (Reporting.err_general l "Cannot perform record update for non-record type")
     in
     let gs = ngensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup
       @ [icopy l (CL_field (CL_id (gs, ctyp), (id, []))) cval]
       @ field_cleanup
     in
     let setup, cval, cleanup = compile_aval l ctx aval in
     [idecl l ctyp gs]
     @ setup
     @ [icopy l (CL_id (gs, ctyp)) cval]
     @ cleanup
     @ List.concat (List.map compile_fields (Bindings.bindings fields)),
     (fun clexp -> icopy l clexp (V_id (gs, ctyp))),
     [iclear ctyp gs]

  | AE_short_circuit (SC_and, aval, aexp) ->
     let branch_id, on_reached = coverage_branch_reached l in
     let left_setup, cval, left_cleanup = compile_aval l ctx aval in
     let right_setup, call, right_cleanup = compile_aexp ctx aexp in
     let right_coverage = coverage_branch_taken branch_id aexp in
     let gs = ngensym () in
     left_setup
     @ on_reached
     @ [ idecl l CT_bool gs;
         iif l cval
             (right_coverage @ right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup)
             [icopy l (CL_id (gs, CT_bool)) (V_lit (VL_bool false, CT_bool))]
             CT_bool ]
     @ left_cleanup,
     (fun clexp -> icopy l clexp (V_id (gs, CT_bool))),
     []
  | AE_short_circuit (SC_or, aval, aexp) ->
     let branch_id, on_reached = coverage_branch_reached l in
     let left_setup, cval, left_cleanup = compile_aval l ctx aval in
     let right_setup, call, right_cleanup = compile_aexp ctx aexp in
     let right_coverage = coverage_branch_taken branch_id aexp in
     let gs = ngensym () in
     left_setup
     @ on_reached
     @ [ idecl l CT_bool gs;
         iif l cval
             [icopy l (CL_id (gs, CT_bool)) (V_lit (VL_bool true, CT_bool))]
             (right_coverage @ right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup)
             CT_bool ]
     @ left_cleanup,
     (fun clexp -> icopy l clexp (V_id (gs, CT_bool))),
     []

  (* This is a faster assignment rule for updating fields of a
     struct. *)
  | AE_assign (AL_id (id, assign_typ), AE_aux (AE_record_update (AV_id (rid, _), fields, typ), _, _))
       when Id.compare id rid = 0 ->
     let compile_fields (field_id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup
       @ [icopy l (CL_field (CL_id (name_or_global ctx id, ctyp_of_typ ctx typ), (field_id, []))) cval]
       @ field_cleanup
     in
     List.concat (List.map compile_fields (Bindings.bindings fields)),
     (fun clexp -> icopy l clexp unit_cval),
     []

  | AE_assign (alexp, aexp) ->
     let setup, call, cleanup = compile_aexp ctx aexp in
     setup @ [call (compile_alexp ctx alexp)], (fun clexp -> icopy l clexp unit_cval), cleanup

  | AE_block (aexps, aexp, _) ->
     let block = compile_block ctx aexps in
     let setup, call, cleanup = compile_aexp ctx aexp in
     block @ setup, call, cleanup

  | AE_loop (While, cond, body) ->
     let loop_start_label = label "while_" in
     let loop_end_label = label "wend_" in
     let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
     let body_setup, body_call, body_cleanup = compile_aexp ctx body in
     let gs = ngensym () in
     let unit_gs = ngensym () in
     let loop_test = V_call (Bnot, [V_id (gs, CT_bool)]) in
     [idecl l CT_bool gs; idecl l CT_unit unit_gs]
     @ [ilabel loop_start_label]
     @ [iblock (cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump l loop_test loop_end_label]
                @ body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup
                @ [igoto loop_start_label])]
     @ [ilabel loop_end_label],
     (fun clexp -> icopy l clexp unit_cval),
     []

  | AE_loop (Until, cond, body) ->
     let loop_start_label = label "repeat_" in
     let loop_end_label = label "until_" in
     let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
     let body_setup, body_call, body_cleanup = compile_aexp ctx body in
     let gs = ngensym () in
     let unit_gs = ngensym () in
     let loop_test = V_id (gs, CT_bool) in
     [idecl l CT_bool gs; idecl l CT_unit unit_gs]
     @ [ilabel loop_start_label]
     @ [iblock (body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup
                @ cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump l loop_test loop_end_label]
                @ [igoto loop_start_label])]
     @ [ilabel loop_end_label],
     (fun clexp -> icopy l clexp unit_cval),
     []

  | AE_cast (aexp, typ) -> compile_aexp ctx aexp

  | AE_return (aval, typ) ->
     let fn_return_ctyp = match Env.get_ret_typ env with
       | Some typ -> ctyp_of_typ ctx typ
       | None -> raise (Reporting.err_general l "No function return type found when compiling return statement")
     in
     (* Cleanup info will be re-added by fix_early_(heap/stack)_return *)
     let return_setup, cval, _ = compile_aval l ctx aval in
     let creturn =
       if ctyp_equal fn_return_ctyp (cval_ctyp cval) then
         [ireturn cval]
       else
         let gs = ngensym () in
         [idecl l fn_return_ctyp gs;
          icopy l (CL_id (gs, fn_return_ctyp)) cval;
          ireturn (V_id (gs, fn_return_ctyp))]
     in
     return_setup @ creturn,
     (fun clexp -> icomment "unreachable after return"),
     []

  | AE_throw (aval, typ) ->
     (* Cleanup info will be handled by fix_exceptions *)
     let throw_setup, cval, _ = compile_aval l ctx aval in
     throw_setup @ [ithrow l cval],
     (fun clexp -> icomment "unreachable after throw"),
     []

  | AE_field (aval, id, typ) ->
     let aval_ctyp = ctyp_of_typ ctx typ in
     let setup, cval, cleanup = compile_aval l ctx aval in
     let ctyp = match cval_ctyp cval with
       | CT_struct (struct_id, fields) ->
          begin match Util.assoc_compare_opt UId.compare (id, []) fields with
          | Some ctyp -> ctyp
          | None ->
             raise (Reporting.err_unreachable l __POS__
                      ("Struct " ^ string_of_id struct_id ^ " does not have expected field " ^ string_of_id id ^ "?"))
          end
       | _ ->
          raise (Reporting.err_unreachable l __POS__ "Field access on non-struct type in ANF representation!")
     in
     let unifiers, ctyp =
       if is_polymorphic ctyp then
         let unifiers = List.map ctyp_suprema (ctyp_unify ctyp aval_ctyp) in
         unifiers, ctyp_suprema aval_ctyp
       else
         [], ctyp
     in
     setup,
     (fun clexp -> icopy l clexp (V_field (cval, (id, unifiers)))),
     cleanup

  | AE_for (loop_var, loop_from, loop_to, loop_step, Ord_aux (ord, _), body) ->
     (* We assume that all loop indices are safe to put in a CT_fint. *)
     let ctx = { ctx with locals = Bindings.add loop_var (Immutable, CT_fint 64) ctx.locals } in

     let is_inc = match ord with
       | Ord_inc -> true
       | Ord_dec -> false
       | Ord_var _ -> raise (Reporting.err_general l "Polymorphic loop direction in C backend")
     in

     (* Loop variables *)
     let from_setup, from_call, from_cleanup = compile_aexp ctx loop_from in
     let from_gs = ngensym () in
     let to_setup, to_call, to_cleanup = compile_aexp ctx loop_to in
     let to_gs = ngensym () in
     let step_setup, step_call, step_cleanup = compile_aexp ctx loop_step in
     let step_gs = ngensym () in
     let variable_init gs setup call cleanup =
       [idecl l (CT_fint 64) gs;
        iblock (setup @ [call (CL_id (gs, CT_fint 64))] @ cleanup)]
     in

     let loop_start_label = label "for_start_" in
     let loop_end_label = label "for_end_" in
     let body_setup, body_call, body_cleanup = compile_aexp ctx body in
     let body_gs = ngensym () in

     let loop_var = name loop_var in

     let loop_body prefix continue =
       prefix
       @ [iblock ([ijump l (V_call ((if is_inc then Igt else Ilt), [V_id (loop_var, CT_fint 64); V_id (to_gs, CT_fint 64)])) loop_end_label]
                  @ body_setup
                  @ [body_call (CL_id (body_gs, CT_unit))]
                  @ body_cleanup
                  @ [icopy l (CL_id (loop_var, (CT_fint 64)))
                       (V_call ((if is_inc then Iadd else Isub), [V_id (loop_var, CT_fint 64); V_id (step_gs, CT_fint 64)]))]
                  @ continue ())]
     in
     (* We can either generate an actual loop body for C, or unroll the body for SMT *)
     let actual = loop_body [ilabel loop_start_label] (fun () -> [igoto loop_start_label]) in
     let rec unroll max n = loop_body [] (fun () -> if n < max then unroll max (n + 1) else [imatch_failure ()]) in
     let body = match C.unroll_loops with Some times -> unroll times 0 | None -> actual in

     variable_init from_gs from_setup from_call from_cleanup
     @ variable_init to_gs to_setup to_call to_cleanup
     @ variable_init step_gs step_setup step_call step_cleanup
     @ [iblock ([idecl l (CT_fint 64) loop_var;
                 icopy l (CL_id (loop_var, (CT_fint 64))) (V_id (from_gs, CT_fint 64));
                 idecl l CT_unit body_gs]
                @ body
                @ [ilabel loop_end_label])],
     (fun clexp -> icopy l clexp unit_cval),
     []

and compile_block ctx = function
  | [] -> []
  | (AE_aux (_, _, l) as exp) :: exps ->
     let setup, call, cleanup = compile_aexp ctx exp in
     let rest = compile_block ctx exps in
     let gs = ngensym () in
     iblock (setup @ [idecl l CT_unit gs; call (CL_id (gs, CT_unit))] @ cleanup) :: rest

let fast_int = function
  | CT_lint when !optimize_aarch64_fast_struct -> CT_fint 64
  | ctyp -> ctyp

(** Compile a sail type definition into a IR one. Most of the
   actual work of translating the typedefs into C is done by the code
   generator, as it's easy to keep track of structs, tuples and unions
   in their sail form at this level, and leave the fiddly details of
   how they get mapped to C in the next stage. This function also adds
   details of the types it compiles to the context, ctx, which is why
   it returns a ctypdef * ctx pair. **)
let compile_type_def ctx (TD_aux (type_def, (l, _))) =
  match type_def with
  | TD_enum (id, ids, _) ->
     CTD_enum (id, ids),
     { ctx with enums = Bindings.add id (IdSet.of_list ids) ctx.enums }

  | TD_record (id, typq, ctors, _) ->
     let record_ctx = { ctx with local_env = add_typquant l typq ctx.local_env } in
     let ctors =
       List.fold_left (fun ctors (typ, id) -> UBindings.add (id, []) (fast_int (ctyp_of_typ record_ctx typ)) ctors) UBindings.empty ctors
     in
     CTD_struct (id, UBindings.bindings ctors),
     { ctx with records = Bindings.add id ctors ctx.records }

  | TD_variant (id, typq, tus, _) ->
     let compile_tu = function
       | Tu_aux (Tu_ty_id (typ, id), _) ->
          let ctx = { ctx with local_env = add_typquant (id_loc id) typq ctx.local_env } in
          ctyp_of_typ ctx typ, id
     in
     let ctus = List.fold_left (fun ctus (ctyp, id) -> UBindings.add (id, []) ctyp ctus) UBindings.empty (List.map compile_tu tus) in
     CTD_variant (id, UBindings.bindings ctus),
     { ctx with variants = Bindings.add id ctus ctx.variants }

  (* Will be re-written before here, see bitfield.ml *)
  | TD_bitfield _ ->
     Reporting.unreachable l __POS__ "Cannot compile TD_bitfield"

  (* All type abbreviations are filtered out in compile_def  *)
  | TD_abbrev _ ->
     Reporting.unreachable l __POS__ "Found TD_abbrev in compile_type_def"

let generate_cleanup instrs =
  let generate_cleanup' (I_aux (instr, _)) =
    match instr with
    | I_init (ctyp, id, cval) -> [(id, iclear ctyp id)]
    | I_decl (ctyp, id) -> [(id, iclear ctyp id)]
    | instr -> []
  in
  let is_clear ids = function
    | I_aux (I_clear (_, id), _) -> NameSet.add id ids
    | _ -> ids
  in
  let cleaned = List.fold_left is_clear NameSet.empty instrs in
  instrs
  |> List.map generate_cleanup'
  |> List.concat
  |> List.filter (fun (id, _) -> not (NameSet.mem id cleaned))
  |> List.map snd

let fix_exception_block ?return:(return=None) ctx instrs =
  let end_block_label = label "end_block_exception_" in
  let is_exception_stop (I_aux (instr, _)) =
    match instr with
    | I_throw _ | I_if _ | I_block _ | I_funcall _ -> true
    | _ -> false
  in
  (* In this function 'after' is instructions after the one we've
     matched on, 'before is instructions before the instruction we've
     matched with, but after the previous match, and 'historic' are
     all the befores from previous matches. *)
  let rec rewrite_exception historic instrs =
    match instr_split_at is_exception_stop instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_block instrs, _) :: after ->
       before
       @ [iblock (rewrite_exception (historic @ before) instrs)]
       @ rewrite_exception (historic @ before) after
    | before, I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (_, l)) :: after ->
       let historic = historic @ before in
       before
       @ [iif l cval (rewrite_exception historic then_instrs) (rewrite_exception historic else_instrs) ctyp]
       @ rewrite_exception historic after
    | before, I_aux (I_throw cval, (_, l)) :: after ->
       before
       @ [icopy l (CL_id (current_exception, cval_ctyp cval)) cval;
          icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool))]
       @ (if C.track_throw then
            let loc_string = Reporting.short_loc_to_string l in
            [icopy l (CL_id (throw_location, CT_string)) (V_lit (VL_string loc_string, CT_string))]
          else [])
       @ generate_cleanup (historic @ before)
       @ [igoto end_block_label]
       @ rewrite_exception (historic @ before) after
    | before, (I_aux (I_funcall (x, _, f, args), (_, l)) as funcall) :: after ->
       let effects = match Env.get_val_spec (fst f) ctx.tc_env with
         | _, Typ_aux (Typ_fn (_, _, effects), _) -> effects
         | exception (Type_error _) -> no_effect (* nullary union constructor, so no val spec *)
         | _ -> assert false (* valspec must have function type *)
       in
       if has_effect effects BE_escape then
         before
         @ [funcall;
            iif l (V_id (have_exception, CT_bool)) (generate_cleanup (historic @ before) @ [igoto end_block_label]) [] CT_unit]
         @ rewrite_exception (historic @ before) after
       else
         before @ funcall :: rewrite_exception (historic @ before) after
    | _, _ -> assert false (* unreachable *)
  in
  match return with
  | None ->
     rewrite_exception [] instrs @ [ilabel end_block_label]
  | Some ctyp ->
     rewrite_exception [] instrs @ [ilabel end_block_label; iundefined ctyp]

let rec map_try_block f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_reset _ | I_init _ | I_reinit _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, List.map (map_try_block f) instrs1, List.map (map_try_block f) instrs2, ctyp)
    | I_funcall _ | I_copy _ | I_clear _ | I_throw _ | I_return _ -> instr
    | I_block instrs -> I_block (List.map (map_try_block f) instrs)
    | I_try_block instrs -> I_try_block (f (List.map (map_try_block f) instrs))
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_jump _ | I_match_failure | I_undefined _ | I_end _ -> instr
  in
  I_aux (instr, aux)

let fix_exception ?return:(return=None) ctx instrs =
  let instrs = List.map (map_try_block (fix_exception_block ctx)) instrs in
  fix_exception_block ~return:return ctx instrs

let rec compile_arg_pat ctx label (P_aux (p_aux, (l, _)) as pat) ctyp =
  match p_aux with
  | P_id id -> (id, ([], []))
  | P_wild -> let gs = gensym () in (gs, ([], []))
  | P_tup [] | P_lit (L_aux (L_unit, _)) -> let gs = gensym () in (gs, ([], []))
  | P_var (pat, _) -> compile_arg_pat ctx label pat ctyp
  | P_typ (_, pat) -> compile_arg_pat ctx label pat ctyp
  | _ ->
     let apat = anf_pat pat in
     let gs = gensym () in
     let destructure, cleanup, _ = compile_match ctx apat (V_id (name gs, ctyp)) label in
     (gs, (destructure, cleanup))

let rec compile_arg_pats ctx label (P_aux (p_aux, (l, _)) as pat) ctyps =
  match p_aux with
  | P_typ (_, pat) -> compile_arg_pats ctx label pat ctyps
  | P_tup pats when List.length pats = List.length ctyps ->
     [], List.map2 (fun pat ctyp -> compile_arg_pat ctx label pat ctyp) pats ctyps, []
  | _ when List.length ctyps = 1 ->
     [], [compile_arg_pat ctx label pat (List.nth ctyps 0)], []

  | _ ->
     let arg_id, (destructure, cleanup) = compile_arg_pat ctx label pat (CT_tup ctyps) in
     let new_ids = List.map (fun ctyp -> gensym (), ctyp) ctyps in
     destructure
     @ [idecl l (CT_tup ctyps) (name arg_id)]
     @ List.mapi (fun i (id, ctyp) -> icopy l (CL_tuple (CL_id (name arg_id, CT_tup ctyps), i)) (V_id (name id, ctyp))) new_ids,
     List.map (fun (id, _) -> id, ([], [])) new_ids,
     [iclear (CT_tup ctyps) (name arg_id)]
     @ cleanup

let combine_destructure_cleanup xs = List.concat (List.map fst xs), List.concat (List.rev (List.map snd xs))

let fix_destructure fail_label = function
  | ([], cleanup) -> ([], cleanup)
  | destructure, cleanup ->
     let body_label = label "fundef_body_" in
     (destructure @ [igoto body_label; ilabel fail_label; imatch_failure (); ilabel body_label], cleanup)

(** Functions that have heap-allocated return types are implemented by
   passing a pointer a location where the return value should be
   stored. The ANF -> Sail IR pass for expressions simply outputs an
   I_return instruction for any return value, so this function walks
   over the IR ast for expressions and modifies the return statements
   into code that sets that pointer, as well as adds extra control
   flow to cleanup heap-allocated variables correctly when a function
   terminates early. See the generate_cleanup function for how this is
   done. *)
let fix_early_return ret instrs =
  let end_function_label = label "end_function_" in
  let is_return_recur (I_aux (instr, _)) =
    match instr with
    | I_return _ | I_undefined _ | I_if _ | I_block _ | I_try_block _ -> true
    | _ -> false
  in
  let rec rewrite_return historic instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_try_block instrs, _) :: after ->
       before
       @ [itry_block (rewrite_return (historic @ before) instrs)]
       @ rewrite_return (historic @ before) after
    | before, I_aux (I_block instrs, _) :: after ->
       before
       @ [iblock (rewrite_return (historic @ before) instrs)]
       @ rewrite_return (historic @ before) after
    | before, I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (_, l)) :: after ->
       let historic = historic @ before in
       before
       @ [iif l cval (rewrite_return historic then_instrs) (rewrite_return historic else_instrs) ctyp]
       @ rewrite_return historic after
    | before, I_aux (I_return cval, (_, l)) :: after ->
       let cleanup_label = label "cleanup_" in
       let end_cleanup_label = label "end_cleanup_" in
       before
       @ [icopy l ret cval;
          igoto cleanup_label]
       (* This is probably dead code until cleanup_label, but we cannot be sure there are no jumps into it. *)
       @ rewrite_return (historic @ before) after
       @ [igoto end_cleanup_label;
          ilabel cleanup_label]
       @ generate_cleanup (historic @ before)
       @ [igoto end_function_label;
          ilabel end_cleanup_label]
    | before, I_aux (I_undefined _, (_, l)) :: after ->
       let cleanup_label = label "cleanup_" in
       let end_cleanup_label = label "end_cleanup_" in
       before
       @ [igoto cleanup_label]
       @ rewrite_return (historic @ before) after
       @ [igoto end_cleanup_label;
          ilabel cleanup_label]
       @ generate_cleanup (historic @ before)
       @ [igoto end_function_label;
          ilabel end_cleanup_label]
    | _, _ -> assert false
  in
  rewrite_return [] instrs
  @ [ilabel end_function_label; iend ()]

let letdef_count = ref 0

let compile_funcl ctx id pat guard exp =
  (* Find the function's type. *)
  let quant, Typ_aux (fn_typ, _) =
    try Env.get_val_spec id ctx.local_env with Type_error _ -> Env.get_val_spec id ctx.tc_env
  in
  let arg_typs, ret_typ = match fn_typ with
    | Typ_fn (arg_typs, ret_typ, _) -> arg_typs, ret_typ
    | _ -> assert false
  in

  (* Handle the argument pattern. *)
  let fundef_label = label "fundef_fail_" in
  let orig_ctx = ctx in
  (* The context must be updated before we call ctyp_of_typ on the argument types. *)
  let ctx = { ctx with local_env = add_typquant (id_loc id) quant ctx.tc_env } in

  let arg_ctyps =  List.map (ctyp_of_typ ctx) arg_typs in
  let ret_ctyp = ctyp_of_typ ctx ret_typ in

  (* Compile the function arguments as patterns. *)
  let arg_setup, compiled_args, arg_cleanup = compile_arg_pats ctx fundef_label pat arg_ctyps in
  let ctx =
    (* We need the primop analyzer to be aware of the function argument types, so put them in ctx *)
    List.fold_left2 (fun ctx (id, _) ctyp -> { ctx with locals = Bindings.add id (Immutable, ctyp) ctx.locals }) ctx compiled_args arg_ctyps
  in

  let guard_bindings = ref IdSet.empty in
  let guard_instrs = match guard with
    | Some guard ->
       let (AE_aux (_, _, l) as guard) = anf guard in
       guard_bindings := aexp_bindings guard;
       let guard_aexp = C.optimize_anf ctx (no_shadow (pat_ids pat) guard) in
       let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard_aexp in
       let guard_label = label "guard_" in
       let gs = ngensym () in
       [iblock (
            [idecl l CT_bool gs]
            @ guard_setup
            @ [guard_call (CL_id (gs, CT_bool))]
            @ guard_cleanup
            @ [ijump (id_loc id) (V_id (gs, CT_bool)) guard_label;
               imatch_failure ();
               ilabel guard_label]
       )]
    | None -> []
  in

  (* Optimize and compile the expression to ANF. *)
  let aexp = C.optimize_anf ctx (no_shadow (IdSet.union (pat_ids pat) !guard_bindings) (anf exp)) in
  
  let setup, call, cleanup = compile_aexp ctx aexp in
  let destructure, destructure_cleanup =
    compiled_args |> List.map snd |> combine_destructure_cleanup |> fix_destructure fundef_label
  in

  let instrs = arg_setup @ destructure @ guard_instrs @ setup @ [call (CL_id (return, ret_ctyp))] @ cleanup @ destructure_cleanup @ arg_cleanup in
  let instrs = fix_early_return (CL_id (return, ret_ctyp)) instrs in
  let instrs = fix_exception ~return:(Some ret_ctyp) ctx instrs in
  let instrs = coverage_function_entry id (exp_loc exp) @ instrs in

  [CDEF_fundef (id, None, List.map fst compiled_args, instrs)], orig_ctx

(** Compile a Sail toplevel definition into an IR definition **)
let rec compile_def n total ctx def =
  match def with
  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, _), _)]), _))
       when !opt_memo_cache ->
     let digest =
       def |> Pretty_print_sail.doc_def |> Pretty_print_sail.to_string |> Digest.string
     in
     let cachefile = Filename.concat "_sbuild" ("ccache" ^ Digest.to_hex digest) in
     let cached =
       if Sys.file_exists cachefile then
         let in_chan = open_in cachefile in
         try
           let compiled = Marshal.from_channel in_chan in
           close_in in_chan;
           Some (compiled, ctx)
         with
         | _ -> close_in in_chan; None
       else
         None
     in
     begin match cached with
     | Some (compiled, ctx) ->
        Util.progress "Compiling " (string_of_id id) n total;
        compiled, ctx
     | None ->
        let compiled, ctx = compile_def' n total ctx def in
        let out_chan = open_out cachefile in
        Marshal.to_channel out_chan compiled [Marshal.Closures];
        close_out out_chan;
        compiled, ctx
     end

  | _ -> compile_def' n total ctx def

and compile_def' n total ctx = function
  | DEF_reg_dec (DEC_aux (DEC_reg (_, _, typ, id), _)) ->
     [CDEF_reg_dec (id, ctyp_of_typ ctx typ, [])], ctx
  | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), _)) ->
     let aexp = C.optimize_anf ctx (no_shadow IdSet.empty (anf exp)) in
     let setup, call, cleanup = compile_aexp ctx aexp in
     let instrs = setup @ [call (CL_id (global id, ctyp_of_typ ctx typ))] @ cleanup in
     [CDEF_reg_dec (id, ctyp_of_typ ctx typ, instrs)], ctx

  | DEF_reg_dec (DEC_aux (_, (l, _))) ->
     raise (Reporting.err_general l "Cannot compile alias register declaration")

  | DEF_spec (VS_aux (VS_val_spec (_, id, _, _), _)) ->
     let quant, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let extern =
       if Env.is_extern id ctx.tc_env "c" then
         Some (Env.get_extern id ctx.tc_env "c")
       else
         None
     in
     let arg_typs, ret_typ = match fn_typ with
       | Typ_fn (arg_typs, ret_typ, _) -> arg_typs, ret_typ
       | _ -> assert false
     in
     let ctx' = { ctx with local_env = add_typquant (id_loc id) quant ctx.local_env } in
     let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ in
     [CDEF_spec (id, extern, arg_ctyps, ret_ctyp)],
     { ctx with valspecs = Bindings.add id (arg_ctyps, ret_ctyp) ctx.valspecs }

  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (pat, exp), _)), _)]), _)) ->
     Util.progress "Compiling " (string_of_id id) n total;
     compile_funcl ctx id pat None exp

  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, Pat_aux (Pat_when (pat, guard, exp), _)), _)]), _)) ->
     Util.progress "Compiling " (string_of_id id) n total;
     compile_funcl ctx id pat (Some guard) exp

  | DEF_fundef (FD_aux (FD_function (_, _, _, []), (l, _))) ->
     raise (Reporting.err_general l "Encountered function with no clauses")

  | DEF_fundef (FD_aux (FD_function (_, _, _, _ :: _ :: _), (l, _))) ->
     raise (Reporting.err_general l "Encountered function with multiple clauses")

  (* All abbreviations should expanded by the typechecker, so we don't
     need to translate type abbreviations into C typedefs. *)
  | DEF_type (TD_aux (TD_abbrev _, _)) -> [], ctx

  | DEF_type type_def ->
     let tdef, ctx = compile_type_def ctx type_def in
     [CDEF_type tdef], ctx

  | DEF_val (LB_aux (LB_val (pat, exp), _)) ->
     let ctyp = ctyp_of_typ ctx (typ_of_pat pat) in
     let aexp = C.optimize_anf ctx (no_shadow IdSet.empty (anf exp)) in
     let setup, call, cleanup = compile_aexp ctx aexp in
     let apat = anf_pat ~global:true pat in
     let gs = ngensym () in
     let end_label = label "let_end_" in
     let destructure, destructure_cleanup, _ = compile_match ctx apat (V_id (gs, ctyp)) end_label in
     let gs_setup, gs_cleanup =
       [idecl (exp_loc exp) ctyp gs], [iclear ctyp gs]
     in
     let bindings = List.map (fun (id, typ) -> id, ctyp_of_typ ctx typ) (apat_globals apat) in
     let n = !letdef_count in
     incr letdef_count;
     let instrs =
       gs_setup @ setup
       @ [call (CL_id (gs, ctyp))]
       @ cleanup
       @ destructure
       @ destructure_cleanup @ gs_cleanup
       @ [ilabel end_label]
     in
     [CDEF_let (n, bindings, instrs)],
     { ctx with letbinds = n :: ctx.letbinds }

  (* Only DEF_default that matters is default Order, but all order
     polymorphism is specialised by this point. *)
  | DEF_default _ -> [], ctx

  (* Overloading resolved by type checker *)
  | DEF_overload _ -> [], ctx

  (* Only the parser and sail pretty printer care about this. *)
  | DEF_fixity _ -> [], ctx

  (* We just ignore any pragmas we don't want to deal with. *)
  | DEF_pragma _ -> [], ctx

  (* Termination measures only needed for Coq, and other theorem prover output *)
  | DEF_measure _ -> [], ctx
  | DEF_loop_measures _ -> [], ctx

  | DEF_internal_mutrec fundefs ->
     let defs = List.map (fun fdef -> DEF_fundef fdef) fundefs in
     List.fold_left (fun (cdefs, ctx) def -> let cdefs', ctx = compile_def n total ctx def in (cdefs @ cdefs', ctx)) ([], ctx) defs

  (* Scattereds and mapdefs should be removed by this point *)
  | (DEF_scattered _ | DEF_mapdef _) as def ->
     raise (Reporting.err_general Parse_ast.Unknown ("Could not compile:\n" ^ Pretty_print_sail.to_string (Pretty_print_sail.doc_def def)))

let rec specialize_variants ctx prior =
  let unifications = ref (UBindings.empty) in

  let fix_variant_ctyp var_id new_ctors = function
    | CT_variant (id, ctors) when Id.compare id var_id = 0 -> CT_variant (id, new_ctors)
    | ctyp -> ctyp
  in
  let fix_struct_ctyp struct_id new_fields = function
    | CT_struct (id, ctors) when Id.compare id struct_id = 0 -> CT_struct (id, new_fields)
    | ctyp -> ctyp
  in

  (* specialize_constructor is called on all instructions when we find
     a constructor in a union type that is polymorphic. It's job is to
     record all uses of that constructor so we can monomorphise it. *)
  let specialize_constructor ctx (ctor_id, existing_unifiers) ctyp =
    assert (existing_unifiers = []);
    function
    | I_aux (I_funcall (clexp, extern, id, [cval]), ((_, l) as aux)) as instr when UId.compare id (ctor_id, []) = 0 ->
       (* Work out how each call to a constructor in instantiated and add that to unifications *)
       let unifiers = List.map ctyp_suprema (ctyp_unify ctyp (cval_ctyp cval)) in
       let mono_id = (ctor_id, unifiers) in
       unifications := UBindings.add mono_id (ctyp_suprema (cval_ctyp cval)) !unifications;

       (* We need to cast each cval to it's ctyp_suprema in order to put it in the most general constructor *)
       let setup, cval, cleanup =
         let suprema = ctyp_suprema (cval_ctyp cval) in
         if ctyp_equal ctyp suprema then
           [], unpoly cval, []
         else
           let gs = ngensym () in
           [idecl l suprema gs;
            icopy l (CL_id (gs, suprema)) (unpoly cval)],
           V_id (gs, suprema),
           [iclear suprema gs]
       in

       let mk_funcall instr =
         if List.length setup = 0 then
           instr
         else
           iblock (setup @ [instr] @ cleanup)
       in

       mk_funcall (I_aux (I_funcall (clexp, extern, mono_id, [cval]), aux))

    | I_aux (I_funcall (clexp, extern, id, cvals), ((_, l) as aux)) as instr when UId.compare id (ctor_id, []) = 0 ->
       Reporting.unreachable l __POS__ "Multiple argument constructor found"

    (* We have to be careful this is the only place where an V_ctor_kind can appear before calling specialize variants *)
    | I_aux (I_jump (V_ctor_kind (_, id, unifiers, pat_ctyp), _), _) as instr when Id.compare id ctor_id = 0 ->
       unifications := UBindings.add (ctor_id, unifiers) (ctyp_suprema pat_ctyp) !unifications;
       instr

    | instr -> instr
  in

  (* specialize_field performs the same job as specialize_constructor,
     but for struct fields rather than union constructors. *)
  let specialize_field ctx (field_id, existing_unifiers) ctyp =
    assert (existing_unifiers = []);
    function
    | I_aux (I_copy (CL_field (clexp, field), cval), aux) when UId.compare (field_id, []) field = 0 ->
       let unifiers = List.map ctyp_suprema (ctyp_unify ctyp (cval_ctyp cval)) in
       let mono_id = (field_id, unifiers) in
       unifications := UBindings.add mono_id (ctyp_suprema (cval_ctyp cval)) !unifications;
       I_aux (I_copy (CL_field (clexp, mono_id), cval), aux)
    | instr -> instr
  in

  function
  | (CDEF_type (CTD_variant (var_id, ctors)) as cdef) :: cdefs ->
     let polymorphic_ctors = List.filter (fun (_, ctyp) -> is_polymorphic ctyp) ctors in

     let cdefs =
       List.fold_left
         (fun cdefs (ctor_id, ctyp) -> List.map (cdef_map_instr (specialize_constructor ctx ctor_id ctyp)) cdefs)
         cdefs
         polymorphic_ctors
     in

     let monomorphic_ctors = List.filter (fun (_, ctyp) -> not (is_polymorphic ctyp)) ctors in
     let specialized_ctors = UBindings.bindings !unifications in
     let new_ctors = monomorphic_ctors @ specialized_ctors in

     let ctx = {
         ctx with variants = Bindings.add var_id
                               (List.fold_left (fun m (uid, ctyp) -> UBindings.add uid ctyp m) !unifications monomorphic_ctors)
                               ctx.variants
       } in

     let cdefs = List.map (cdef_map_ctyp (map_ctyp (fix_variant_ctyp var_id new_ctors))) cdefs in
     let prior = List.map (cdef_map_ctyp (map_ctyp (fix_variant_ctyp var_id new_ctors))) prior in
     specialize_variants ctx (CDEF_type (CTD_variant (var_id, new_ctors)) :: prior) cdefs

  | (CDEF_type (CTD_struct (struct_id, fields)) as cdef) :: cdefs ->
     let polymorphic_fields = List.filter (fun (_, ctyp) -> is_polymorphic ctyp) fields in

     let cdefs =
       List.fold_left
         (fun cdefs (field_id, ctyp) -> List.map (cdef_map_instr (specialize_field ctx field_id ctyp)) cdefs)
         cdefs
         polymorphic_fields
     in

     let monomorphic_fields = List.filter (fun (_, ctyp) -> not (is_polymorphic ctyp)) fields in
     let specialized_fields = UBindings.bindings !unifications in
     let new_fields = monomorphic_fields @ specialized_fields in

     let ctx = {
         ctx with records = Bindings.add struct_id
                              (List.fold_left (fun m (uid, ctyp) -> UBindings.add uid ctyp m) !unifications monomorphic_fields)
                              ctx.records
       } in

     let cdefs = List.map (cdef_map_ctyp (map_ctyp (fix_struct_ctyp struct_id new_fields))) cdefs in
     let prior = List.map (cdef_map_ctyp (map_ctyp (fix_struct_ctyp struct_id new_fields))) prior in     
     specialize_variants ctx (CDEF_type (CTD_struct (struct_id, new_fields)) :: prior) cdefs

 | cdef :: cdefs ->
     let remove_poly (I_aux (instr, aux)) =
       match instr with
       | I_copy (clexp, cval) when is_polymorphic (cval_ctyp cval) ->
          I_aux (I_copy (clexp, unpoly cval), aux)
       | instr -> I_aux (instr, aux)
     in
     let cdef = cdef_map_instr remove_poly cdef in
     specialize_variants ctx (cdef :: prior) cdefs

  | [] -> List.rev prior, ctx

(** Once we specialize variants, there may be additional type
   dependencies which could be in the wrong order. As such we need to
   sort the type definitions in the list of cdefs. *)
let sort_ctype_defs cdefs =
  (* Split the cdefs into type definitions and non type definitions *)
  let is_ctype_def = function CDEF_type _ -> true | _ -> false in
  let unwrap = function CDEF_type ctdef -> ctdef | _ -> assert false in
  let ctype_defs = List.map unwrap (List.filter is_ctype_def cdefs) in
  let cdefs = List.filter (fun cdef -> not (is_ctype_def cdef)) cdefs in

  let ctdef_id = function
    | CTD_enum (id, _) | CTD_struct (id, _) | CTD_variant (id, _) -> id
  in

  let ctdef_ids = function
    | CTD_enum _ -> IdSet.empty
    | CTD_struct (_, ctors) | CTD_variant (_, ctors) ->
       List.fold_left (fun ids (_, ctyp) -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctors
  in

  (* Create a reverse (i.e. from types to the types that are dependent
     upon them) id graph of dependencies between types *)
  let module IdGraph = Graph.Make(Id) in

  let graph =
    List.fold_left (fun g ctdef ->
        List.fold_left (fun g id -> IdGraph.add_edge id (ctdef_id ctdef) g)
          (IdGraph.add_edges (ctdef_id ctdef) [] g) (* Make sure even types with no dependencies are in graph *)
          (IdSet.elements (ctdef_ids ctdef)))
      IdGraph.empty
      ctype_defs
  in

  (* Then select the ctypes in the correct order as given by the topsort *)
  let ids = IdGraph.topsort graph in
  let ctype_defs =
    List.map (fun id -> CDEF_type (List.find (fun ctdef -> Id.compare (ctdef_id ctdef) id = 0) ctype_defs)) ids
  in

  ctype_defs @ cdefs

let compile_ast ctx ast =
  if !opt_memo_cache then
    (try
       if Sys.is_directory "_sbuild" then
         ()
       else
         raise (Reporting.err_general Parse_ast.Unknown "_sbuild exists, but is a file not a directory!")
     with
     | Sys_error _ -> Unix.mkdir "_sbuild" 0o775)
  else ();

  let total = List.length ast.defs in
  let _, chunks, ctx =
    List.fold_left (fun (n, chunks, ctx) def -> let defs, ctx = compile_def n total ctx def in n + 1, defs :: chunks, ctx) (1, [], ctx) ast.defs
  in
  let cdefs = List.concat (List.rev chunks) in
  let cdefs, ctx = specialize_variants ctx [] cdefs in
  let cdefs = sort_ctype_defs cdefs in
  cdefs, ctx

end

let add_special_functions env =
  let assert_vs = Initial_check.extern_of_string (mk_id "sail_assert") "(bool, string) -> unit" in
  let exit_vs = Initial_check.extern_of_string (mk_id "sail_exit") "unit -> unit" in
  let cons_vs = Initial_check.extern_of_string (mk_id "sail_cons") "forall ('a : Type). ('a, list('a)) -> list('a)" in

  snd (Type_error.check_defs env [assert_vs; exit_vs; cons_vs])
