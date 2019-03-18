(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util
open Jib
open Jib_util
open Type_check
open Value2

open Anf

let opt_debug_function = ref ""
let opt_debug_flow_graphs = ref false
let opt_memo_cache = ref false

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

let ctor_bindings = List.fold_left (fun map (id, ctyp) -> Bindings.add id ctyp map) Bindings.empty

(** The context type contains two type-checking
   environments. ctx.local_env contains the closest typechecking
   environment, usually from the expression we are compiling, whereas
   ctx.tc_env is the global type checking environment from
   type-checking the entire AST. We also keep track of local variables
   in ctx.locals, so we know when their type changes due to flow
   typing. *)
type ctx =
  { records : (ctyp Bindings.t) Bindings.t;
    enums : IdSet.t Bindings.t;
    variants : (ctyp Bindings.t) Bindings.t;
    tc_env : Env.t;
    local_env : Env.t;
    locals : (mut * ctyp) Bindings.t;
    letbinds : int list;
    no_raw : bool;
    convert_typ : ctx -> typ -> ctyp;
    optimize_anf : ctx -> typ aexp -> typ aexp
  }

let initial_ctx ~convert_typ:convert_typ ~optimize_anf:optimize_anf env =
  { records = Bindings.empty;
    enums = Bindings.empty;
    variants = Bindings.empty;
    tc_env = env;
    local_env = env;
    locals = Bindings.empty;
    letbinds = [];
    no_raw = false;
    convert_typ = convert_typ;
    optimize_anf = optimize_anf
  }

let ctyp_of_typ ctx typ = ctx.convert_typ ctx typ

let rec chunkify n xs =
  match Util.take n xs, Util.drop n xs with
  | xs, [] -> [xs]
  | xs, ys -> xs :: chunkify n ys

let rec compile_aval l ctx = function
  | AV_C_fragment (frag, typ, ctyp) ->
     let ctyp' = ctyp_of_typ ctx typ in
     if not (ctyp_equal ctyp ctyp') then
       raise (Reporting.err_unreachable l __POS__ (string_of_ctyp ctyp ^ " != " ^ string_of_ctyp ctyp'));
     [], (frag, ctyp_of_typ ctx typ), []

  | AV_id (id, typ) ->
     begin
       try
         let _, ctyp = Bindings.find id ctx.locals in
         [], (F_id (name id), ctyp), []
       with
       | Not_found ->
          [], (F_id (name id), ctyp_of_typ ctx (lvar_typ typ)), []
     end

  | AV_ref (id, typ) ->
     [], (F_ref (name id), CT_ref (ctyp_of_typ ctx (lvar_typ typ))), []

  | AV_lit (L_aux (L_string str, _), typ) ->
     [], (F_lit (V_string (String.escaped str)), ctyp_of_typ ctx typ), []

  | AV_lit (L_aux (L_num n, _), typ) when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
     let gs = ngensym () in
     [iinit CT_lint gs (F_lit (V_int n), CT_fint 64)],
     (F_id gs, CT_lint),
     [iclear CT_lint gs]

  | AV_lit (L_aux (L_num n, _), typ) ->
     let gs = ngensym () in
     [iinit CT_lint gs (F_lit (V_string (Big_int.to_string n)), CT_string)],
     (F_id gs, CT_lint),
     [iclear CT_lint gs]

  | AV_lit (L_aux (L_zero, _), _) -> [], (F_lit (V_bit Sail2_values.B0), CT_bit), []
  | AV_lit (L_aux (L_one, _), _) -> [], (F_lit (V_bit Sail2_values.B1), CT_bit), []

  | AV_lit (L_aux (L_true, _), _) -> [], (F_lit (V_bool true), CT_bool), []
  | AV_lit (L_aux (L_false, _), _) -> [], (F_lit (V_bool false), CT_bool), []

  | AV_lit (L_aux (L_real str, _), _) ->
     let gs = ngensym () in
     [iinit CT_real gs (F_lit (V_string str), CT_string)],
     (F_id gs, CT_real),
     [iclear CT_real gs]

  | AV_lit (L_aux (L_unit, _), _) -> [], (F_lit V_unit, CT_unit), []

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
     @ [idecl tup_ctyp gs]
     @ List.mapi (fun n cval -> icopy l (CL_tuple (CL_id (gs, tup_ctyp), n)) cval) cvals,
     (F_id gs, CT_tup (List.map cval_ctyp cvals)),
     [iclear tup_ctyp gs]
     @ cleanup

  | AV_record (fields, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let gs = ngensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup
       @ [icopy l (CL_field (CL_id (gs, ctyp), string_of_id id)) cval]
       @ field_cleanup
     in
     [idecl ctyp gs]
     @ List.concat (List.map compile_fields (Bindings.bindings fields)),
     (F_id gs, ctyp),
     [iclear ctyp gs]

  | AV_vector ([], _) ->
     raise (Reporting.err_general l "Encountered empty vector literal")

  (* Convert a small bitvector to a uint64_t literal. *)
  | AV_vector (avals, typ) when is_bitvector avals && List.length avals <= 64 ->
     begin
       let bitstring = F_lit (V_bits (List.map value_of_aval_bit avals)) in
       let len = List.length avals in
       match destruct_vector ctx.tc_env typ with
       | Some (_, Ord_aux (Ord_inc, _), _) ->
          [], (bitstring, CT_fbits (len, false)), []
       | Some (_, Ord_aux (Ord_dec, _), _) ->
          [], (bitstring, CT_fbits (len, true)), []
       | Some _ ->
          raise (Reporting.err_general l "Encountered order polymorphic bitvector literal")
       | None ->
          raise (Reporting.err_general l "Encountered vector literal without vector type")
     end

  (* Convert a bitvector literal that is larger than 64-bits to a
     variable size bitvector, converting it in 64-bit chunks. *)
  | AV_vector (avals, typ) when is_bitvector avals ->
     let len = List.length avals in
     let bitstring avals = F_lit (V_bits (List.map value_of_aval_bit avals)) in
     let first_chunk = bitstring (Util.take (len mod 64) avals) in
     let chunks = Util.drop (len mod 64) avals |> chunkify 64 |> List.map bitstring in
     let gs = ngensym () in
     [iinit (CT_lbits true) gs (first_chunk, CT_fbits (len mod 64, true))]
     @ List.map (fun chunk -> ifuncall (CL_id (gs, CT_lbits true))
                                       (mk_id "append_64")
                                       [(F_id gs, CT_lbits true); (chunk, CT_fbits (64, true))]) chunks,
     (F_id gs, CT_lbits true),
     [iclear (CT_lbits true) gs]

  (* If we have a bitvector value, that isn't a literal then we need to set bits individually. *)
  | AV_vector (avals, Typ_aux (Typ_app (id, [_; A_aux (A_order ord, _); A_aux (A_typ (Typ_aux (Typ_id bit_id, _)), _)]), _))
       when string_of_id bit_id = "bit" && string_of_id id = "vector" && List.length avals <= 64 ->
     let len = List.length avals in
     let direction = match ord with
       | Ord_aux (Ord_inc, _) -> false
       | Ord_aux (Ord_dec, _) -> true
       | Ord_aux (Ord_var _, _) -> raise (Reporting.err_general l "Polymorphic vector direction found")
     in
     let gs = ngensym () in
     let ctyp = CT_fbits (len, direction) in
     let mask i = V_bits (Util.list_init (63 - i) (fun _ -> Sail2_values.B0) @ [Sail2_values.B1] @ Util.list_init i (fun _ -> Sail2_values.B0)) in
     let aval_mask i aval =
       let setup, cval, cleanup = compile_aval l ctx aval in
       match cval with
       | (F_lit (V_bit Sail2_values.B0), _) -> []
       | (F_lit (V_bit Sail2_values.B1), _) ->
          [icopy l (CL_id (gs, ctyp)) (F_op (F_id gs, "|", F_lit (mask i)), ctyp)]
       | _ ->
          setup @ [iif cval [icopy l (CL_id (gs, ctyp)) (F_op (F_id gs, "|", F_lit (mask i)), ctyp)] [] CT_unit] @ cleanup
     in
     [idecl ctyp gs;
      icopy l (CL_id (gs, ctyp)) (F_lit (V_bits (Util.list_init 64 (fun _ -> Sail2_values.B0))), ctyp)]
     @ List.concat (List.mapi aval_mask (List.rev avals)),
     (F_id gs, ctyp),
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
                  (mk_id "internal_vector_update")
                  [(F_id gs, vector_ctyp); (F_lit (V_int (Big_int.of_int i)), CT_fint 64); cval]]
       @ cleanup
     in
     [idecl vector_ctyp gs;
      iextern (CL_id (gs, vector_ctyp)) (mk_id "internal_vector_init") [(F_lit (V_int (Big_int.of_int len)), CT_fint 64)]]
     @ List.concat (List.mapi aval_set (if direction then List.rev avals else avals)),
     (F_id gs, vector_ctyp),
     [iclear vector_ctyp gs]

  | AV_vector _ as aval ->
     raise (Reporting.err_general l ("Have AV_vector: " ^ Pretty_print_sail.to_string (pp_aval aval) ^ " which is not a vector type"))

  | AV_list (avals, Typ_aux (typ, _)) ->
     let ctyp = match typ with
       | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> ctyp_of_typ ctx typ
       | _ -> raise (Reporting.err_general l "Invalid list type")
     in
     let gs = ngensym () in
     let mk_cons aval =
       let setup, cval, cleanup = compile_aval l ctx aval in
       setup @ [ifuncall (CL_id (gs, CT_list ctyp)) (mk_id ("cons#" ^ string_of_ctyp ctyp)) [cval; (F_id gs, CT_list ctyp)]] @ cleanup
     in
     [idecl (CT_list ctyp) gs]
     @ List.concat (List.map mk_cons (List.rev avals)),
     (F_id gs, CT_list ctyp),
     [iclear (CT_list ctyp) gs]

let compile_funcall l ctx id args typ =
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
  let final_ctyp = ctyp_of_typ ctx typ in

  let setup_arg ctyp aval =
    let arg_setup, cval, arg_cleanup = compile_aval l ctx aval in
    setup := List.rev arg_setup @ !setup;
    cleanup := arg_cleanup @ !cleanup;
    let have_ctyp = cval_ctyp cval in
    if is_polymorphic ctyp then
      (F_poly (fst cval), have_ctyp)
    else if ctyp_equal ctyp have_ctyp then
      cval
    else
      let gs = ngensym () in
      setup := iinit ctyp gs cval :: !setup;
      cleanup := iclear ctyp gs :: !cleanup;
      (F_id gs, ctyp)
  in

  assert (List.length arg_ctyps = List.length args);

  let setup_args = List.map2 setup_arg arg_ctyps args in

  List.rev !setup,
  begin fun clexp ->
  if ctyp_equal (clexp_ctyp clexp) ret_ctyp then
    ifuncall clexp id setup_args
  else
    let gs = ngensym () in
    iblock [idecl ret_ctyp gs;
            ifuncall (CL_id (gs, ret_ctyp)) id setup_args;
            icopy l clexp (F_id gs, ret_ctyp);
            iclear ret_ctyp gs]
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
  match apat_aux, cval with
  | AP_id (pid, _), (frag, ctyp) when Env.is_union_constructor pid ctx.tc_env ->
     [ijump (F_op (F_field (frag, "kind"), "!=", F_lit (V_ctor_kind (string_of_id pid))), CT_bool) case_label],
     [],
     ctx

  | AP_global (pid, typ), (frag, ctyp) ->
     let global_ctyp = ctyp_of_typ ctx typ in
     [icopy l (CL_id (name pid, global_ctyp)) cval], [], ctx

  | AP_id (pid, _), (frag, ctyp) when is_ct_enum ctyp ->
     begin match Env.lookup_id pid ctx.tc_env with
     | Unbound -> [idecl ctyp (name pid); icopy l (CL_id (name pid, ctyp)) (frag, ctyp)], [], ctx
     | _ -> [ijump (F_op (F_id (name pid), "!=", frag), CT_bool) case_label], [], ctx
     end

  | AP_id (pid, typ), _ ->
     let ctyp = cval_ctyp cval in
     let id_ctyp = ctyp_of_typ ctx typ in
     let ctx = { ctx with locals = Bindings.add pid (Immutable, id_ctyp) ctx.locals } in
     [idecl id_ctyp (name pid); icopy l (CL_id (name pid, id_ctyp)) cval], [iclear id_ctyp (name pid)], ctx

  | AP_as (apat, id, typ), _ ->
     let id_ctyp = ctyp_of_typ ctx typ in
     let instrs, cleanup, ctx = compile_match ctx apat cval case_label in
     let ctx = { ctx with locals = Bindings.add id (Immutable, id_ctyp) ctx.locals } in
     instrs @ [idecl id_ctyp (name id); icopy l (CL_id (name id, id_ctyp)) cval], iclear id_ctyp (name id) :: cleanup, ctx

  | AP_tup apats, (frag, ctyp) ->
     begin
       let get_tup n ctyp = (F_field (frag, "ztup" ^ string_of_int n), ctyp) in
       let fold (instrs, cleanup, n, ctx) apat ctyp =
         let instrs', cleanup', ctx = compile_match ctx apat (get_tup n ctyp) case_label in
         instrs @ instrs', cleanup' @ cleanup, n + 1, ctx
       in
       match ctyp with
       | CT_tup ctyps ->
          let instrs, cleanup, _, ctx = List.fold_left2 fold ([], [], 0, ctx) apats ctyps in
          instrs, cleanup, ctx
       | _ -> failwith ("AP_tup with ctyp " ^ string_of_ctyp ctyp)
     end

  | AP_app (ctor, apat, variant_typ), (frag, ctyp) ->
     begin match ctyp with
     | CT_variant (_, ctors) ->
        let ctor_c_id = string_of_id ctor in
        let ctor_ctyp = Bindings.find ctor (ctor_bindings ctors) in
        (* These should really be the same, something has gone wrong if they are not. *)
        if ctyp_equal ctor_ctyp (ctyp_of_typ ctx variant_typ) then
          raise (Reporting.err_general l (Printf.sprintf "%s is not the same type as %s" (string_of_ctyp ctor_ctyp) (string_of_ctyp (ctyp_of_typ ctx variant_typ))))
        else ();
        let ctor_c_id, ctor_ctyp =
          if is_polymorphic ctor_ctyp then
            let unification = List.map ctyp_suprema (ctyp_unify ctor_ctyp (apat_ctyp ctx apat)) in
            (if List.length unification > 0 then
               ctor_c_id ^ "_" ^ Util.string_of_list "_" (fun ctyp -> Util.zencode_string (string_of_ctyp ctyp)) unification
             else
               ctor_c_id),
            ctyp_suprema (apat_ctyp ctx apat)
          else
            ctor_c_id, ctor_ctyp
        in
        let instrs, cleanup, ctx = compile_match ctx apat ((F_field (frag, Util.zencode_string ctor_c_id), ctor_ctyp)) case_label in
        [ijump (F_op (F_field (frag, "kind"), "!=", F_lit (V_ctor_kind ctor_c_id)), CT_bool) case_label]
        @ instrs,
        cleanup,
        ctx
     | ctyp ->
        raise (Reporting.err_general l (Printf.sprintf "Variant constructor %s : %s matching against non-variant type %s : %s"
                                                       (string_of_id ctor)
                                                       (string_of_typ variant_typ)
                                                       (string_of_fragment ~zencode:false frag)
                                                       (string_of_ctyp ctyp)))
     end

  | AP_wild _, _ -> [], [], ctx

  | AP_cons (hd_apat, tl_apat), (frag, CT_list ctyp) ->
     let hd_setup, hd_cleanup, ctx = compile_match ctx hd_apat (F_field (F_unary ("*", frag), "hd"), ctyp) case_label in
     let tl_setup, tl_cleanup, ctx = compile_match ctx tl_apat (F_field (F_unary ("*", frag), "tl"), CT_list ctyp) case_label in
     [ijump (F_op (frag, "==", F_lit V_null), CT_bool) case_label] @ hd_setup @ tl_setup, tl_cleanup @ hd_cleanup, ctx

  | AP_cons _, (_, _) ->
     raise (Reporting.err_general l "Tried to pattern match cons on non list type")

  | AP_nil _, (frag, _) -> [ijump (F_op (frag, "!=", F_lit V_null), CT_bool) case_label], [], ctx

let unit_fragment = (F_lit V_unit, CT_unit)

let rec compile_aexp ctx (AE_aux (aexp_aux, env, l)) =
  let ctx = { ctx with local_env = env } in
  match aexp_aux with
  | AE_let (mut, id, binding_typ, binding, (AE_aux (_, body_env, _) as body), body_typ) ->
     let binding_ctyp = ctyp_of_typ { ctx with local_env = body_env } binding_typ in
     let setup, call, cleanup = compile_aexp ctx binding in
     let letb_setup, letb_cleanup =
       [idecl binding_ctyp (name id);
        iblock (setup @ [call (CL_id (name id, binding_ctyp))] @ cleanup)],
       [iclear binding_ctyp (name id)]
     in
     let ctx = { ctx with locals = Bindings.add id (mut, binding_ctyp) ctx.locals } in
     let setup, call, cleanup = compile_aexp ctx body in
     letb_setup @ setup, call, cleanup @ letb_cleanup

  | AE_app (id, vs, typ) ->
     compile_funcall l ctx id vs typ

  | AE_val aval ->
     let setup, cval, cleanup = compile_aval l ctx aval in
     setup, (fun clexp -> icopy l clexp cval), cleanup

  (* Compile case statements *)
  | AE_case (aval, cases, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let aval_setup, cval, aval_cleanup = compile_aval l ctx aval in
     let case_return_id = ngensym () in
     let finish_match_label = label "finish_match_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _, _)
           | AE_aux (AE_val (AV_C_fragment (F_lit (V_bool true), _, _)), _, _) -> true
         | _ -> false
       in
       let case_label = label "case_" in
       let destructure, destructure_cleanup, ctx = compile_match ctx apat cval case_label in
       let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, body_call, body_cleanup = compile_aexp ctx body in
       let gs = ngensym () in
       let case_instrs =
         destructure @ [icomment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [idecl CT_bool gs; guard_call (CL_id (gs, CT_bool))] @ guard_cleanup
              @ [iif (F_unary ("!", F_id gs), CT_bool) (destructure_cleanup @ [igoto case_label]) [] CT_unit]
              @ [icomment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id (case_return_id, ctyp))] @ body_cleanup @ destructure_cleanup
         @ [igoto finish_match_label]
       in
       if is_dead_aexp body then
         [ilabel case_label]
       else
         [iblock case_instrs; ilabel case_label]
     in
     [icomment "begin match"]
     @ aval_setup @ [idecl ctyp case_return_id]
     @ List.concat (List.map compile_case cases)
     @ [imatch_failure ()]
     @ [ilabel finish_match_label],
     (fun clexp -> icopy l clexp (F_id case_return_id, ctyp)),
     [iclear ctyp case_return_id]
     @ aval_cleanup
     @ [icomment "end match"]

  (* Compile try statement *)
  | AE_try (aexp, cases, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let aexp_setup, aexp_call, aexp_cleanup = compile_aexp ctx aexp in
     let try_return_id = ngensym () in
     let handled_exception_label = label "handled_exception_" in
     let fallthrough_label = label "fallthrough_exception_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _, _)
         | AE_aux (AE_val (AV_C_fragment (F_lit (V_bool true), _, _)), _, _) -> true
         | _ -> false
       in
       let try_label = label "try_" in
       let exn_cval = (F_id current_exception, ctyp_of_typ ctx (mk_typ (Typ_id (mk_id "exception")))) in
       let destructure, destructure_cleanup, ctx = compile_match ctx apat exn_cval try_label in
       let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, body_call, body_cleanup = compile_aexp ctx body in
       let gs = ngensym () in
       let case_instrs =
         destructure @ [icomment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [idecl CT_bool gs; guard_call (CL_id (gs, CT_bool))] @ guard_cleanup
              @ [ijump (F_unary ("!", F_id gs), CT_bool) try_label]
              @ [icomment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id (try_return_id, ctyp))] @ body_cleanup @ destructure_cleanup
         @ [igoto handled_exception_label]
       in
       [iblock case_instrs; ilabel try_label]
     in
     assert (ctyp_equal ctyp (ctyp_of_typ ctx typ));
     [idecl ctyp try_return_id;
      itry_block (aexp_setup @ [aexp_call (CL_id (try_return_id, ctyp))] @ aexp_cleanup);
      ijump (F_unary ("!", F_id have_exception), CT_bool) handled_exception_label]
     @ List.concat (List.map compile_case cases)
     @ [igoto fallthrough_label;
        ilabel handled_exception_label;
        icopy l (CL_id (have_exception, CT_bool)) (F_lit (V_bool false), CT_bool);
        ilabel fallthrough_label],
     (fun clexp -> icopy l clexp (F_id try_return_id, ctyp)),
     []

  | AE_if (aval, then_aexp, else_aexp, if_typ) ->
     if is_dead_aexp then_aexp then
       compile_aexp ctx else_aexp
     else if is_dead_aexp else_aexp then
       compile_aexp ctx then_aexp
     else
       let if_ctyp = ctyp_of_typ ctx if_typ in
       let compile_branch aexp =
         let setup, call, cleanup = compile_aexp ctx aexp in
         fun clexp -> setup @ [call clexp] @ cleanup
       in
       let setup, cval, cleanup = compile_aval l ctx aval in
       setup,
       (fun clexp -> iif cval
                         (compile_branch then_aexp clexp)
                         (compile_branch else_aexp clexp)
                         if_ctyp),
       cleanup

  (* FIXME: AE_record_update could be AV_record_update - would reduce some copying. *)
  | AE_record_update (aval, fields, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let ctors = match ctyp with
       | CT_struct (_, ctors) -> List.fold_left (fun m (k, v) -> Bindings.add k v m) Bindings.empty ctors
       | _ -> raise (Reporting.err_general l "Cannot perform record update for non-record type")
     in
     let gs = ngensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup
       @ [icopy l (CL_field (CL_id (gs, ctyp), string_of_id id)) cval]
       @ field_cleanup
     in
     let setup, cval, cleanup = compile_aval l ctx aval in
     [idecl ctyp gs]
     @ setup
     @ [icopy l (CL_id (gs, ctyp)) cval]
     @ cleanup
     @ List.concat (List.map compile_fields (Bindings.bindings fields)),
     (fun clexp -> icopy l clexp (F_id gs, ctyp)),
     [iclear ctyp gs]

  | AE_short_circuit (SC_and, aval, aexp) ->
     let left_setup, cval, left_cleanup = compile_aval l ctx aval in
     let right_setup, call, right_cleanup = compile_aexp ctx aexp in
     let gs = ngensym () in
     left_setup
     @ [ idecl CT_bool gs;
         iif cval
             (right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup)
             [icopy l (CL_id (gs, CT_bool)) (F_lit (V_bool false), CT_bool)]
             CT_bool ]
     @ left_cleanup,
     (fun clexp -> icopy l clexp (F_id gs, CT_bool)),
     []
  | AE_short_circuit (SC_or, aval, aexp) ->
     let left_setup, cval, left_cleanup = compile_aval l ctx aval in
     let right_setup, call, right_cleanup = compile_aexp ctx aexp in
     let gs = ngensym () in
     left_setup
     @ [ idecl CT_bool gs;
         iif cval
             [icopy l (CL_id (gs, CT_bool)) (F_lit (V_bool true), CT_bool)]
             (right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup)
             CT_bool ]
     @ left_cleanup,
     (fun clexp -> icopy l clexp (F_id gs, CT_bool)),
     []

  (* This is a faster assignment rule for updating fields of a
     struct. *)
  | AE_assign (id, assign_typ, AE_aux (AE_record_update (AV_id (rid, _), fields, typ), _, _))
       when Id.compare id rid = 0 ->
     let compile_fields (field_id, aval) =
       let field_setup, cval, field_cleanup = compile_aval l ctx aval in
       field_setup
       @ [icopy l (CL_field (CL_id (name id, ctyp_of_typ ctx typ), string_of_id field_id)) cval]
       @ field_cleanup
     in
     List.concat (List.map compile_fields (Bindings.bindings fields)),
     (fun clexp -> icopy l clexp unit_fragment),
     []

  | AE_assign (id, assign_typ, aexp) ->
     let assign_ctyp =
       match Bindings.find_opt id ctx.locals with
       | Some (_, ctyp) -> ctyp
       | None -> ctyp_of_typ ctx assign_typ
     in
     let setup, call, cleanup = compile_aexp ctx aexp in
     setup @ [call (CL_id (name id, assign_ctyp))], (fun clexp -> icopy l clexp unit_fragment), cleanup

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
     let loop_test = (F_unary ("!", F_id gs), CT_bool) in
     [idecl CT_bool gs; idecl CT_unit unit_gs]
     @ [ilabel loop_start_label]
     @ [iblock (cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump loop_test loop_end_label]
                @ body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup
                @ [igoto loop_start_label])]
     @ [ilabel loop_end_label],
     (fun clexp -> icopy l clexp unit_fragment),
     []

  | AE_loop (Until, cond, body) ->
     let loop_start_label = label "repeat_" in
     let loop_end_label = label "until_" in
     let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
     let body_setup, body_call, body_cleanup = compile_aexp ctx body in
     let gs = ngensym () in
     let unit_gs = ngensym () in
     let loop_test = (F_id gs, CT_bool) in
     [idecl CT_bool gs; idecl CT_unit unit_gs]
     @ [ilabel loop_start_label]
     @ [iblock (body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup
                @ cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump loop_test loop_end_label]
                @ [igoto loop_start_label])]
     @ [ilabel loop_end_label],
     (fun clexp -> icopy l clexp unit_fragment),
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
         [idecl fn_return_ctyp gs;
          icopy l (CL_id (gs, fn_return_ctyp)) cval;
          ireturn (F_id gs, fn_return_ctyp)]
     in
     return_setup @ creturn,
     (fun clexp -> icomment "unreachable after return"),
     []

  | AE_throw (aval, typ) ->
     (* Cleanup info will be handled by fix_exceptions *)
     let throw_setup, cval, _ = compile_aval l ctx aval in
     throw_setup @ [ithrow cval],
     (fun clexp -> icomment "unreachable after throw"),
     []

  | AE_field (aval, id, _) ->
     let setup, cval, cleanup = compile_aval l ctx aval in
     let ctyp = match cval_ctyp cval with
       | CT_struct (struct_id, fields) ->
          begin match Util.assoc_compare_opt Id.compare id fields with
          | Some ctyp -> ctyp
          | None ->
             raise (Reporting.err_unreachable l __POS__
                      ("Struct " ^ string_of_id struct_id ^ " does not have expected field " ^ string_of_id id ^ "?"))
          end
       | _ ->
          raise (Reporting.err_unreachable l __POS__ "Field access on non-struct type in ANF representation!")
     in
     setup,
     (fun clexp -> icopy l clexp (F_field (fst cval, Util.zencode_string (string_of_id id)), ctyp)),
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
       [idecl (CT_fint 64) gs;
        iblock (setup @ [call (CL_id (gs, CT_fint 64))] @ cleanup)]
     in

     let loop_start_label = label "for_start_" in
     let loop_end_label = label "for_end_" in
     let body_setup, body_call, body_cleanup = compile_aexp ctx body in
     let body_gs = ngensym () in

     let loop_var = name loop_var in

     variable_init from_gs from_setup from_call from_cleanup
     @ variable_init to_gs to_setup to_call to_cleanup
     @ variable_init step_gs step_setup step_call step_cleanup
     @ [iblock ([idecl (CT_fint 64) loop_var;
                 icopy l (CL_id (loop_var, (CT_fint 64))) (F_id from_gs, (CT_fint 64));
                 idecl CT_unit body_gs;
                 iblock ([ilabel loop_start_label]
                         @ [ijump (F_op (F_id loop_var, (if is_inc then ">" else "<"), F_id to_gs), CT_bool) loop_end_label]
                         @ body_setup
                         @ [body_call (CL_id (body_gs, CT_unit))]
                         @ body_cleanup
                         @ [icopy l (CL_id (loop_var, (CT_fint 64)))
                                  (F_op (F_id loop_var, (if is_inc then "+" else "-"), F_id step_gs), (CT_fint 64))]
                         @ [igoto loop_start_label]);
                 ilabel loop_end_label])],
     (fun clexp -> icopy l clexp unit_fragment),
     []

and compile_block ctx = function
  | [] -> []
  | exp :: exps ->
     let setup, call, cleanup = compile_aexp ctx exp in
     let rest = compile_block ctx exps in
     let gs = ngensym () in
     iblock (setup @ [idecl CT_unit gs; call (CL_id (gs, CT_unit))] @ cleanup) :: rest

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
       List.fold_left (fun ctors (typ, id) -> Bindings.add id (ctyp_of_typ record_ctx typ) ctors) Bindings.empty ctors
     in
     CTD_struct (id, Bindings.bindings ctors),
     { ctx with records = Bindings.add id ctors ctx.records }

  | TD_variant (id, typq, tus, _) ->
     let compile_tu = function
       | Tu_aux (Tu_ty_id (typ, id), _) ->
          let ctx = { ctx with local_env = add_typquant (id_loc id) typq ctx.local_env } in
          ctyp_of_typ ctx typ, id
     in
     let ctus = List.fold_left (fun ctus (ctyp, id) -> Bindings.add id ctyp ctus) Bindings.empty (List.map compile_tu tus) in
     CTD_variant (id, Bindings.bindings ctus),
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
    | before, I_aux (I_if (cval, then_instrs, else_instrs, ctyp), _) :: after ->
       let historic = historic @ before in
       before
       @ [iif cval (rewrite_exception historic then_instrs) (rewrite_exception historic else_instrs) ctyp]
       @ rewrite_exception historic after
    | before, I_aux (I_throw cval, (_, l)) :: after ->
       before
       @ [icopy l (CL_id (current_exception, cval_ctyp cval)) cval;
          icopy l (CL_id (have_exception, CT_bool)) (F_lit (V_bool true), CT_bool)]
       @ generate_cleanup (historic @ before)
       @ [igoto end_block_label]
       @ rewrite_exception (historic @ before) after
    | before, (I_aux (I_funcall (x, _, f, args), _) as funcall) :: after ->
       let effects = match Env.get_val_spec f ctx.tc_env with
         | _, Typ_aux (Typ_fn (_, _, effects), _) -> effects
         | exception (Type_error _) -> no_effect (* nullary union constructor, so no val spec *)
         | _ -> assert false (* valspec must have function type *)
       in
       if has_effect effects BE_escape then
         before
         @ [funcall;
            iif (F_id have_exception, CT_bool) (generate_cleanup (historic @ before) @ [igoto end_block_label]) [] CT_unit]
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
     let destructure, cleanup, _ = compile_match ctx apat (F_id (name gs), ctyp) label in
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
     @ [idecl (CT_tup ctyps) (name arg_id)]
     @ List.mapi (fun i (id, ctyp) -> icopy l (CL_tuple (CL_id (name arg_id, CT_tup ctyps), i)) (F_id (name id), ctyp)) new_ids,
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
    | I_return _ | I_undefined _ | I_if _ | I_block _ -> true
    | _ -> false
  in
  let rec rewrite_return historic instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_block instrs, _) :: after ->
       before
       @ [iblock (rewrite_return (historic @ before) instrs)]
       @ rewrite_return (historic @ before) after
    | before, I_aux (I_if (cval, then_instrs, else_instrs, ctyp), _) :: after ->
       let historic = historic @ before in
       before
       @ [iif cval (rewrite_return historic then_instrs) (rewrite_return historic else_instrs) ctyp]
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
     let aexp = ctx.optimize_anf ctx (no_shadow IdSet.empty (anf exp)) in
     let setup, call, cleanup = compile_aexp ctx aexp in
     let instrs = setup @ [call (CL_id (name id, ctyp_of_typ ctx typ))] @ cleanup in
     [CDEF_reg_dec (id, ctyp_of_typ ctx typ, instrs)], ctx

  | DEF_reg_dec (DEC_aux (_, (l, _))) ->
     raise (Reporting.err_general l "Cannot compile alias register declaration")

  | DEF_spec (VS_aux (VS_val_spec (_, id, _, _), _)) ->
     let quant, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let arg_typs, ret_typ = match fn_typ with
       | Typ_fn (arg_typs, ret_typ, _) -> arg_typs, ret_typ
       | _ -> assert false
     in
     let ctx' = { ctx with local_env = add_typquant (id_loc id) quant ctx.local_env } in
     let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ in
     [CDEF_spec (id, arg_ctyps, ret_ctyp)], ctx

  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (pat, exp), _)), _)]), _)) ->
     Util.progress "Compiling " (string_of_id id) n total;

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

     (* Optimize and compile the expression to ANF. *)
     let aexp = no_shadow (pat_ids pat) (anf exp) in
     let aexp = ctx.optimize_anf ctx aexp in

     let setup, call, cleanup = compile_aexp ctx aexp in
     let destructure, destructure_cleanup =
       compiled_args |> List.map snd |> combine_destructure_cleanup |> fix_destructure fundef_label
     in

     let instrs = arg_setup @ destructure @ setup @ [call (CL_id (return, ret_ctyp))] @ cleanup @ destructure_cleanup @ arg_cleanup in
     let instrs = fix_early_return (CL_id (return, ret_ctyp)) instrs in
     let instrs = fix_exception ~return:(Some ret_ctyp) ctx instrs in

     if Id.compare (mk_id !opt_debug_function) id = 0 then
       let header =
         Printf.sprintf "Sail IR for %s %s(%s) : (%s) -> %s" Util.("function" |> red |> clear) (string_of_id id)
                        (Util.string_of_list ", " string_of_id (List.map fst compiled_args))
                        (Util.string_of_list ", " (fun ctyp -> Util.(string_of_ctyp ctyp |> yellow |> clear)) arg_ctyps)
                        Util.(string_of_ctyp ret_ctyp |> yellow |> clear)
       in
       prerr_endline (Util.header header (List.length arg_ctyps + 2));
       prerr_endline (Pretty_print_sail.to_string PPrint.(separate_map hardline pp_instr instrs))
     else ();

     if !opt_debug_flow_graphs then
       begin
         let instrs = Jib_optimize.(instrs |> optimize_unit |> flatten_instrs) in
         let root, _, cfg = Jib_ssa.control_flow_graph instrs in
         let idom = Jib_ssa.immediate_dominators cfg root in
         let _, cfg = Jib_ssa.ssa instrs in
         let out_chan = open_out (Util.zencode_string (string_of_id id) ^ ".gv") in
         Jib_ssa.make_dot out_chan cfg;
         close_out out_chan;
         let out_chan = open_out (Util.zencode_string (string_of_id id) ^ ".dom.gv") in
         Jib_ssa.make_dominators_dot out_chan idom cfg;
         close_out out_chan;
       end;

     [CDEF_fundef (id, None, List.map fst compiled_args, instrs)], orig_ctx

  | DEF_fundef (FD_aux (FD_function (_, _, _, []), (l, _))) ->
     raise (Reporting.err_general l "Encountered function with no clauses")

  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), (l, _))) ->
     raise (Reporting.err_general l "Encountered function with multiple clauses")

  (* All abbreviations should expanded by the typechecker, so we don't
     need to translate type abbreviations into C typedefs. *)
  | DEF_type (TD_aux (TD_abbrev _, _)) -> [], ctx

  | DEF_type type_def ->
     let tdef, ctx = compile_type_def ctx type_def in
     [CDEF_type tdef], ctx

  | DEF_val (LB_aux (LB_val (pat, exp), _)) ->
     let ctyp = ctyp_of_typ ctx (typ_of_pat pat) in
     let aexp = ctx.optimize_anf ctx (no_shadow IdSet.empty (anf exp)) in
     let setup, call, cleanup = compile_aexp ctx aexp in
     let apat = anf_pat ~global:true pat in
     let gs = ngensym () in
     let end_label = label "let_end_" in
     let destructure, destructure_cleanup, _ = compile_match ctx apat (F_id gs, ctyp) end_label in
     let gs_setup, gs_cleanup =
       [idecl ctyp gs], [iclear ctyp gs]
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

  | DEF_internal_mutrec fundefs ->
     let defs = List.map (fun fdef -> DEF_fundef fdef) fundefs in
     List.fold_left (fun (cdefs, ctx) def -> let cdefs', ctx = compile_def n total ctx def in (cdefs @ cdefs', ctx)) ([], ctx) defs

  (* Scattereds and mapdefs should be removed by this point *)
  | (DEF_scattered _ | DEF_mapdef _) as def ->
     raise (Reporting.err_general Parse_ast.Unknown ("Could not compile:\n" ^ Pretty_print_sail.to_string (Pretty_print_sail.doc_def def)))

let rec specialize_variants ctx prior =
  let unifications = ref (Bindings.empty) in

  let fix_variant_ctyp var_id new_ctors = function
    | CT_variant (id, ctors) when Id.compare id var_id = 0 -> CT_variant (id, new_ctors)
    | ctyp -> ctyp
  in

  let specialize_constructor ctx ctor_id ctyp =
    function
    | I_aux (I_funcall (clexp, extern, id, [cval]), ((_, l) as aux)) as instr when Id.compare id ctor_id = 0 ->
       (* Work out how each call to a constructor in instantiated and add that to unifications *)
       let unification = List.map ctyp_suprema (ctyp_unify ctyp (cval_ctyp cval)) in
       let mono_id = append_id ctor_id ("_" ^ Util.string_of_list "_" (fun ctyp -> Util.zencode_string (string_of_ctyp ctyp)) unification) in
       unifications := Bindings.add mono_id (ctyp_suprema (cval_ctyp cval)) !unifications;

       (* We need to cast each cval to it's ctyp_suprema in order to put it in the most general constructor *)
       let casts =
         let cast_to_suprema (frag, ctyp) =
           let suprema = ctyp_suprema ctyp in
           if ctyp_equal ctyp suprema then
             [], (unpoly frag, ctyp), []
           else
             let gs = ngensym () in
             [idecl suprema gs;
              icopy l (CL_id (gs, suprema)) (unpoly frag, ctyp)],
             (F_id gs, suprema),
             [iclear suprema gs]
         in
         List.map cast_to_suprema [cval]
       in
       let setup = List.concat (List.map (fun (setup, _, _) -> setup) casts) in
       let cvals = List.map (fun (_, cval, _) -> cval) casts in
       let cleanup = List.concat (List.map (fun (_, _, cleanup) -> cleanup) casts) in

       let mk_funcall instr =
         if List.length setup = 0 then
           instr
         else
           iblock (setup @ [instr] @ cleanup)
       in

       mk_funcall (I_aux (I_funcall (clexp, extern, mono_id, cvals), aux))

    | I_aux (I_funcall (clexp, extern, id, cvals), ((_, l) as aux)) as instr when Id.compare id ctor_id = 0 ->
       Reporting.unreachable l __POS__ "Multiple argument constructor found"

    | instr -> instr
  in

  function
  | (CDEF_type (CTD_variant (var_id, ctors)) as cdef) :: cdefs ->
     let polymorphic_ctors = List.filter (fun (_, ctyp) -> is_polymorphic ctyp) ctors in

     let cdefs =
       List.fold_left (fun cdefs (ctor_id, ctyp) -> List.map (cdef_map_instr (specialize_constructor ctx ctor_id ctyp)) cdefs)
                      cdefs
                      polymorphic_ctors
     in

     let monomorphic_ctors = List.filter (fun (_, ctyp) -> not (is_polymorphic ctyp)) ctors in
     let specialized_ctors = Bindings.bindings !unifications in
     let new_ctors = monomorphic_ctors @ specialized_ctors in

     let ctx = {
         ctx with variants = Bindings.add var_id
                               (List.fold_left (fun m (id, ctyp) -> Bindings.add id ctyp m) !unifications monomorphic_ctors)
                               ctx.variants
       } in

     let cdefs = List.map (cdef_map_ctyp (map_ctyp (fix_variant_ctyp var_id new_ctors))) cdefs in
     let prior = List.map (cdef_map_ctyp (map_ctyp (fix_variant_ctyp var_id new_ctors))) prior in
     specialize_variants ctx (CDEF_type (CTD_variant (var_id, new_ctors)) :: prior) cdefs

  | cdef :: cdefs ->
     let remove_poly (I_aux (instr, aux)) =
       match instr with
       | I_copy (clexp, (frag, ctyp)) when is_polymorphic ctyp ->
          I_aux (I_copy (clexp, (frag, ctyp_suprema (clexp_ctyp clexp))), aux)
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

let compile_ast ctx (Defs defs) =
  let assert_vs = Initial_check.extern_of_string (mk_id "sail_assert") "(bool, string) -> unit effect {escape}" in
  let exit_vs = Initial_check.extern_of_string (mk_id "sail_exit") "unit -> unit effect {escape}" in

  let ctx = { ctx with tc_env = snd (Type_error.check ctx.tc_env (Defs [assert_vs; exit_vs])) } in

  if !opt_memo_cache then
    (try
       if Sys.is_directory "_sbuild" then
         ()
       else
         raise (Reporting.err_general Parse_ast.Unknown "_sbuild exists, but is a file not a directory!")
     with
     | Sys_error _ -> Unix.mkdir "_sbuild" 0o775)
  else ();

  let total = List.length defs in
  let _, chunks, ctx =
    List.fold_left (fun (n, chunks, ctx) def -> let defs, ctx = compile_def n total ctx def in n + 1, defs :: chunks, ctx) (1, [], ctx) defs
  in
  let cdefs = List.concat (List.rev chunks) in
  let cdefs, ctx = specialize_variants ctx [] cdefs in
  let cdefs = sort_ctype_defs cdefs in
  cdefs, ctx
