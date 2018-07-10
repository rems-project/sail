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
open Bytecode
open Bytecode_util
open Type_check
open PPrint
open Value2

open Anf

module Big_int = Nat_big_num

let c_verbosity = ref 0
let opt_ddump_flow_graphs = ref false
let opt_trace = ref false
let opt_static = ref false

(* Optimization flags *)
let optimize_primops = ref false
let optimize_z3 = ref false
let optimize_hoist_allocations = ref false
let optimize_struct_updates = ref false

let c_debug str =
  if !c_verbosity > 0 then prerr_endline (Lazy.force str) else ()

let c_error ?loc:(l=Parse_ast.Unknown) message =
  raise (Reporting_basic.err_general l ("\nC backend: " ^ message))

let zencode_id = function
  | Id_aux (Id str, l) -> Id_aux (Id (Util.zencode_string str), l)
  | Id_aux (DeIid str, l) -> Id_aux (Id (Util.zencode_string ("op " ^ str)), l)

(**************************************************************************)
(* 2. Converting sail types to C types                                    *)
(**************************************************************************)

let max_int64 = Big_int.of_int64 Int64.max_int
let min_int64 = Big_int.of_int64 Int64.min_int

type ctx =
  { records : (ctyp Bindings.t) Bindings.t;
    enums : IdSet.t Bindings.t;
    variants : (ctyp Bindings.t) Bindings.t;
    tc_env : Env.t;
    local_env : Env.t;
    letbinds : int list;
    recursive_functions : IdSet.t;
    no_raw : bool;
  }

let initial_ctx env =
  { records = Bindings.empty;
    enums = Bindings.empty;
    variants = Bindings.empty;
    tc_env = env;
    local_env = env;
    letbinds = [];
    recursive_functions = IdSet.empty;
    no_raw = false;
  }

let rec ctyp_equal ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_int, CT_int -> true
  | CT_bits d1, CT_bits d2 -> d1 = d2
  | CT_bits64 (m1, d1), CT_bits64 (m2, d2) -> m1 = m2 && d1 = d2
  | CT_bit, CT_bit -> true
  | CT_int64, CT_int64 -> true
  | CT_unit, CT_unit -> true
  | CT_bool, CT_bool -> true
  | CT_struct (id1, _), CT_struct (id2, _) -> Id.compare id1 id2 = 0
  | CT_enum (id1, _), CT_enum (id2, _) -> Id.compare id1 id2 = 0
  | CT_variant (id1, _), CT_variant (id2, _) -> Id.compare id1 id2 = 0
  | CT_tup ctyps1, CT_tup ctyps2 when List.length ctyps1 = List.length ctyps2 ->
     List.for_all2 ctyp_equal ctyps1 ctyps2
  | CT_string, CT_string -> true
  | CT_real, CT_real -> true
  | CT_vector (d1, ctyp1), CT_vector (d2, ctyp2) -> d1 = d2 && ctyp_equal ctyp1 ctyp2
  | CT_list ctyp1, CT_list ctyp2 -> ctyp_equal ctyp1 ctyp2
  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_equal ctyp1 ctyp2
  | _, _ -> false

(** Convert a sail type into a C-type **)
let rec ctyp_of_typ ctx typ =
  let Typ_aux (typ_aux, l) as typ = Env.expand_synonyms ctx.tc_env typ in
  match typ_aux with
  | Typ_id id when string_of_id id = "bit" -> CT_bit
  | Typ_id id when string_of_id id = "bool" -> CT_bool
  | Typ_id id when string_of_id id = "int" -> CT_int
  | Typ_id id when string_of_id id = "nat" -> CT_int
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" ->
     begin
       match destruct_range Env.empty typ with
       | None -> assert false (* Checked if range type in guard *)
       | Some (kids, constr, n, m) ->
          match nexp_simp n, nexp_simp m with
          | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
               when Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 ->
             CT_int64
          | n, m when !optimize_z3 ->
             prerr_endline ("optimize atom " ^ string_of_nexp n ^ ", " ^ string_of_nexp m ^ " in context " ^ (Util.string_of_list ", " string_of_n_constraint (Env.get_constraints ctx.local_env)));
             if prove ctx.local_env (nc_lteq (nconstant min_int64) n) && prove ctx.local_env (nc_lteq m (nconstant max_int64)) then
               (prerr_endline "yes"; CT_int64)
             else
               (prerr_endline "no"; CT_int)
          | _ -> CT_int
     end

  | Typ_app (id, [Typ_arg_aux (Typ_arg_typ typ, _)]) when string_of_id id = "list" ->
     CT_list (ctyp_of_typ ctx typ)

  | Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _);
                  Typ_arg_aux (Typ_arg_order ord, _);
                  Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id vtyp_id, _)), _)])
       when string_of_id id = "vector" && string_of_id vtyp_id = "bit" ->
     begin
       let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
       match nexp_simp n with
       | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> CT_bits64 (Big_int.to_int n, direction)
       | _ -> CT_bits direction
     end
  | Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _);
                  Typ_arg_aux (Typ_arg_order ord, _);
                  Typ_arg_aux (Typ_arg_typ typ, _)])
       when string_of_id id = "vector" ->
     let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
     CT_vector (direction, ctyp_of_typ ctx typ)

  | Typ_id id when string_of_id id = "unit" -> CT_unit
  | Typ_id id when string_of_id id = "string" -> CT_string
  | Typ_id id when string_of_id id = "real" -> CT_real

  | Typ_app (id, [Typ_arg_aux (Typ_arg_typ typ, _)]) when string_of_id id = "register" || string_of_id id = "ref" ->
     CT_ref (ctyp_of_typ ctx typ)

  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.records -> CT_struct (id, Bindings.find id ctx.records |> Bindings.bindings)
  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.variants -> CT_variant (id, Bindings.find id ctx.variants |> Bindings.bindings)
  | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)

  | Typ_tup typs -> CT_tup (List.map (ctyp_of_typ ctx) typs)

  | Typ_exist _ when !optimize_z3 ->
     (* Use Type_check.destruct_exist when optimising with z3, to ensure that we
        don't cause any type variable clashes in local_env. *)
     begin match destruct_exist ctx.local_env typ with
     | Some (kids, nc, typ) ->
        c_debug (lazy ("optimize existential: " ^ string_of_n_constraint nc ^ ". " ^ string_of_typ typ
                       ^ " in context " ^ (Util.string_of_list ", " string_of_n_constraint (Env.get_constraints ctx.local_env))));
        let env = add_existential l kids nc ctx.local_env in
        ctyp_of_typ { ctx with local_env = env } typ
     | None -> c_error "Existential cannot be destructured. This should be impossible!"
     end

  | Typ_exist (_, _, typ) -> ctyp_of_typ ctx typ

  | _ -> c_error ~loc:l ("No C type for type " ^ string_of_typ typ)

let rec is_stack_ctyp ctyp = match ctyp with
  | CT_bits64 _ | CT_int64 | CT_bit | CT_unit | CT_bool | CT_enum _ -> true
  | CT_bits _ | CT_int | CT_real | CT_string | CT_list _ | CT_vector _ -> false
  | CT_struct (_, fields) -> List.for_all (fun (_, ctyp) -> is_stack_ctyp ctyp) fields
  | CT_variant (_, ctors) -> false (* List.for_all (fun (_, ctyp) -> is_stack_ctyp ctyp) ctors *) (*FIXME*)
  | CT_tup ctyps -> List.for_all is_stack_ctyp ctyps
  | CT_ref ctyp -> true

let is_stack_typ ctx typ = is_stack_ctyp (ctyp_of_typ ctx typ)

let ctor_bindings = List.fold_left (fun map (id, ctyp) -> Bindings.add id ctyp map) Bindings.empty

(**************************************************************************)
(* 3. Optimization of primitives and literals                             *)
(**************************************************************************)

let hex_char =
  let open Sail2_values in
  function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let literal_to_fragment (L_aux (l_aux, _) as lit) =
  match l_aux with
  | L_num n when Big_int.less_equal min_int64 n && Big_int.less_equal n max_int64 ->
     Some (F_lit (V_int n))
  | L_hex str when String.length str <= 16 ->
     let padding = 16 - String.length str in
     let padding = Util.list_init padding (fun _ -> Sail2_values.B0) in
     let content = Util.string_to_list str |> List.map hex_char |> List.concat in
     Some (F_lit (V_bits (padding @ content)))
  | L_unit -> Some (F_lit V_unit)
  | L_true -> Some (F_lit (V_bool true))
  | L_false -> Some (F_lit (V_bool false))
  | _ -> None

let c_literals ctx =
  let rec c_literal env l = function
    | AV_lit (lit, typ) as v when is_stack_ctyp (ctyp_of_typ { ctx with local_env = env } typ) ->
       begin
         match literal_to_fragment lit with
         | Some frag -> AV_C_fragment (frag, typ)
         | None -> v
       end
    | AV_tuple avals -> AV_tuple (List.map (c_literal env l) avals)
    | v -> v
  in
  map_aval c_literal

let mask m =
  if Big_int.less_equal m (Big_int.of_int 64) then
    let n = Big_int.to_int m in
    if n mod 4 == 0
    then "UINT64_C(0x" ^ String.make (16 - n / 4) '0' ^ String.make (n / 4) 'F' ^ ")"
    else "UINT64_C(" ^ String.make (64 - n) '0' ^ String.make n '1' ^ ")"
  else
    failwith "Tried to create a mask literal for a vector greater than 64 bits."

let rec is_bitvector = function
  | [] -> true
  | AV_lit (L_aux (L_zero, _), _) :: avals -> is_bitvector avals
  | AV_lit (L_aux (L_one, _), _) :: avals -> is_bitvector avals
  | _ :: _ -> false

let rec value_of_aval_bit = function
  | AV_lit (L_aux (L_zero, _), _) -> Sail2_values.B0
  | AV_lit (L_aux (L_one, _), _) -> Sail2_values.B1
  | _ -> assert false

let rec c_aval ctx = function
  | AV_lit (lit, typ) as v ->
     begin
       match literal_to_fragment lit with
       | Some frag -> AV_C_fragment (frag, typ)
       | None -> v
     end
  | AV_C_fragment (str, typ) -> AV_C_fragment (str, typ)
  (* An id can be converted to a C fragment if it's type can be stack-allocated. *)
  | AV_id (id, lvar) as v ->
     begin
       match lvar with
       | Local (_, typ) when is_stack_typ ctx typ ->
          AV_C_fragment (F_id id, typ)
       | Register (_, _, typ) when is_stack_typ ctx typ ->
          AV_C_fragment (F_id id, typ)
       | _ -> v
     end
  | AV_vector (v, typ) when is_bitvector v && List.length v <= 64 ->
     let bitstring = F_lit (V_bits (List.map value_of_aval_bit v)) in
     AV_C_fragment (bitstring, typ)
  | AV_tuple avals -> AV_tuple (List.map (c_aval ctx) avals)
  | aval -> aval

let is_c_fragment = function
  | AV_C_fragment _ -> true
  | _ -> false

let c_fragment = function
  | AV_C_fragment (frag, _) -> frag
  | _ -> assert false

let v_mask_lower i = F_lit (V_bits (Util.list_init i (fun _ -> Sail2_values.B1)))

let analyze_primop' ctx env l id args typ =
  let ctx = { ctx with local_env = env } in
  let no_change = AE_app (id, args, typ) in
  let args = List.map (c_aval ctx) args in
  let extern = if Env.is_extern id ctx.tc_env "c" then Env.get_extern id ctx.tc_env "c" else failwith "Not extern" in
  (* prerr_endline ("Analysing: " ^ string_of_typ typ ^ " " ^ extern ^ Pretty_print_sail.to_string (separate_map (string ", ") pp_aval args)); *)

  let v_one = F_lit (V_int (Big_int.of_int 1)) in
  let v_int n = F_lit (V_int (Big_int.of_int n)) in

  match extern, args with
  | "eq_bits", [AV_C_fragment (v1, typ1); AV_C_fragment (v2, typ2)] ->
     AE_val (AV_C_fragment (F_op (v1, "==", v2), typ))

  | "neq_bits", [AV_C_fragment (v1, typ1); AV_C_fragment (v2, typ2)] ->
     AE_val (AV_C_fragment (F_op (v1, "!=", v2), typ))

  | "eq_int", [AV_C_fragment (v1, typ1); AV_C_fragment (v2, typ2)] ->
     AE_val (AV_C_fragment (F_op (v1, "==", v2), typ))

  | "zeros", [_] ->
     begin match destruct_vector ctx.tc_env typ with
     | Some (Nexp_aux (Nexp_constant n, _), _, Typ_aux (Typ_id id, _))
          when string_of_id id = "bit" && Big_int.less_equal n (Big_int.of_int 64) ->
        AE_val (AV_C_fragment (F_raw "0x0", typ))
     | _ -> no_change
     end

  | "xor_bits", [AV_C_fragment (v1, typ1); AV_C_fragment (v2, typ2)] ->
     AE_val (AV_C_fragment (F_op (v1, "^", v2), typ))

  | "or_bits", [AV_C_fragment (v1, typ1); AV_C_fragment (v2, typ2)] ->
     AE_val (AV_C_fragment (F_op (v1, "|", v2), typ))

  | "and_bits", [AV_C_fragment (v1, typ1); AV_C_fragment (v2, typ2)] ->
     AE_val (AV_C_fragment (F_op (v1, "&", v2), typ))

  | "not_bits", [AV_C_fragment (v, _)] ->
     begin match destruct_vector ctx.tc_env typ with
     | Some (Nexp_aux (Nexp_constant n, _), _, Typ_aux (Typ_id id, _))
          when string_of_id id = "bit" && Big_int.less_equal n (Big_int.of_int 64) ->
        AE_val (AV_C_fragment (F_op (F_unary ("~", v), "&", v_mask_lower (Big_int.to_int n)), typ))
     | _ -> no_change
     end

  | "vector_subrange", [AV_C_fragment (vec, _); AV_C_fragment (f, _); AV_C_fragment (t, _)] ->
     let len = F_op (f, "-", F_op (t, "-", v_one)) in
     AE_val (AV_C_fragment (F_op (F_call ("safe_rshift", [F_raw "UINT64_MAX"; F_op (v_int 64, "-", len)]), "&", F_op (vec, ">>", t)), typ))

  | "vector_access", [AV_C_fragment (vec, _); AV_C_fragment (n, _)] ->
     AE_val (AV_C_fragment (F_op (v_one, "&", F_op (vec, ">>", n)), typ))

  | "eq_bit", [AV_C_fragment (a, _); AV_C_fragment (b, _)] ->
     AE_val (AV_C_fragment (F_op (a, "==", b), typ))

  | "slice", [AV_C_fragment (vec, _); AV_C_fragment (start, _); AV_C_fragment (len, _)] ->
     AE_val (AV_C_fragment (F_op (F_call ("safe_rshift", [F_raw "UINT64_MAX"; F_op (v_int 64, "-", len)]), "&", F_op (vec, ">>", start)), typ))

  | "undefined_bit", _ ->
     AE_val (AV_C_fragment (F_lit (V_bit Sail2_values.B0), typ))

  | "undefined_vector", [AV_C_fragment (len, _); _] ->
     begin match destruct_vector ctx.tc_env typ with
     | Some (Nexp_aux (Nexp_constant n, _), _, Typ_aux (Typ_id id, _))
          when string_of_id id = "bit" && Big_int.less_equal n (Big_int.of_int 64) ->
       AE_val (AV_C_fragment (F_lit (V_bit Sail2_values.B0), typ))
     | _ -> no_change
     end

  | "sail_uint", [AV_C_fragment (frag, vtyp)] ->
     begin match destruct_vector ctx.tc_env vtyp with
     | Some (Nexp_aux (Nexp_constant n, _), _, _)
          when Big_int.less_equal n (Big_int.of_int 63) && is_stack_typ ctx typ ->
        prerr_endline "Optimizing uint"; (* TODO: Not sure this ever fires *)
        AE_val (AV_C_fragment (frag, typ))
     | _ -> no_change
     end

  | "replicate_bits", [AV_C_fragment (vec, vtyp); AV_C_fragment (times, _)] ->
     begin match destruct_vector ctx.tc_env typ, destruct_vector ctx.tc_env vtyp with
     | Some (Nexp_aux (Nexp_constant n, _), _, _), Some (Nexp_aux (Nexp_constant m, _), _, _)
          when Big_int.less_equal n (Big_int.of_int 64) ->
        AE_val (AV_C_fragment (F_call ("fast_replicate_bits", [F_lit (V_int m); vec; times]), typ))
     | _ -> no_change
     end

  | "undefined_bool", _ ->
     AE_val (AV_C_fragment (F_lit (V_bool false), typ))

  | _, _ -> no_change

let analyze_primop ctx env l id args typ =
  let no_change = AE_app (id, args, typ) in
  if !optimize_primops then
    try analyze_primop' ctx env l id args typ with
    | Failure _ -> no_change
  else
    no_change

(**************************************************************************)
(* 4. Conversion to low-level AST                                         *)
(**************************************************************************)

(** We now use a low-level AST (see language/bytecode.ott) that is
   only slightly abstracted away from C. To be succint in comments we
   usually refer to this as Sail IR or IR rather than low-level AST
   repeatedly.

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

let ctype_def_ctyps = function
  | CTD_enum _ -> []
  | CTD_struct (_, fields) -> List.map snd fields
  | CTD_variant (_, ctors) -> List.map snd ctors

let cval_ctyp = function (_, ctyp) -> ctyp

let rec map_instrs f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, f (List.map (map_instrs f) instrs1), f (List.map (map_instrs f) instrs2), ctyp)
    | I_funcall _ | I_convert _ | I_copy _ | I_clear _ | I_jump _ | I_throw _ | I_return _ -> instr
    | I_block instrs -> I_block (f (List.map (map_instrs f) instrs))
    | I_try_block instrs -> I_try_block (f (List.map (map_instrs f) instrs))
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure -> instr
  in
  I_aux (instr, aux)

let cval_rename from_id to_id (frag, ctyp) = (frag_rename from_id to_id frag, ctyp)

let rec instr_ctyps (I_aux (instr, aux)) =
  match instr with
  | I_decl (ctyp, _) | I_reset (ctyp, _) | I_clear (ctyp, _) -> [ctyp]
  | I_init (ctyp, _, cval) | I_reinit (ctyp, _, cval) -> [ctyp; cval_ctyp cval]
  | I_if (cval, instrs1, instrs2, ctyp) ->
     ctyp :: cval_ctyp cval :: List.concat (List.map instr_ctyps instrs1 @ List.map instr_ctyps instrs2)
  | I_funcall (_, _, _, cvals, ctyp) ->
     ctyp :: List.map cval_ctyp cvals
  | I_convert (_, ctyp1, _, ctyp2) -> [ctyp1; ctyp2]
  | I_copy (_, cval) -> [cval_ctyp cval]
  | I_block instrs | I_try_block instrs -> List.concat (List.map instr_ctyps instrs)
  | I_throw cval | I_jump (cval, _) | I_return cval -> [cval_ctyp cval]
  | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure -> []

let rec c_ast_registers = function
  | CDEF_reg_dec (id, ctyp, instrs) :: ast -> (id, ctyp, instrs) :: c_ast_registers ast
  | _ :: ast -> c_ast_registers ast
  | [] -> []

let cdef_ctyps ctx = function
  | CDEF_reg_dec (_, ctyp, instrs) -> ctyp :: List.concat (List.map instr_ctyps instrs)
  | CDEF_spec (_, ctyps, ctyp) -> ctyp :: ctyps
  | CDEF_fundef (id, _, _, instrs) ->
     let _, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let arg_typs, ret_typ = match fn_typ with
       | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
       | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
       | _ -> assert false
     in
     let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx) arg_typs, ctyp_of_typ ctx ret_typ in
     ret_ctyp :: arg_ctyps @ List.concat (List.map instr_ctyps instrs)

  | CDEF_startup (id, instrs) | CDEF_finish (id, instrs) -> List.concat (List.map instr_ctyps instrs)
  | CDEF_type tdef -> ctype_def_ctyps tdef
  | CDEF_let (_, bindings, instrs) ->
     List.map snd bindings
     @ List.concat (List.map instr_ctyps instrs)

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

let rec chunkify n xs =
  match Util.take n xs, Util.drop n xs with
  | xs, [] -> [xs]
  | xs, ys -> xs :: chunkify n ys

let rec compile_aval ctx = function
  | AV_C_fragment (frag, typ) ->
     [], (frag, ctyp_of_typ ctx typ), []

  | AV_id (id, typ) ->
     [], (F_id id, ctyp_of_typ ctx (lvar_typ typ)), []

  | AV_ref (id, typ) ->
     [], (F_ref id, CT_ref (ctyp_of_typ ctx (lvar_typ typ))), []

  | AV_lit (L_aux (L_string str, _), typ) ->
     [], (F_lit (V_string (String.escaped str)), ctyp_of_typ ctx typ), []

  | AV_lit (L_aux (L_num n, _), typ) when Big_int.less_equal min_int64 n && Big_int.less_equal n max_int64 ->
     let gs = gensym () in
     [iinit CT_int gs (F_lit (V_int n), CT_int64)],
     (F_id gs, CT_int),
     [iclear CT_int gs]

  | AV_lit (L_aux (L_num n, _), typ) ->
     let gs = gensym () in
     [iinit CT_int gs (F_lit (V_string (Big_int.to_string n)), CT_string)],
     (F_id gs, CT_int),
     [iclear CT_int gs]

  | AV_lit (L_aux (L_zero, _), _) -> [], (F_lit (V_bit Sail2_values.B0), CT_bit), []
  | AV_lit (L_aux (L_one, _), _) -> [], (F_lit (V_bit Sail2_values.B1), CT_bit), []

  | AV_lit (L_aux (L_true, _), _) -> [], (F_lit (V_bool true), CT_bool), []
  | AV_lit (L_aux (L_false, _), _) -> [], (F_lit (V_bool false), CT_bool), []

  | AV_lit (L_aux (L_real str, _), _) ->
     let gs = gensym () in
     [iinit CT_real gs (F_lit (V_string str), CT_string)],
     (F_id gs, CT_real),
     [iclear CT_real gs]

  | AV_lit (L_aux (_, l) as lit, _) ->
     c_error ~loc:l ("Encountered unexpected literal " ^ string_of_lit lit)

  | AV_tuple avals ->
     let elements = List.map (compile_aval ctx) avals in
     let cvals = List.map (fun (_, cval, _) -> cval) elements in
     let setup = List.concat (List.map (fun (setup, _, _) -> setup) elements) in
     let cleanup = List.concat (List.rev (List.map (fun (_, _, cleanup) -> cleanup) elements)) in
     let tup_ctyp = CT_tup (List.map cval_ctyp cvals) in
     let gs = gensym () in
     setup
     @ [idecl tup_ctyp gs]
     @ List.mapi (fun n cval -> icopy (CL_field (gs, "tup" ^ string_of_int n)) cval) cvals,
     (F_id gs, CT_tup (List.map cval_ctyp cvals)),
     [iclear tup_ctyp gs]
     @ cleanup

  | AV_record (fields, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let gs = gensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval ctx aval in
       field_setup
       @ [icopy (CL_field (gs, string_of_id id)) cval]
       @ field_cleanup
     in
     [idecl ctyp gs]
     @ List.concat (List.map compile_fields (Bindings.bindings fields)),
     (F_id gs, ctyp),
     [iclear ctyp gs]

  | AV_vector ([], _) ->
     c_error "Encountered empty vector literal"

  (* Convert a small bitvector to a uint64_t literal. *)
  | AV_vector (avals, typ) when is_bitvector avals && List.length avals <= 64 ->
     begin
       let bitstring = F_lit (V_bits (List.map value_of_aval_bit avals)) in
       let len = List.length avals in
       match destruct_vector ctx.tc_env typ with
       | Some (_, Ord_aux (Ord_inc, _), _) ->
          [], (bitstring, CT_bits64 (len, false)), []
       | Some (_, Ord_aux (Ord_dec, _), _) ->
          [], (bitstring, CT_bits64 (len, true)), []
       | Some _ ->
          c_error "Encountered order polymorphic bitvector literal"
       | None ->
          c_error "Encountered vector literal without vector type"
     end

  (* Convert a bitvector literal that is larger than 64-bits to a
     variable size bitvector, converting it in 64-bit chunks. *)
  | AV_vector (avals, typ) when is_bitvector avals ->
     let len = List.length avals in
     let bitstring avals = F_lit (V_bits (List.map value_of_aval_bit avals)) in
     let first_chunk = bitstring (Util.take (len mod 64) avals) in
     let chunks = Util.drop (len mod 64) avals |> chunkify 64 |> List.map bitstring in
     let gs = gensym () in
     [iinit (CT_bits true) gs (first_chunk, CT_bits64 (len mod 64, true))]
     @ List.map (fun chunk -> ifuncall (CL_id gs)
                                       (mk_id "append_64")
                                       [(F_id gs, CT_bits true); (chunk, CT_bits64 (64, true))]
                                       (CT_bits true)) chunks,
     (F_id gs, CT_bits true),
     [iclear (CT_bits true) gs]

  (* If we have a bitvector value, that isn't a literal then we need to set bits individually. *)
  | AV_vector (avals, Typ_aux (Typ_app (id, [_; Typ_arg_aux (Typ_arg_order ord, _); Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id bit_id, _)), _)]), _))
       when string_of_id bit_id = "bit" && string_of_id id = "vector" && List.length avals <= 64 ->
     let len = List.length avals in
     let direction = match ord with
       | Ord_aux (Ord_inc, _) -> false
       | Ord_aux (Ord_dec, _) -> true
       | Ord_aux (Ord_var _, _) -> c_error "Polymorphic vector direction found"
     in
     let gs = gensym () in
     let ctyp = CT_bits64 (len, direction) in
     let mask i = V_bits (Util.list_init (63 - i) (fun _ -> Sail2_values.B0) @ [Sail2_values.B1] @ Util.list_init i (fun _ -> Sail2_values.B0)) in
     let aval_mask i aval =
       let setup, cval, cleanup = compile_aval ctx aval in
       match cval with
       | (F_lit (V_bit Sail2_values.B0), _) -> []
       | (F_lit (V_bit Sail2_values.B1), _) ->
          [icopy (CL_id gs) (F_op (F_id gs, "|", F_lit (mask i)), ctyp)]
       | _ ->
          setup @ [iif cval [icopy (CL_id gs) (F_op (F_id gs, "|", F_lit (mask i)), ctyp)] [] CT_unit] @ cleanup
     in
     [idecl ctyp gs;
      icopy (CL_id gs) (F_lit (V_bits (Util.list_init 64 (fun _ -> Sail2_values.B0))), ctyp)]
     @ List.concat (List.mapi aval_mask (List.rev avals)),
     (F_id gs, ctyp),
     []

  (* Compiling a vector literal that isn't a bitvector *)
  | AV_vector (avals, Typ_aux (Typ_app (id, [_; Typ_arg_aux (Typ_arg_order ord, _); Typ_arg_aux (Typ_arg_typ typ, _)]), _))
       when string_of_id id = "vector" ->
     let len = List.length avals in
     let direction = match ord with
       | Ord_aux (Ord_inc, _) -> false
       | Ord_aux (Ord_dec, _) -> true
       | Ord_aux (Ord_var _, _) -> c_error "Polymorphic vector direction found"
     in
     let vector_ctyp = CT_vector (direction, ctyp_of_typ ctx typ) in
     let gs = gensym () in
     let aval_set i aval =
       let setup, cval, cleanup = compile_aval ctx aval in
       setup
       @ [iextern (CL_id gs)
                  (mk_id "internal_vector_update")
                  [(F_id gs, vector_ctyp); (F_lit (V_int (Big_int.of_int i)), CT_int64); cval] vector_ctyp]
       @ cleanup
     in
     [idecl vector_ctyp gs;
      iextern (CL_id gs) (mk_id "internal_vector_init") [(F_lit (V_int (Big_int.of_int len)), CT_int64)] vector_ctyp]
     @ List.concat (List.mapi aval_set (if direction then List.rev avals else avals)),
     (F_id gs, vector_ctyp),
     [iclear vector_ctyp gs]

  | AV_vector _ as aval ->
     c_error ("Have AV_vector: " ^ Pretty_print_sail.to_string (pp_aval aval) ^ " which is not a vector type")

  | AV_list (avals, Typ_aux (typ, _)) ->
     let ctyp = match typ with
       | Typ_app (id, [Typ_arg_aux (Typ_arg_typ typ, _)]) when string_of_id id = "list" -> ctyp_of_typ ctx typ
       | _ -> c_error "Invalid list type"
     in
     let gs = gensym () in
     let mk_cons aval =
       let setup, cval, cleanup = compile_aval ctx aval in
       setup @ [ifuncall (CL_id gs) (mk_id ("cons#" ^ string_of_ctyp ctyp)) [cval; (F_id gs, CT_list ctyp)] (CT_list ctyp)] @ cleanup
     in
     [idecl (CT_list ctyp) gs]
     @ List.concat (List.map mk_cons (List.rev avals)),
     (F_id gs, CT_list ctyp),
     [iclear (CT_list ctyp) gs]

let compile_funcall l ctx id args typ =
  let setup = ref [] in
  let cleanup = ref [] in

  let quant, Typ_aux (fn_typ, _) =
    try Env.get_val_spec id ctx.local_env
    with Type_error _ ->
      c_debug (lazy ("Falling back to global env for " ^ string_of_id id)); Env.get_val_spec id ctx.tc_env
  in
  let arg_typs, ret_typ = match fn_typ with
    | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
    | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
    | _ -> assert false
  in
  let ctx' = { ctx with local_env = add_typquant (id_loc id) quant ctx.local_env } in
  let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ in
  let final_ctyp = ctyp_of_typ ctx typ in

  let setup_arg ctyp aval =
    let arg_setup, cval, arg_cleanup = compile_aval ctx aval in
    setup := List.rev arg_setup @ !setup;
    cleanup := arg_cleanup @ !cleanup;
    let have_ctyp = cval_ctyp cval in
    if ctyp_equal ctyp have_ctyp then
      cval
    else if is_stack_ctyp have_ctyp && not (is_stack_ctyp ctyp) then
      let gs = gensym () in
      setup := iinit ctyp gs cval :: !setup;
      cleanup := iclear ctyp gs :: !cleanup;
      (F_id gs, ctyp)
    else if not (is_stack_ctyp have_ctyp) && is_stack_ctyp ctyp then
      (* This is inefficient. FIXME: Remove id restriction on iconvert
         instruction. Fortunatly only happens when flow typing makes a
         length-polymorphic bitvector monomorphic. *)
      let gs1 = gensym () in
      let gs2 = gensym () in
      setup := idecl have_ctyp gs1 :: !setup;
      setup := icopy (CL_id gs1) cval :: !setup;
      setup := idecl ctyp gs2 :: !setup;
      setup := iconvert (CL_id gs2) ctyp gs1 have_ctyp :: !setup;
      cleanup := iclear have_ctyp gs1 :: !cleanup;
      (F_id gs2, ctyp)
    else
      c_error ~loc:l
        (Printf.sprintf "Failure when setting up function %s arguments: %s and %s." (string_of_id id) (string_of_ctyp have_ctyp) (string_of_ctyp ctyp))
  in

  assert (List.length arg_ctyps = List.length args);

  let sargs = List.map2 setup_arg arg_ctyps args in

  let call =
    if ctyp_equal final_ctyp ret_ctyp then
      fun ret -> ifuncall ret id sargs ret_ctyp
    else if not (is_stack_ctyp ret_ctyp) && is_stack_ctyp final_ctyp then
      let gs = gensym () in
      setup := idecl ret_ctyp gs :: !setup;
      setup := ifuncall (CL_id gs) id sargs ret_ctyp :: !setup;
      cleanup := iclear ret_ctyp gs :: !cleanup;
      fun ret -> iconvert ret final_ctyp gs ret_ctyp
    else if is_stack_ctyp ret_ctyp && not (is_stack_ctyp final_ctyp) then
      let gs = gensym () in
      setup := idecl ret_ctyp gs :: !setup;
      setup := ifuncall (CL_id gs) id sargs ret_ctyp :: !setup;
      fun ret -> iconvert ret final_ctyp gs ret_ctyp
    else
      c_error (Printf.sprintf "Funcall call type mismatch between %s and %s" (string_of_ctyp ret_ctyp) (string_of_ctyp final_ctyp))
  in

  (List.rev !setup, final_ctyp, call, !cleanup)

let rec compile_match ctx (AP_aux (apat_aux, env, l)) cval case_label =
  let ctx = { ctx with local_env = env } in
  match apat_aux, cval with
  | AP_id (pid, _), (frag, ctyp) when Env.is_union_constructor pid ctx.tc_env ->
     [ijump (F_op (F_field (frag, "kind"), "!=", F_lit (V_ctor_kind (string_of_id pid))), CT_bool) case_label],
     []
  | AP_global (pid, typ), (frag, ctyp) ->
     let global_ctyp = ctyp_of_typ ctx typ in
     if ctyp_equal global_ctyp ctyp then
       [icopy (CL_id pid) cval], []
     else
       begin match frag with
       | F_id id ->
          [iconvert (CL_id pid) global_ctyp id ctyp], []
       | _ -> c_error "Cannot compile global letbinding"
       end
  | AP_id (pid, _), (frag, ctyp) when is_ct_enum ctyp ->
     begin match Env.lookup_id pid ctx.tc_env with
     | Unbound -> [idecl ctyp pid; icopy (CL_id pid) (frag, ctyp)], []
     | _ -> [ijump (F_op (F_id pid, "!=", frag), CT_bool) case_label], []
     end
  | AP_id (pid, typ), _ ->
     let ctyp = cval_ctyp cval in
     let id_ctyp = ctyp_of_typ ctx typ in
     if ctyp_equal id_ctyp ctyp then
       [idecl ctyp pid; icopy (CL_id pid) cval], [iclear id_ctyp pid]
     else
       let gs = gensym () in
       [idecl id_ctyp pid; idecl ctyp gs; icopy (CL_id gs) cval; iconvert (CL_id pid) id_ctyp gs ctyp; iclear ctyp gs], [iclear id_ctyp pid]
  | AP_tup apats, (frag, ctyp) ->
     begin
       let get_tup n ctyp = (F_field (frag, "ztup" ^ string_of_int n), ctyp) in
       let fold (instrs, cleanup, n) apat ctyp =
         let instrs', cleanup' = compile_match ctx apat (get_tup n ctyp) case_label in
         instrs @ instrs', cleanup' @ cleanup, n + 1
       in
       match ctyp with
       | CT_tup ctyps ->
          let instrs, cleanup, _ = List.fold_left2 fold ([], [], 0) apats ctyps in
          instrs, cleanup
       | _ -> failwith ("AP_tup with ctyp " ^ string_of_ctyp ctyp)
     end
  | AP_app (ctor, apat), (frag, ctyp) ->
     begin match ctyp with
     | CT_variant (_, ctors) ->
        let ctor_c_id = string_of_id ctor in
        let ctor_ctyp = Bindings.find ctor (ctor_bindings ctors) in
        let instrs, cleanup = compile_match ctx apat ((F_field (frag, Util.zencode_string ctor_c_id), ctor_ctyp)) case_label in
        [ijump (F_op (F_field (frag, "kind"), "!=", F_lit (V_ctor_kind ctor_c_id)), CT_bool) case_label]
        @ instrs,
        cleanup
     | _ -> failwith "AP_app constructor with non-variant type"
     end
  | AP_wild, _ -> [], []

  | AP_cons (hd_apat, tl_apat), (frag, CT_list ctyp) ->
     let hd_setup, hd_cleanup = compile_match ctx hd_apat (F_field (F_unary ("*", frag), "hd"), ctyp) case_label in
     let tl_setup, tl_cleanup = compile_match ctx tl_apat (F_field (F_unary ("*", frag), "tl"), CT_list ctyp) case_label in
     [ijump (F_op (frag, "==", F_lit V_null), CT_bool) case_label] @ hd_setup @ tl_setup, tl_cleanup @ hd_cleanup
  | AP_cons _, (_, _) -> c_error "Tried to pattern match cons on non list type"

  | AP_nil, (frag, _) -> [ijump (F_op (frag, "!=", F_lit V_null), CT_bool) case_label], []

let unit_fragment = (F_lit V_unit, CT_unit)

(** GLOBAL: label_counter is used to make sure all labels have unique
   names. Like gensym_counter it should be safe to reset between
   top-level definitions. **)
let label_counter = ref 0

let label str =
  let str = str ^ string_of_int !label_counter in
  incr label_counter;
  str

let rec compile_aexp ctx (AE_aux (aexp_aux, env, l)) =
  let ctx = { ctx with local_env = env } in
  match aexp_aux with
  | AE_let (id, _, binding, body, typ) ->
     let setup, ctyp, call, cleanup = compile_aexp ctx binding in
     let letb_setup, letb_cleanup =
       [idecl ctyp id; iblock (setup @ [call (CL_id id)] @ cleanup)], [iclear ctyp id]
     in
     let setup, ctyp, call, cleanup = compile_aexp ctx body in
     let body_ctyp = ctyp_of_typ ctx typ in
     if ctyp_equal body_ctyp ctyp then
       letb_setup @ setup, ctyp, call, cleanup @ letb_cleanup
     else
       begin
         prerr_endline ("Mismatch: " ^ string_of_ctyp body_ctyp ^ " and " ^ string_of_ctyp ctyp);
         let gs = gensym () in
         letb_setup @ setup @ [idecl ctyp gs; call (CL_id gs)],
         body_ctyp,
         (fun clexp -> iconvert clexp body_ctyp gs ctyp),
         [iclear ctyp gs] @ cleanup @ letb_cleanup
       end

  | AE_app (id, vs, typ) ->
     compile_funcall l ctx id vs typ

  | AE_val aval ->
     let setup, cval, cleanup = compile_aval ctx aval in
     setup, cval_ctyp cval, (fun clexp -> icopy clexp cval), cleanup

  (* Compile case statements *)
  | AE_case (aval, cases, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let aval_setup, cval, aval_cleanup = compile_aval ctx aval in
     let case_return_id = gensym () in
     let finish_match_label = label "finish_match_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _, _)
         | AE_aux (AE_val (AV_C_fragment (F_lit (V_bool true), _)), _, _) -> true
         | _ -> false
       in
       let case_label = label "case_" in
       c_debug (lazy ("Compiling match"));
       let destructure, destructure_cleanup = compile_match ctx apat cval case_label in
       c_debug (lazy ("Compiled match"));
       let guard_setup, _, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
       let gs = gensym () in
       let case_instrs =
         destructure @ [icomment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [idecl CT_bool gs; guard_call (CL_id gs)] @ guard_cleanup
              @ [iif (F_unary ("!", F_id gs), CT_bool) (destructure_cleanup @ [igoto case_label]) [] CT_unit]
              @ [icomment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id case_return_id)] @ body_cleanup @ destructure_cleanup
         @ [igoto finish_match_label]
       in
       [iblock case_instrs; ilabel case_label]
     in
     [icomment "begin match"]
     @ aval_setup @ [idecl ctyp case_return_id]
     @ List.concat (List.map compile_case cases)
     @ [imatch_failure ()]
     @ [ilabel finish_match_label],
     ctyp,
     (fun clexp -> icopy clexp (F_id case_return_id, ctyp)),
     (if is_stack_ctyp ctyp then [] else [iclear ctyp case_return_id])
     @ aval_cleanup
     @ [icomment "end match"]

  (* Compile try statement *)
  | AE_try (aexp, cases, typ) ->
     let aexp_setup, ctyp, aexp_call, aexp_cleanup = compile_aexp ctx aexp in
     let try_return_id = gensym () in
     let handled_exception_label = label "handled_exception_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _, _)
         | AE_aux (AE_val (AV_C_fragment (F_lit (V_bool true), _)), _, _) -> true
         | _ -> false
       in
       let try_label = label "try_" in
       let exn_cval = (F_current_exception, ctyp_of_typ ctx (mk_typ (Typ_id (mk_id "exception")))) in
       let destructure, destructure_cleanup = compile_match ctx apat exn_cval try_label in
       let guard_setup, _, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
       let gs = gensym () in
       let case_instrs =
         destructure @ [icomment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [idecl CT_bool gs; guard_call (CL_id gs)] @ guard_cleanup
              @ [ijump (F_unary ("!", F_id gs), CT_bool) try_label]
              @ [icomment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id try_return_id)] @ body_cleanup @ destructure_cleanup
         @ [igoto handled_exception_label]
       in
       [iblock case_instrs; ilabel try_label]
     in
     assert (ctyp_equal ctyp (ctyp_of_typ ctx typ));
     [icomment "begin try catch";
      idecl ctyp try_return_id;
      itry_block (aexp_setup @ [aexp_call (CL_id try_return_id)] @ aexp_cleanup);
      ijump (F_unary ("!", F_have_exception), CT_bool) handled_exception_label]
     @ List.concat (List.map compile_case cases)
     @ [imatch_failure ();
        ilabel handled_exception_label;
        icopy CL_have_exception (F_lit (V_bool false), CT_bool)],
     ctyp,
     (fun clexp -> icopy clexp (F_id try_return_id, ctyp)),
     []

  | AE_if (aval, then_aexp, else_aexp, if_typ) ->
     let if_ctyp = ctyp_of_typ ctx if_typ in
     let compile_branch aexp =
       let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
       if ctyp_equal if_ctyp ctyp then
         fun clexp -> setup @ [call clexp] @ cleanup
       else
         fun clexp ->
         let gs = gensym () in
         setup
         @ [idecl ctyp gs;
            call (CL_id gs);
            iconvert clexp if_ctyp gs ctyp;
            iclear ctyp gs]
         @ cleanup
     in
     let setup, cval, cleanup = compile_aval ctx aval in
     setup,
     if_ctyp,
     (fun clexp -> iif cval
                       (compile_branch then_aexp clexp)
                       (compile_branch else_aexp clexp)
                       if_ctyp),
     cleanup

  (* FIXME: AE_record_update could be AV_record_update - would reduce some copying. *)
  | AE_record_update (aval, fields, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let gs = gensym () in
     let compile_fields (id, aval) =
       let field_setup, cval, field_cleanup = compile_aval ctx aval in
       field_setup
       @ [icopy (CL_field (gs, string_of_id id)) cval]
       @ field_cleanup
     in
     let setup, cval, cleanup = compile_aval ctx aval in
     [idecl ctyp gs]
     @ setup
     @ [icopy (CL_id gs) cval]
     @ cleanup
     @ List.concat (List.map compile_fields (Bindings.bindings fields)),
     ctyp,
     (fun clexp -> icopy clexp (F_id gs, ctyp)),
     [iclear ctyp gs]

  | AE_short_circuit (SC_and, aval, aexp) ->
     let left_setup, cval, left_cleanup = compile_aval ctx aval in
     let right_setup, _, call, right_cleanup = compile_aexp ctx aexp in
     let gs = gensym () in
     left_setup
     @ [ idecl CT_bool gs;
         iif cval (right_setup @ [call (CL_id gs)] @ right_cleanup) [icopy (CL_id gs) (F_lit (V_bool false), CT_bool)] CT_bool ]
     @ left_cleanup,
     CT_bool,
     (fun clexp -> icopy clexp (F_id gs, CT_bool)),
     []
  | AE_short_circuit (SC_or, aval, aexp) ->
     let left_setup, cval, left_cleanup = compile_aval ctx aval in
     let right_setup, _, call, right_cleanup = compile_aexp ctx aexp in
     let gs = gensym () in
     left_setup
     @ [ idecl CT_bool gs;
         iif cval [icopy (CL_id gs) (F_lit (V_bool true), CT_bool)] (right_setup @ [call (CL_id gs)] @ right_cleanup) CT_bool ]
     @ left_cleanup,
     CT_bool,
     (fun clexp -> icopy clexp (F_id gs, CT_bool)),
     []

  (* This is a faster assignment rule for updating fields of a
     struct. Turned on by !optimize_struct_updates. *)
  | AE_assign (id, assign_typ, AE_aux (AE_record_update (AV_id (rid, _), fields, typ), _, _))
       when Id.compare id rid = 0 && !optimize_struct_updates ->
     c_debug (lazy ("Optimizing struct update"));
     let compile_fields (field_id, aval) =
       let field_setup, cval, field_cleanup = compile_aval ctx aval in
       field_setup
       @ [icopy (CL_field (id, string_of_id field_id)) cval]
       @ field_cleanup
     in
     List.concat (List.map compile_fields (Bindings.bindings fields)),
     CT_unit,
     (fun clexp -> icopy clexp unit_fragment),
     []

  | AE_assign (id, assign_typ, aexp) ->
     (* assign_ctyp is the type of the C variable we are assigning to,
        ctyp is the type of the C expression being assigned. These may
        be different. *)
     let pointer_assign ctyp1 ctyp2 =
       match ctyp1 with
       | CT_ref ctyp1 when ctyp_equal ctyp1 ctyp2 -> true
       | CT_ref ctyp1 -> c_error ~loc:l "Incompatible type in pointer assignment"
       | _ -> false
     in
     let assign_ctyp = ctyp_of_typ ctx assign_typ in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     let comment = "assign " ^ string_of_ctyp assign_ctyp ^ " := " ^ string_of_ctyp ctyp in
     if ctyp_equal assign_ctyp ctyp then
       setup @ [call (CL_id id)], CT_unit, (fun clexp -> icopy clexp unit_fragment), cleanup
     else if pointer_assign assign_ctyp ctyp then
       setup @ [call (CL_addr id)], CT_unit, (fun clexp -> icopy clexp unit_fragment), cleanup
     else
       let gs = gensym () in
       setup @ [ icomment comment;
                 idecl ctyp gs;
                 call (CL_id gs);
                 iconvert (CL_id id) assign_ctyp gs ctyp;
                 iclear ctyp gs
               ],
       CT_unit,
       (fun clexp -> icopy clexp unit_fragment),
       cleanup

  | AE_block (aexps, aexp, _) ->
     let block = compile_block ctx aexps in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     block @ setup, ctyp, call, cleanup

  | AE_loop (While, cond, body) ->
     let loop_start_label = label "while_" in
     let loop_end_label = label "wend_" in
     let cond_setup, _, cond_call, cond_cleanup = compile_aexp ctx cond in
     let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
     let gs = gensym () in
     let unit_gs = gensym () in
     let loop_test = (F_unary ("!", F_id gs), CT_bool) in
     [idecl CT_bool gs; idecl CT_unit unit_gs]
     @ [ilabel loop_start_label]
     @ [iblock (cond_setup
                @ [cond_call (CL_id gs)]
                @ cond_cleanup
                @ [ijump loop_test loop_end_label]
                @ body_setup
                @ [body_call (CL_id unit_gs)]
                @ body_cleanup
                @ [igoto loop_start_label])]
     @ [ilabel loop_end_label],
     CT_unit,
     (fun clexp -> icopy clexp unit_fragment),
     []

  | AE_loop (Until, cond, body) ->
     let loop_start_label = label "repeat_" in
     let loop_end_label = label "until_" in
     let cond_setup, _, cond_call, cond_cleanup = compile_aexp ctx cond in
     let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
     let gs = gensym () in
     let unit_gs = gensym () in
     let loop_test = (F_id gs, CT_bool) in
     [idecl CT_bool gs; idecl CT_unit unit_gs]
     @ [ilabel loop_start_label]
     @ [iblock (body_setup
                @ [body_call (CL_id unit_gs)]
                @ body_cleanup
                @ cond_setup
                @ [cond_call (CL_id gs)]
                @ cond_cleanup
                @ [ijump loop_test loop_end_label]
                @ [igoto loop_start_label])]
     @ [ilabel loop_end_label],
     CT_unit,
     (fun clexp -> icopy clexp unit_fragment),
     []

  | AE_cast (aexp, typ) -> compile_aexp ctx aexp

  | AE_return (aval, typ) ->
     let fn_return_ctyp = match Env.get_ret_typ env with
       | Some typ -> ctyp_of_typ ctx typ
       | None -> c_error ~loc:l "No function return type found when compiling return statement"
     in
     (* Cleanup info will be re-added by fix_early_return *)
     let return_setup, cval, _ = compile_aval ctx aval in
     let creturn =
       if ctyp_equal fn_return_ctyp (cval_ctyp cval) then
         [ireturn cval]
       else if is_stack_ctyp (cval_ctyp cval) && not (is_stack_ctyp fn_return_ctyp) then
         let gs1 = gensym () in
         let gs2 = gensym () in
         [idecl (cval_ctyp cval) gs1;
          icopy (CL_id gs1) cval;
          idecl fn_return_ctyp gs2;
          iconvert (CL_id gs2) fn_return_ctyp gs1 (cval_ctyp cval);
          ireturn (F_id gs2, fn_return_ctyp)]
       else
         c_error ~loc:l "Can only do return type conversion from stack to heap"
     in
     return_setup @ creturn,
     ctyp_of_typ ctx typ,
     (fun clexp -> icomment "unreachable after return"),
     []

  | AE_throw (aval, typ) ->
     (* Cleanup info will be handled by fix_exceptions *)
     let throw_setup, cval, _ = compile_aval ctx aval in
     throw_setup @ [ithrow cval],
     ctyp_of_typ ctx typ,
     (fun clexp -> icomment "unreachable after throw"),
     []

  | AE_field (aval, id, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let setup, cval, cleanup = compile_aval ctx aval in
     setup,
     ctyp,
     (fun clexp -> icopy clexp (F_field (fst cval, Util.zencode_string (string_of_id id)), ctyp)),
     cleanup

  | AE_for (loop_var, loop_from, loop_to, loop_step, Ord_aux (ord, _), body) ->
     (* This is a bit of a hack, we force loop_var to be CT_int64 by
        forcing it's type to be a known nexp that will map to
        CT_int64. *)
     let make_small _ _ = function
       | AV_id (id, Local (Immutable, typ)) when Id.compare id loop_var = 0 -> AV_id (id, Local (Immutable, atom_typ (nint 0)))
       | aval -> aval
     in
     let body = map_aval make_small body in

     let is_inc = match ord with
       | Ord_inc -> true
       | Ord_dec -> false
       | Ord_var _ -> c_error "Polymorphic loop direction in C backend"
     in

     (* Loop variables *)
     let from_setup, from_ctyp, from_call, from_cleanup = compile_aexp ctx loop_from in
     let from_gs = gensym () in
     let to_setup, to_ctyp, to_call, to_cleanup = compile_aexp ctx loop_to in
     let to_gs = gensym () in
     let step_setup, step_ctyp, step_call, step_cleanup = compile_aexp ctx loop_step in
     let step_gs = gensym () in
     let variable_init gs setup ctyp call cleanup =
       [idecl CT_int64 gs;
        if is_stack_ctyp ctyp then
          iblock (setup @ [call (CL_id gs)] @ cleanup)
        else
          let gs' = gensym () in
          iblock (setup
                  @ [idecl ctyp gs'; call (CL_id gs'); iconvert (CL_id gs) CT_int64 gs' ctyp; iclear ctyp gs']
                  @ cleanup)]
     in

     let loop_start_label = label "for_start_" in
     let loop_end_label = label "for_end_" in
     let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
     let body_gs = gensym () in

     variable_init from_gs from_setup from_ctyp from_call from_cleanup
     @ variable_init to_gs to_setup to_ctyp to_call to_cleanup
     @ variable_init step_gs step_setup step_ctyp step_call step_cleanup
     @ [iblock ([idecl CT_int64 loop_var;
                 icopy (CL_id loop_var) (F_id from_gs, CT_int64);
                 idecl CT_unit body_gs;
                 iblock ([ilabel loop_start_label]
                         @ [ijump (F_op (F_id loop_var, (if is_inc then ">" else "<"), F_id to_gs), CT_bool) loop_end_label]
                         @ body_setup
                         @ [body_call (CL_id body_gs)]
                         @ body_cleanup
                         @ [icopy (CL_id loop_var) (F_op (F_id loop_var, (if is_inc then "+" else "-"), F_id step_gs), CT_int64)]
                         @ [igoto loop_start_label]);
                 ilabel loop_end_label])],
     CT_unit,
     (fun clexp -> icopy clexp unit_fragment),
     []

(*
  | aexp -> failwith ("Cannot compile ANF expression: " ^ Pretty_print_sail.to_string (pp_aexp aexp))
 *)

and compile_block ctx = function
  | [] -> []
  | exp :: exps ->
     let setup, _, call, cleanup = compile_aexp ctx exp in
     let rest = compile_block ctx exps in
     let gs = gensym () in
     iblock (setup @ [idecl CT_unit gs; call (CL_id gs)] @ cleanup) :: rest

(** Compile a sail type definition into a IR one. Most of the
   actual work of translating the typedefs into C is done by the code
   generator, as it's easy to keep track of structs, tuples and unions
   in their sail form at this level, and leave the fiddly details of
   how they get mapped to C in the next stage. This function also adds
   details of the types it compiles to the context, ctx, which is why
   it returns a ctypdef * ctx pair. **)
let compile_type_def ctx (TD_aux (type_def, _)) =
  match type_def with
  | TD_enum (id, _, ids, _) ->
     CTD_enum (id, ids),
     { ctx with enums = Bindings.add id (IdSet.of_list ids) ctx.enums }

  | TD_record (id, _, _, ctors, _) ->
     let ctors = List.fold_left (fun ctors (typ, id) -> Bindings.add id (ctyp_of_typ ctx typ) ctors) Bindings.empty ctors in
     CTD_struct (id, Bindings.bindings ctors),
     { ctx with records = Bindings.add id ctors ctx.records }

  | TD_variant (id, _, _, tus, _) ->
     let compile_tu = function
       | Tu_aux (Tu_ty_id (Typ_aux (Typ_fn (typ, _, _), _), id), _) -> ctyp_of_typ ctx typ, id
       | Tu_aux (Tu_ty_id (typ, id), _) -> ctyp_of_typ ctx typ, id
     in
     let ctus = List.fold_left (fun ctus (ctyp, id) -> Bindings.add id ctyp ctus) Bindings.empty (List.map compile_tu tus) in
     CTD_variant (id, Bindings.bindings ctus),
     { ctx with variants = Bindings.add id ctus ctx.variants }

  (* Will be re-written before here, see bitfield.ml *)
  | TD_bitfield _ -> failwith "Cannot compile TD_bitfield"
  (* All type abbreviations are filtered out in compile_def  *)
  | TD_abbrev _ -> assert false

let instr_split_at f =
  let rec instr_split_at' f before = function
    | [] -> (List.rev before, [])
    | instr :: instrs when f instr -> (List.rev before, instr :: instrs)
    | instr :: instrs -> instr_split_at' f (instr :: before) instrs
  in
  instr_split_at' f []

let generate_cleanup instrs =
  let generate_cleanup' (I_aux (instr, _)) =
    match instr with
    | I_init (ctyp, id, cval) when not (is_stack_ctyp ctyp) -> [(id, iclear ctyp id)]
    | I_decl (ctyp, id) when not (is_stack_ctyp ctyp) -> [(id, iclear ctyp id)]
    | instr -> []
  in
  let is_clear ids = function
    | I_aux (I_clear (_, id), _) -> IdSet.add id ids
    | _ -> ids
  in
  let cleaned = List.fold_left is_clear IdSet.empty instrs in
  instrs
  |> List.map generate_cleanup'
  |> List.concat
  |> List.filter (fun (id, _) -> not (IdSet.mem id cleaned))
  |> List.map snd

(** Functions that have heap-allocated return types are implemented by
   passing a pointer a location where the return value should be
   stored. The ANF -> Sail IR pass for expressions simply outputs an
   I_return instruction for any return value, so this function walks
   over the IR ast for expressions and modifies the return statements
   into code that sets that pointer, as well as adds extra control
   flow to cleanup heap-allocated variables correctly when a function
   terminates early. See the generate_cleanup function for how this is
   done. *)
let fix_early_return ret ctx instrs =
  let end_function_label = label "end_function_" in
  let is_return_recur (I_aux (instr, _)) =
    match instr with
    | I_return _ | I_if _ | I_block _ -> true
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
    | before, I_aux (I_return cval, _) :: after ->
       let cleanup_label = label "cleanup_" in
       let end_cleanup_label = label "end_cleanup_" in
       before
       @ [icopy ret cval;
          igoto cleanup_label]
       (* This is probably dead code until cleanup_label, but how can we be sure there are no jumps into it? *)
       @ rewrite_return (historic @ before) after
       @ [igoto end_cleanup_label]
       @ [ilabel cleanup_label]
       @ generate_cleanup (historic @ before)
       @ [igoto end_function_label]
       @ [ilabel end_cleanup_label]
    | _, _ -> assert false
  in
  rewrite_return [] instrs
  @ [ilabel end_function_label]

(* This is like fix_early_return, but for stack allocated returns. *)
let fix_early_stack_return ctx instrs =
  let is_return_recur (I_aux (instr, _)) =
    match instr with
    | I_return _ | I_if _ | I_block _ -> true
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
    | before, (I_aux (I_return cval, _) as ret) :: after ->
       before
       @ [icomment "early return cleanup"]
       @ generate_cleanup (historic @ before)
       @ [ret]
       (* There could be jumps into here *)
       @ rewrite_return (historic @ before) after
    | _, _ -> assert false
  in
  rewrite_return [] instrs

let fix_exception_block ctx instrs =
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
    | before, I_aux (I_throw cval, _) :: after ->
       before
       @ [icopy CL_current_exception cval;
          icopy CL_have_exception (F_lit (V_bool true), CT_bool)]
       @ generate_cleanup (historic @ before)
       @ [igoto end_block_label]
       @ rewrite_exception (historic @ before) after
    | before, (I_aux (I_funcall (x, _, f, args, ctyp), _) as funcall) :: after ->
       let effects = match Env.get_val_spec f ctx.tc_env with
         | _, Typ_aux (Typ_fn (_, _, effects), _) -> effects
         | exception (Type_error _) -> no_effect (* nullary union constructor, so no val spec *)
         | _ -> assert false (* valspec must have function type *)
       in
       if has_effect effects BE_escape then
         before
         @ [funcall;
            iif (F_have_exception, CT_bool) (generate_cleanup (historic @ before) @ [igoto end_block_label]) [] CT_unit]
         @ rewrite_exception (historic @ before) after
       else
         before @ funcall :: rewrite_exception (historic @ before) after
    | _, _ -> assert false (* unreachable *)
  in
  rewrite_exception [] instrs
  @ [ilabel end_block_label]

let rec map_try_block f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_reset _ | I_init _ | I_reinit _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, List.map (map_try_block f) instrs1, List.map (map_try_block f) instrs2, ctyp)
    | I_funcall _ | I_convert _ | I_copy _ | I_clear _ | I_throw _ | I_return _ -> instr
    | I_block instrs -> I_block (List.map (map_try_block f) instrs)
    | I_try_block instrs -> I_try_block (f (List.map (map_try_block f) instrs))
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_jump _ | I_match_failure -> instr
  in
  I_aux (instr, aux)

let fix_exception ctx instrs =
  let instrs = List.map (map_try_block (fix_exception_block ctx)) instrs in
  fix_exception_block ctx instrs

let rec arg_pats ctx (Typ_aux (arg_typ_aux, _) as arg_typ) (P_aux (p_aux, (l, _)) as pat) =
  match p_aux, arg_typ_aux with
  | P_typ (_, pat), _ -> arg_pats ctx arg_typ pat
  | P_tup pats, Typ_tup arg_typs when List.length pats = List.length arg_typs ->
     List.map2 (fun pat arg_typ -> pat, ctyp_of_typ ctx arg_typ) pats arg_typs
  | P_wild, Typ_tup arg_typs -> List.map (fun arg_typ -> pat, ctyp_of_typ ctx arg_typ) arg_typs
  | _, _ -> [(pat, ctyp_of_typ ctx arg_typ)]

let rec compile_arg_pat ctx label (P_aux (p_aux, (l, _)) as pat, ctyp) =
  match p_aux with
  | P_id id -> (id, ([], []))
  | P_wild -> let gs = gensym () in (gs, ([], []))
  | P_tup [] | P_lit (L_aux (L_unit, _)) -> let gs = gensym () in (gs, ([], []))
  | P_var (pat, _) -> compile_arg_pat ctx label (pat, ctyp)
  | P_typ (_, pat) -> compile_arg_pat ctx label (pat, ctyp)
  | _ ->
     let apat = anf_pat pat in
     let gs = gensym () in
     let destructure, cleanup = compile_match ctx apat (F_id gs, ctyp) label in
     (gs, (destructure, cleanup))

let combine_destructure_cleanup xs = List.concat (List.map fst xs), List.concat (List.rev (List.map snd xs))

let fix_destructure fail_label = function
  | ([], cleanup) -> ([], cleanup)
  | destructure, cleanup ->
     let body_label = label "fundef_body_" in
     (destructure @ [igoto body_label; ilabel fail_label; imatch_failure (); ilabel body_label], cleanup)

let letdef_count = ref 0

(** Compile a Sail toplevel definition into an IR definition **)
let rec compile_def ctx = function
  | DEF_reg_dec (DEC_aux (DEC_reg (typ, id), _)) ->
     [CDEF_reg_dec (id, ctyp_of_typ ctx typ, [])], ctx
  | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), _)) ->
     let aexp = map_functions (analyze_primop ctx) (c_literals ctx (no_shadow IdSet.empty (anf exp))) in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     let instrs = setup @ [call (CL_id id)] @ cleanup in
     [CDEF_reg_dec (id, ctyp_of_typ ctx typ, instrs)], ctx

  | DEF_spec (VS_aux (VS_val_spec (_, id, _, _), _)) ->
     c_debug (lazy "Compiling VS");
     let quant, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let arg_typs, ret_typ = match fn_typ with
       | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
       | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
       | _ -> assert false
     in
     let ctx' = { ctx with local_env = add_typquant (id_loc id) quant ctx.local_env } in
     let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ in
     [CDEF_spec (id, arg_ctyps, ret_ctyp)], ctx

  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (pat, exp), _)), _)]), _)) ->
     c_debug (lazy ("Compiling function " ^ string_of_id id));
     let aexp = map_functions (analyze_primop ctx) (c_literals ctx (no_shadow (pat_ids pat) (anf exp))) in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     c_debug (lazy "Compiled aexp");
     let fundef_label = label "fundef_fail_" in
     let _, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let arg_typ, ret_typ = match fn_typ with
       | Typ_fn (arg_typ, ret_typ, _) -> arg_typ, ret_typ
       | _ -> assert false
     in
     let compiled_args = List.map (compile_arg_pat ctx fundef_label) (arg_pats ctx arg_typ pat) in
     let gs = gensym () in
     let destructure, destructure_cleanup =
       compiled_args |> List.map snd |> combine_destructure_cleanup |> fix_destructure fundef_label
     in
     if is_stack_ctyp ctyp then
       let instrs = destructure @ [idecl ctyp gs] @ setup @ [call (CL_id gs)] @ cleanup @ destructure_cleanup @ [ireturn (F_id gs, ctyp)] in
       let instrs = fix_early_stack_return ctx instrs in
       let instrs = fix_exception ctx instrs in
       [CDEF_fundef (id, None, List.map fst compiled_args, instrs)], ctx
     else
       let instrs = destructure @ setup @ [call (CL_addr gs)] @ cleanup @ destructure_cleanup in
       let instrs = fix_early_return (CL_addr gs) ctx instrs in
       let instrs = fix_exception ctx instrs in
       [CDEF_fundef (id, Some gs, List.map fst compiled_args, instrs)], ctx

  | DEF_fundef (FD_aux (FD_function (_, _, _, []), (l, _))) ->
     c_error ~loc:l "Encountered function with no clauses"
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), (l, _))) ->
     c_error ~loc:l "Encountered function with multiple clauses"

  (* All abbreviations should expanded by the typechecker, so we don't
     need to translate type abbreviations into C typedefs. *)
  | DEF_type (TD_aux (TD_abbrev _, _)) -> [], ctx

  | DEF_type type_def ->
     let tdef, ctx = compile_type_def ctx type_def in
     [CDEF_type tdef], ctx

  | DEF_val (LB_aux (LB_val (pat, exp), _)) ->
     c_debug (lazy ("Compiling letbind " ^ string_of_pat pat));
     let aexp = map_functions (analyze_primop ctx) (c_literals ctx (no_shadow IdSet.empty (anf exp))) in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     let apat = anf_pat ~global:true pat in
     let gs = gensym () in
     let end_label = label "let_end_" in
     let destructure, destructure_cleanup = compile_match ctx apat (F_id gs, ctyp) end_label in
     let gs_setup, gs_cleanup =
         [idecl ctyp gs], [iclear ctyp gs]
     in
     let bindings = List.map (fun (id, typ) -> id, ctyp_of_typ ctx typ) (apat_globals apat) in
     let n = !letdef_count in
     incr letdef_count;
     let instrs =
       [icomment "gs_setup"] @ gs_setup @ [icomment "setup"] @ setup
       @ [icomment "call"]
       @ [call (CL_id gs)]
       @ [icomment "cleanup"]
       @ cleanup
       @ [icomment "destructure"]
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

  | DEF_internal_mutrec fundefs ->
     let defs = List.map (fun fdef -> DEF_fundef fdef) fundefs in
     List.fold_left (fun (cdefs, ctx) def -> let cdefs', ctx = compile_def ctx def in (cdefs @ cdefs', ctx)) ([], ctx) defs

  | def ->
     c_error ("Could not compile:\n" ^ Pretty_print_sail.to_string (Pretty_print_sail.doc_def def))

(** To keep things neat we use GCC's local labels extension to limit
   the scope of labels. We do this by iterating over all the blocks
   and adding a __label__ declaration with all the labels local to
   that block. The add_local_labels function is called by the code
   generator just before it outputs C.

   See https://gcc.gnu.org/onlinedocs/gcc/Local-Labels.html **)
let add_local_labels' instrs =
  let is_label (I_aux (instr, _)) =
    match instr with
    | I_label str -> [str]
    | _ -> []
  in
  let labels = List.concat (List.map is_label instrs) in
  let local_label_decl = iraw ("__label__ " ^ String.concat ", " labels ^ ";\n") in
  if labels = [] then
    instrs
  else
    local_label_decl :: instrs

let add_local_labels instrs =
  match map_instrs add_local_labels' (iblock instrs) with
  | I_aux (I_block instrs, _) -> instrs
  | _ -> assert false

(**************************************************************************)
(* 5. Optimizations                                                       *)
(**************************************************************************)

let clexp_rename from_id to_id =
  let rename id = if Id.compare id from_id = 0 then to_id else id in
  function
  | CL_id id -> CL_id (rename id)
  | CL_field (id, field) -> CL_field (rename id, field)
  | CL_addr id -> CL_addr (rename id)
  | CL_addr_field (id, field) -> CL_addr_field (rename id, field)
  | CL_current_exception -> CL_current_exception
  | CL_have_exception -> CL_have_exception

let rec instrs_rename from_id to_id =
  let rename id = if Id.compare id from_id = 0 then to_id else id in
  let crename = cval_rename from_id to_id in
  let irename instrs = instrs_rename from_id to_id instrs in
  let lrename = clexp_rename from_id to_id in
  function
  | (I_aux (I_decl (ctyp, new_id), _) :: _) as instrs when Id.compare from_id new_id = 0 -> instrs
  | I_aux (I_decl (ctyp, new_id), aux) :: instrs -> I_aux (I_decl (ctyp, new_id), aux) :: irename instrs
  | I_aux (I_reset (ctyp, id), aux) :: instrs -> I_aux (I_reset (ctyp, rename id), aux) :: irename instrs
  | I_aux (I_init (ctyp, id, cval), aux) :: instrs -> I_aux (I_init (ctyp, rename id, crename cval), aux) :: irename instrs
  | I_aux (I_reinit (ctyp, id, cval), aux) :: instrs -> I_aux (I_reinit (ctyp, rename id, crename cval), aux) :: irename instrs
  | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: instrs ->
     I_aux (I_if (crename cval, irename then_instrs, irename else_instrs, ctyp), aux) :: irename instrs
  | I_aux (I_jump (cval, label), aux) :: instrs -> I_aux (I_jump (crename cval, label), aux) :: irename instrs
  | I_aux (I_funcall (clexp, extern, id, cvals, ctyp), aux) :: instrs ->
     I_aux (I_funcall (lrename clexp, extern, rename id, List.map crename cvals, ctyp), aux) :: irename instrs
  | I_aux (I_copy (clexp, cval), aux) :: instrs -> I_aux (I_copy (lrename clexp, crename cval), aux) :: irename instrs
  | I_aux (I_convert (clexp, ctyp1, id, ctyp2), aux) :: instrs ->
     I_aux (I_convert (lrename clexp, ctyp1, rename id, ctyp2), aux) :: irename instrs
  | I_aux (I_clear (ctyp, id), aux) :: instrs -> I_aux (I_clear (ctyp, rename id), aux) :: irename instrs
  | I_aux (I_return cval, aux) :: instrs -> I_aux (I_return (crename cval), aux) :: irename instrs
  | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (irename block), aux) :: irename instrs
  | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (irename block), aux) :: irename instrs
  | I_aux (I_throw cval, aux) :: instrs -> I_aux (I_throw (crename cval), aux) :: irename instrs
  | (I_aux ((I_comment _ | I_raw _ | I_label _ | I_goto _ | I_match_failure), _) as instr) :: instrs -> instr :: irename instrs
  | [] -> []

let hoist_ctyp = function
  | CT_int | CT_bits _ | CT_struct _ -> true
  | _ -> false

let hoist_counter = ref 0
let hoist_id () =
  let id = mk_id ("gh#" ^ string_of_int !hoist_counter) in
  incr hoist_counter;
  id

let hoist_allocations ctx = function
  | CDEF_fundef (function_id, _, _, _) as cdef when IdSet.mem function_id ctx.recursive_functions ->
     c_debug (lazy (Printf.sprintf "skipping recursive function %s" (string_of_id function_id)));
     [cdef]

  | CDEF_fundef (function_id, heap_return, args, body) ->
     let decls = ref [] in
     let cleanups = ref [] in
     let rec hoist = function
       | I_aux (I_decl (ctyp, decl_id), annot) :: instrs when hoist_ctyp ctyp ->
          let hid = hoist_id () in
          decls := idecl ctyp hid :: !decls;
          cleanups := iclear ctyp hid :: !cleanups;
          let instrs = instrs_rename decl_id hid instrs in
          I_aux (I_reset (ctyp, hid), annot) :: hoist instrs

       | I_aux (I_init (ctyp, decl_id, cval), annot) :: instrs when hoist_ctyp ctyp ->
          let hid = hoist_id () in
          decls := idecl ctyp hid :: !decls;
          cleanups := iclear ctyp hid :: !cleanups;
          let instrs = instrs_rename decl_id hid instrs in
          I_aux (I_reinit (ctyp, hid, cval), annot) :: hoist instrs

       | I_aux (I_clear (ctyp, _), _) :: instrs when hoist_ctyp ctyp ->
          hoist instrs

       | I_aux (I_block block, annot) :: instrs ->
          I_aux (I_block (hoist block), annot) :: hoist instrs
       | I_aux (I_try_block block, annot) :: instrs ->
          I_aux (I_try_block (hoist block), annot) :: hoist instrs
       | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), annot) :: instrs ->
          I_aux (I_if (cval, hoist then_instrs, hoist else_instrs, ctyp), annot) :: hoist instrs

       | instr :: instrs -> instr :: hoist instrs
       | [] -> []
     in
     let body = hoist body in
     if !decls = [] then
       [CDEF_fundef (function_id, heap_return, args, body)]
     else
       [CDEF_startup (function_id, List.rev !decls);
        CDEF_fundef (function_id, heap_return, args, body);
        CDEF_finish (function_id, !cleanups)]

  | cdef -> [cdef]

let flat_counter = ref 0
let flat_id () =
  let id = mk_id ("local#" ^ string_of_int !flat_counter) in
  incr flat_counter;
  id

let flatten_instrs ctx =
  let rec flatten = function
    | I_aux (I_decl (ctyp, decl_id), aux) :: instrs ->
       let fid = flat_id () in
       I_aux (I_decl (ctyp, fid), aux) :: flatten (instrs_rename decl_id fid instrs)

    | I_aux ((I_block block | I_try_block block), _) :: instrs ->
       flatten block @ flatten instrs

    | I_aux (I_if (cval, then_instrs, else_instrs, _), _) :: instrs ->
       let then_label = label "then_" in
       let endif_label = label "endif_" in
       [ijump cval then_label]
       @ flatten else_instrs
       @ [igoto endif_label]
       @ [ilabel then_label]
       @ flatten then_instrs
       @ [ilabel endif_label]
       @ flatten instrs

    | I_aux (I_comment _, _) :: instrs -> flatten instrs

    | instr :: instrs -> instr :: flatten instrs
    | [] -> []
  in
  function
  | CDEF_fundef (function_id, heap_return, args, body) ->
     flat_counter := 0;
     [CDEF_fundef (function_id, heap_return, args, flatten body)]

  | CDEF_let (n, bindings, instrs) ->
    flat_counter := 0;
    [CDEF_let (n, bindings, flatten instrs)]

  | cdef -> [cdef]

(* When this optimization fires we know we have bytecode of the form

   recreate x : S; x = y; ...

   when this continues with x.A = a, x.B = b etc until y = x. Then
   provided there are no further references to x we can eliminate
   the variable x.

   Must be called after hoist_allocations, otherwise does nothing. *)
let fix_struct_updates ctx =
  (* FIXME need to check no remaining references *)
  let rec fix_updates struct_id id = function
    | I_aux (I_copy (CL_field (struct_id', field), cval), aux) :: instrs
         when Id.compare struct_id struct_id' = 0 ->
       Util.option_map (fun instrs -> I_aux (I_copy (CL_field (id, field), cval), aux) :: instrs) (fix_updates struct_id id instrs)
    | I_aux (I_copy (CL_id id', (F_id struct_id', ctyp)), aux) :: instrs
         when Id.compare struct_id struct_id' = 0 && Id.compare id id' = 0->
       Some instrs
    | _ -> None
  in
  let rec fix_updates_ret struct_id id = function
    | I_aux (I_copy (CL_field (struct_id', field), cval), aux) :: instrs
         when Id.compare struct_id struct_id' = 0 ->
       Util.option_map (fun instrs -> I_aux (I_copy (CL_addr_field (id, field), cval), aux) :: instrs) (fix_updates_ret struct_id id instrs)
    | I_aux (I_copy (CL_addr id', (F_id struct_id', ctyp)), aux) :: instrs
         when Id.compare struct_id struct_id' = 0 && Id.compare id id' = 0->
       Some instrs
    | _ -> None
  in
  let rec opt hr = function
    | (I_aux (I_reset (ctyp, struct_id), _) as instr1)
      :: (I_aux (I_copy (CL_id struct_id', (F_id id, ctyp')), _) as instr2)
      :: instrs
         when is_ct_struct ctyp && ctyp_equal ctyp ctyp' && Id.compare struct_id struct_id' = 0 ->
       prerr_endline ("Potential struct update " ^ string_of_id struct_id);
       begin match fix_updates struct_id id instrs with
       | None -> instr1 :: instr2 :: opt hr instrs
       | Some updated -> opt hr updated
       end

    | (I_aux (I_reset (ctyp, struct_id), _) as instr) :: instrs
         when is_ct_struct ctyp && Util.is_some hr ->
       let id = match hr with Some id -> id | None -> assert false in
       prerr_endline ("Potential struct return " ^ string_of_id struct_id ^ " to " ^ string_of_id id);
       begin match fix_updates_ret struct_id id instrs with
       | None -> instr :: opt hr instrs
       | Some updated -> opt hr updated
       end

    | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (opt hr block), aux) :: opt hr instrs
    | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (opt hr block), aux) :: opt hr instrs
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: instrs ->
       I_aux (I_if (cval, opt hr then_instrs, opt hr else_instrs, ctyp), aux) :: opt hr instrs

    | instr :: instrs -> instr :: opt hr instrs
    | [] -> []
  in
  function
  | CDEF_fundef (function_id, heap_return, args, body) ->
     [CDEF_fundef (function_id, heap_return, args, opt heap_return body)]
  | cdef -> [cdef]

let concatMap f xs = List.concat (List.map f xs)

let optimize ctx cdefs =
  let nothing cdefs = cdefs in
  cdefs
  |> (if !optimize_hoist_allocations then concatMap (hoist_allocations ctx) else nothing)
  |> (if !optimize_struct_updates then concatMap (fix_struct_updates ctx) else nothing)

(**************************************************************************)
(* 6. Code generation                                                     *)
(**************************************************************************)

let sgen_id id = Util.zencode_string (string_of_id id)
let codegen_id id = string (sgen_id id)

let upper_sgen_id id = Util.zencode_string (string_of_id id)
let upper_codegen_id id = string (upper_sgen_id id)

let rec sgen_ctyp = function
  | CT_unit -> "unit"
  | CT_bit -> "mach_bits"
  | CT_bool -> "bool"
  | CT_bits64 _ -> "mach_bits"
  | CT_int64 -> "mach_int"
  | CT_int -> "sail_int"
  | CT_bits _ -> "sail_bits"
  | CT_tup _ as tup -> "struct " ^ Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> "struct " ^ sgen_id id
  | CT_enum (id, _) -> "enum " ^ sgen_id id
  | CT_variant (id, _) -> "struct " ^ sgen_id id
  | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
  | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
  | CT_string -> "sail_string"
  | CT_real -> "real"
  | CT_ref ctyp -> sgen_ctyp ctyp ^ "*"

let rec sgen_ctyp_name = function
  | CT_unit -> "unit"
  | CT_bit -> "mach_bits"
  | CT_bool -> "bool"
  | CT_bits64 _ -> "mach_bits"
  | CT_int64 -> "mach_int"
  | CT_int -> "sail_int"
  | CT_bits _ -> "sail_bits"
  | CT_tup _ as tup -> Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> sgen_id id
  | CT_enum (id, _) -> sgen_id id
  | CT_variant (id, _) -> sgen_id id
  | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
  | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
  | CT_string -> "sail_string"
  | CT_real -> "real"
  | CT_ref ctyp -> "ref_" ^ sgen_ctyp_name ctyp

let sgen_cval_param (frag, ctyp) =
  match ctyp with
  | CT_bits direction ->
     string_of_fragment frag ^ ", " ^ string_of_bool direction
  | CT_bits64 (len, direction) ->
     string_of_fragment frag ^ ", UINT64_C(" ^ string_of_int len ^ ") , " ^ string_of_bool direction
  | _ ->
     string_of_fragment frag

let sgen_cval = function (frag, _) -> string_of_fragment frag

let sgen_clexp = function
  | CL_id id -> "&" ^ sgen_id id
  | CL_field (id, field) -> "&(" ^ sgen_id id ^ "." ^ Util.zencode_string field ^ ")"
  | CL_addr id -> sgen_id id
  | CL_addr_field (id, field) -> "&(" ^ sgen_id id ^ "->" ^ Util.zencode_string field ^ ")"
  | CL_have_exception -> "have_exception"
  | CL_current_exception -> "current_exception"

let sgen_clexp_pure = function
  | CL_id id -> sgen_id id
  | CL_field (id, field) -> sgen_id id ^ "." ^ Util.zencode_string field
  | CL_addr id -> "*" ^ sgen_id id
  | CL_addr_field (id, field) -> sgen_id id ^ "->" ^ Util.zencode_string field
  | CL_have_exception -> "have_exception"
  | CL_current_exception -> "current_exception"

let rec codegen_instr fid ctx (I_aux (instr, _)) =
  match instr with
  | I_decl (ctyp, id) when is_stack_ctyp ctyp ->
     string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_id id))
  | I_decl (ctyp, id) ->
     string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_id id)) ^^ hardline
     ^^ string (Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id))

  | I_copy (clexp, cval) ->
     let ctyp = cval_ctyp cval in
     if is_stack_ctyp ctyp then
       string (Printf.sprintf "  %s = %s;" (sgen_clexp_pure clexp) (sgen_cval cval))
     else
       string (Printf.sprintf "  COPY(%s)(%s, %s);" (sgen_ctyp_name ctyp) (sgen_clexp clexp) (sgen_cval cval))
  | I_jump (cval, label) ->
     string (Printf.sprintf "  if (%s) goto %s;" (sgen_cval cval) label)
  | I_if (cval, [then_instr], [], ctyp) ->
     string (Printf.sprintf "  if (%s)" (sgen_cval cval)) ^^ hardline
     ^^ twice space ^^ codegen_instr fid ctx then_instr
  | I_if (cval, then_instrs, [], ctyp) ->
     string "  if" ^^ space ^^ parens (string (sgen_cval cval)) ^^ space
     ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
  | I_if (cval, then_instrs, else_instrs, ctyp) ->
     string "  if" ^^ space ^^ parens (string (sgen_cval cval)) ^^ space
     ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
     ^^ space ^^ string "else" ^^ space
     ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) else_instrs) (twice space ^^ rbrace)
  | I_block instrs ->
     string "  {"
     ^^ jump 2 2 (separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline
     ^^ string "  }"
  | I_try_block instrs ->
     string "  { /* try */"
     ^^ jump 2 2 (separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline
     ^^ string "  }"
  | I_funcall (x, extern, f, args, ctyp) ->
     let c_args = Util.string_of_list ", " sgen_cval args in
     let fname =
       if Env.is_extern f ctx.tc_env "c" then
         Env.get_extern f ctx.tc_env "c"
       else if extern then
         string_of_id f
       else
         sgen_id f
     in
     let fname =
       match fname, ctyp with
       | "internal_pick", _ -> Printf.sprintf "pick_%s" (sgen_ctyp_name ctyp)
       | "eq_anything", _ ->
          begin match args with
          | cval :: _ -> Printf.sprintf "eq_%s" (sgen_ctyp_name (cval_ctyp cval))
          | _ -> c_error "eq_anything function with bad arity."
          end
       | "length", _ ->
          begin match args with
          | cval :: _ -> Printf.sprintf "length_%s" (sgen_ctyp_name (cval_ctyp cval))
          | _ -> c_error "length function with bad arity."
          end
       | "vector_access", CT_bit -> "bitvector_access"
       | "vector_access", _ ->
          begin match args with
          | cval :: _ -> Printf.sprintf "vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
          | _ -> c_error "vector access function with bad arity."
          end
       | "vector_update_subrange", _ -> Printf.sprintf "vector_update_subrange_%s" (sgen_ctyp_name ctyp)
       | "vector_subrange", _ -> Printf.sprintf "vector_subrange_%s" (sgen_ctyp_name ctyp)
       | "vector_update", CT_bits64 _ -> "update_mach_bits"
       | "vector_update", CT_bits _ -> "update_sail_bits"
       | "vector_update", _ -> Printf.sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
       | "internal_vector_update", _ -> Printf.sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
       | "internal_vector_init", _ -> Printf.sprintf "internal_vector_init_%s" (sgen_ctyp_name ctyp)
       | "undefined_vector", CT_bits64 _ -> "UNDEFINED(mach_bits)"
       | "undefined_vector", CT_bits _ -> "UNDEFINED(sail_bits)"
       | "undefined_bit", _ -> "UNDEFINED(mach_bits)"
       | "undefined_vector", _ -> Printf.sprintf "UNDEFINED(vector_%s)" (sgen_ctyp_name ctyp)
       | fname, _ -> fname
     in
     if fname = "reg_deref" then
       if is_stack_ctyp ctyp then
         string (Printf.sprintf  " %s = *(%s);" (sgen_clexp_pure x) c_args)
       else
         string (Printf.sprintf  " COPY(%s)(&%s, *(%s));" (sgen_ctyp_name ctyp) (sgen_clexp_pure x) c_args)
     else if is_stack_ctyp ctyp then
       string (Printf.sprintf "  %s = %s(%s);" (sgen_clexp_pure x) fname c_args)
     else
       string (Printf.sprintf "  %s(%s, %s);" fname (sgen_clexp x) c_args)

  | I_clear (ctyp, id) when is_stack_ctyp ctyp ->
     empty
  | I_clear (ctyp, id) ->
     string (Printf.sprintf "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id))

  | I_init (ctyp, id, cval) when is_stack_ctyp ctyp ->
     string (Printf.sprintf "  %s %s = %s;" (sgen_ctyp ctyp) (sgen_id id) (sgen_cval cval))
  | I_init (ctyp, id, cval) ->
     string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_id id)) ^^ hardline
     ^^ string (Printf.sprintf "  CREATE_OF(%s, %s)(&%s, %s);"
                               (sgen_ctyp_name ctyp)
                               (sgen_ctyp_name (cval_ctyp cval))
                               (sgen_id id)
                               (sgen_cval_param cval))

  | I_reinit (ctyp, id, cval) when is_stack_ctyp ctyp ->
     string (Printf.sprintf "  %s %s = %s;" (sgen_ctyp ctyp) (sgen_id id) (sgen_cval cval))
  | I_reinit (ctyp, id, cval) ->
     string (Printf.sprintf "  RECREATE_OF(%s, %s)(&%s, %s);"
                            (sgen_ctyp_name ctyp)
                            (sgen_ctyp_name (cval_ctyp cval))
                            (sgen_id id)
                            (sgen_cval_param cval))

  | I_reset (ctyp, id) when is_stack_ctyp ctyp ->
     string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_id id))
  | I_reset (ctyp, id) ->
     string (Printf.sprintf "  RECREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id))

  (* FIXME: This just covers the cases we see in our specs, need a
     special conversion code-generator for full generality *)
  | I_convert (x, CT_tup ctyps1, y, CT_tup ctyps2) when List.length ctyps1 = List.length ctyps2 ->
     let convert i (ctyp1, ctyp2) =
       if ctyp_equal ctyp1 ctyp2 then
         string (Printf.sprintf "  %s.ztup%i = %s.ztup%i;" (sgen_clexp_pure x) i (sgen_id y) i)
       else if ctyp_equal ctyp1 ctyp2 then
         c_error "heap tuple type conversion"
       else if is_stack_ctyp ctyp1 then
         string (Printf.sprintf "  %s.ztup%i = CONVERT_OF(%s, %s)(%s.ztup%i);"
                                (sgen_clexp_pure x)
                                i
                                (sgen_ctyp_name ctyp1)
                                (sgen_ctyp_name ctyp2)
                                (sgen_id y)
                                i)
       else
         string (Printf.sprintf "  CONVERT_OF(%s, %s)(%s.ztup%i, %s.ztup%i);"
                                (sgen_ctyp_name ctyp1)
                                (sgen_ctyp_name ctyp2)
                                (sgen_clexp x)
                                i
                                (sgen_id y)
                                i)
     in
     separate hardline (List.mapi convert (List.map2 (fun x y -> (x, y)) ctyps1 ctyps2))
  (* If we're converting from a bits type with a known compile time
     length, pass it as an extra parameter to the conversion. *)
  | I_convert (x, ctyp1, y, (CT_bits64 (n, _) as ctyp2)) ->
     if is_stack_ctyp ctyp1 then
       string (Printf.sprintf "  %s = CONVERT_OF(%s, %s)(%s, %d);"
                 (sgen_clexp_pure x)
                 (sgen_ctyp_name ctyp1)
                 (sgen_ctyp_name ctyp2)
                 (sgen_id y)
                 n)
     else
       string (Printf.sprintf "  CONVERT_OF(%s, %s)(%s, %s, %d);"
                 (sgen_ctyp_name ctyp1)
                 (sgen_ctyp_name ctyp2)
                 (sgen_clexp x)
                 (sgen_id y)
                 n)
  | I_convert (x, ctyp1, y, ctyp2) ->
     if is_stack_ctyp ctyp1 then
       string (Printf.sprintf "  %s = CONVERT_OF(%s, %s)(%s);"
                 (sgen_clexp_pure x)
                 (sgen_ctyp_name ctyp1)
                 (sgen_ctyp_name ctyp2)
                 (sgen_id y))
     else
       string (Printf.sprintf "  CONVERT_OF(%s, %s)(%s, %s);"
                 (sgen_ctyp_name ctyp1)
                 (sgen_ctyp_name ctyp2)
                 (sgen_clexp x)
                 (sgen_id y))
  | I_return cval ->
     string (Printf.sprintf "  return %s;" (sgen_cval cval))
  | I_throw cval ->
     c_error "I_throw reached code generator"
  | I_comment str ->
     string ("  /* " ^ str ^ " */")
  | I_label str ->
     string (str ^ ": ;")
  | I_goto str ->
     string (Printf.sprintf "  goto %s;" str)

  | I_raw _ when ctx.no_raw -> empty
  | I_raw str ->
     string ("  " ^ str)

  | I_match_failure ->
     string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")

let codegen_type_def ctx = function
  | CTD_enum (id, ids) ->
     let codegen_eq =
       let name = sgen_id id in
       string (Printf.sprintf "static bool eq_%s(enum %s op1, enum %s op2) { return op1 == op2; }" name name name)
     in
     string (Printf.sprintf "// enum %s" (string_of_id id)) ^^ hardline
     ^^ separate space [string "enum"; codegen_id id; lbrace; separate_map (comma ^^ space) upper_codegen_id ids; rbrace ^^ semi]
     ^^ twice hardline
     ^^ codegen_eq

  | CTD_struct (id, ctors) ->
     (* Generate a set_T function for every struct T *)
     let codegen_set (id, ctyp) =
       if is_stack_ctyp ctyp then
         string (Printf.sprintf "rop->%s = op.%s;" (sgen_id id) (sgen_id id))
       else
         string (Printf.sprintf "COPY(%s)(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_id id) (sgen_id id))
     in
     let codegen_setter id ctors =
       string (let n = sgen_id id in Printf.sprintf "static void COPY(%s)(struct %s *rop, const struct %s op)" n n n) ^^ space
       ^^ surround 2 0 lbrace
                   (separate_map hardline codegen_set (Bindings.bindings ctors))
                   rbrace
     in
     (* Generate an init/clear_T function for every struct T *)
     let codegen_field_init f (id, ctyp) =
       if not (is_stack_ctyp ctyp) then
         [string (Printf.sprintf "%s(%s)(&op->%s);" f (sgen_ctyp_name ctyp) (sgen_id id))]
       else []
     in
     let codegen_init f id ctors =
       string (let n = sgen_id id in Printf.sprintf "static void %s(%s)(struct %s *op)" f n n) ^^ space
       ^^ surround 2 0 lbrace
                   (separate hardline (Bindings.bindings ctors |> List.map (codegen_field_init f) |> List.concat))
                   rbrace
     in
     let codegen_eq =
       let codegen_eq_test (id, ctyp) =
         string (Printf.sprintf "EQUAL(%s)(op1.%s, op2.%s)" (sgen_ctyp_name ctyp) (sgen_id id) (sgen_id id))
       in
       string (Printf.sprintf "static bool EQUAL(%s)(struct %s op1, struct %s op2)" (sgen_id id) (sgen_id id) (sgen_id id))
       ^^ space
       ^^ surround 2 0 lbrace
            (string "return" ^^ space
             ^^ separate_map (string " && ") codegen_eq_test ctors
             ^^ string ";")
            rbrace
     in
     (* Generate the struct and add the generated functions *)
     let codegen_ctor (id, ctyp) =
       string (sgen_ctyp ctyp) ^^ space ^^ codegen_id id
     in
     string (Printf.sprintf "// struct %s" (string_of_id id)) ^^ hardline
     ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
     ^^ surround 2 0 lbrace
                 (separate_map (semi ^^ hardline) codegen_ctor ctors ^^ semi)
                 rbrace
     ^^ semi ^^ twice hardline
     ^^ codegen_setter id (ctor_bindings ctors)
     ^^ twice hardline
     ^^ codegen_init "CREATE" id (ctor_bindings ctors)
     ^^ twice hardline
     ^^ codegen_init "RECREATE" id (ctor_bindings ctors)
     ^^ twice hardline
     ^^ codegen_init "KILL" id (ctor_bindings ctors)
     ^^ twice hardline
     ^^ codegen_eq

  | CTD_variant (id, tus) ->
     let codegen_tu (ctor_id, ctyp) =
       separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_id ctor_id ^^ semi; rbrace]
     in
     (* Create an if, else if, ... block that does something for each constructor *)
     let rec each_ctor v f = function
       | [] -> string "{}"
       | [(ctor_id, ctyp)] ->
          string (Printf.sprintf "if (%skind == Kind_%s)" v (sgen_id ctor_id)) ^^ lbrace ^^ hardline
          ^^ jump 0 2 (f ctor_id ctyp)
          ^^ hardline ^^ rbrace
       | (ctor_id, ctyp) :: ctors ->
          string (Printf.sprintf "if (%skind == Kind_%s) " v (sgen_id ctor_id)) ^^ lbrace ^^ hardline
          ^^ jump 0 2 (f ctor_id ctyp)
          ^^ hardline ^^ rbrace ^^ string " else " ^^ each_ctor v f ctors
     in
     let codegen_init =
       let n = sgen_id id in
       let ctor_id, ctyp = List.hd tus in
       string (Printf.sprintf "static void CREATE(%s)(struct %s *op)" n n)
       ^^ hardline
       ^^ surround 2 0 lbrace
                   (string (Printf.sprintf "op->kind = Kind_%s;" (sgen_id ctor_id)) ^^ hardline
                    ^^ if not (is_stack_ctyp ctyp) then
                         string (Printf.sprintf "CREATE(%s)(&op->%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id))
                       else empty)
                   rbrace
     in
     let codegen_reinit =
       let n = sgen_id id in
       string (Printf.sprintf "static void RECREATE(%s)(struct %s *op) {}" n n)
     in
     let clear_field v ctor_id ctyp =
       if is_stack_ctyp ctyp then
         string (Printf.sprintf "/* do nothing */")
       else
         string (Printf.sprintf "KILL(%s)(&%s->%s);" (sgen_ctyp_name ctyp) v (sgen_id ctor_id))
     in
     let codegen_clear =
       let n = sgen_id id in
       string (Printf.sprintf "static void KILL(%s)(struct %s *op)" n n) ^^ hardline
       ^^ surround 2 0 lbrace
                   (each_ctor "op->" (clear_field "op") tus ^^ semi)
                   rbrace
     in
     let codegen_ctor (ctor_id, ctyp) =
       let ctor_args, tuple =
         let tuple_set i ctyp =
           if is_stack_ctyp ctyp then
             string (Printf.sprintf "op.ztup%d = op%d;" i i)
           else
             string (Printf.sprintf "set_%s(&op.ztup%d, op%d);" (sgen_ctyp_name ctyp) i i)
         in
         match ctyp with
         | CT_tup ctyps ->
            String.concat ", " (List.mapi (fun i ctyp -> Printf.sprintf "%s op%d" (sgen_ctyp ctyp) i) ctyps),
            string (Printf.sprintf "%s op;" (sgen_ctyp ctyp)) ^^ hardline
            ^^ string (Printf.sprintf "CREATE(%s)(&op);" (sgen_ctyp_name ctyp)) ^^ hardline
            ^^ separate hardline (List.mapi tuple_set ctyps) ^^ hardline
         | ctyp -> Printf.sprintf "%s op" (sgen_ctyp ctyp), empty
       in
       string (Printf.sprintf "static void %s(struct %s *rop, %s)" (sgen_id ctor_id) (sgen_id id) ctor_args) ^^ hardline
       ^^ surround 2 0 lbrace
                   (tuple
                    ^^ each_ctor "rop->" (clear_field "rop") tus ^^ hardline
                    ^^ string ("rop->kind = Kind_" ^ sgen_id ctor_id) ^^ semi ^^ hardline
                    ^^ if is_stack_ctyp ctyp then
                         string (Printf.sprintf "rop->%s = op;" (sgen_id ctor_id))
                       else
                         string (Printf.sprintf "CREATE(%s)(&rop->%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id)) ^^ hardline
                         ^^ string (Printf.sprintf "COPY(%s)(&rop->%s, op);" (sgen_ctyp_name ctyp) (sgen_id ctor_id)))
                   rbrace
     in
     let codegen_setter =
       let n = sgen_id id in
       let set_field ctor_id ctyp =
         if is_stack_ctyp ctyp then
           string (Printf.sprintf "rop->%s = op.%s;" (sgen_id ctor_id) (sgen_id ctor_id))
         else
           string (Printf.sprintf "CREATE(%s)(&rop->%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id))
           ^^ string (Printf.sprintf " COPY(%s)(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id) (sgen_id ctor_id))
       in
       string (Printf.sprintf "static void COPY(%s)(struct %s *rop, struct %s op)" n n n) ^^ hardline
       ^^ surround 2 0 lbrace
                   (each_ctor "rop->" (clear_field "rop") tus
                    ^^ semi ^^ hardline
                    ^^ string "rop->kind = op.kind"
                    ^^ semi ^^ hardline
                    ^^ each_ctor "op." set_field tus)
                   rbrace
     in
     let codegen_eq =
       let codegen_eq_test ctor_id ctyp =
         string (Printf.sprintf "return EQUAL(%s)(op1.%s, op2.%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id) (sgen_id ctor_id))
       in
       let rec codegen_eq_tests = function
         | [] -> string "return false;"
         | (ctor_id, ctyp) :: ctors ->
            string (Printf.sprintf "if (op1.kind == Kind_%s && op2.kind == Kind_%s) " (sgen_id ctor_id) (sgen_id ctor_id)) ^^ lbrace ^^ hardline
            ^^ jump 0 2 (codegen_eq_test ctor_id ctyp)
            ^^ hardline ^^ rbrace ^^ string " else " ^^ codegen_eq_tests ctors
       in
       let n = sgen_id id in
       string (Printf.sprintf "static bool EQUAL(%s)(struct %s op1, struct %s op2) " n n n)
       ^^ surround 2 0 lbrace (codegen_eq_tests tus) rbrace
     in
     string (Printf.sprintf "// union %s" (string_of_id id)) ^^ hardline
     ^^ string "enum" ^^ space
     ^^ string ("kind_" ^ sgen_id id) ^^ space
     ^^ separate space [ lbrace;
                         separate_map (comma ^^ space) (fun id -> string ("Kind_" ^ sgen_id id)) (List.map fst tus);
                         rbrace ^^ semi ]
     ^^ twice hardline
     ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
     ^^ surround 2 0 lbrace
                 (separate space [string "enum"; string ("kind_" ^ sgen_id id); string "kind" ^^ semi]
                  ^^ hardline
                  ^^ string "union" ^^ space
                  ^^ surround 2 0 lbrace
                              (separate_map (semi ^^ hardline) codegen_tu tus ^^ semi)
                              rbrace
                  ^^ semi)
                 rbrace
     ^^ semi
     ^^ twice hardline
     ^^ codegen_init
     ^^ twice hardline
     ^^ codegen_reinit
     ^^ twice hardline
     ^^ codegen_clear
     ^^ twice hardline
     ^^ codegen_setter
     ^^ twice hardline
     ^^ codegen_eq
     ^^ twice hardline
     ^^ separate_map (twice hardline) codegen_ctor tus
     (* If this is the exception type, then we setup up some global variables to deal with exceptions. *)
     ^^ if string_of_id id = "exception" then
          twice hardline
          ^^ string "struct zexception *current_exception = NULL;"
          ^^ hardline
          ^^ string "bool have_exception = false;"
        else
          empty

(** GLOBAL: because C doesn't have real anonymous tuple types
   (anonymous structs don't quite work the way we need) every tuple
   type in the spec becomes some generated named struct in C. This is
   done in such a way that every possible tuple type has a unique name
   associated with it. This global variable keeps track of these
   generated struct names, so we never generate two copies of the
   struct that is used to represent them in C.

   The way this works is that codegen_def scans each definition's type
   annotations for tuple types and generates the required structs
   using codegen_type_def before the actual definition is generated by
   codegen_def'.

   This variable should be reset to empty only when the entire AST has
   been translated to C. **)
let generated = ref IdSet.empty

let codegen_tup ctx ctyps =
  let id = mk_id ("tuple_" ^ string_of_ctyp (CT_tup ctyps)) in
  if IdSet.mem id !generated then
    empty
  else
    begin
      let _, fields = List.fold_left (fun (n, fields) ctyp -> n + 1, Bindings.add (mk_id ("tup" ^ string_of_int n)) ctyp fields)
                                     (0, Bindings.empty)
                                     ctyps
      in
      generated := IdSet.add id !generated;
      codegen_type_def ctx (CTD_struct (id, Bindings.bindings fields)) ^^ twice hardline
    end

let codegen_node id ctyp =
  string (Printf.sprintf "struct node_%s {\n  %s hd;\n  struct node_%s *tl;\n};\n" (sgen_id id) (sgen_ctyp ctyp) (sgen_id id))
  ^^ string (Printf.sprintf "typedef struct node_%s *%s;" (sgen_id id) (sgen_id id))

let codegen_list_init id =
  string (Printf.sprintf "static void CREATE(%s)(%s *rop) { *rop = NULL; }" (sgen_id id) (sgen_id id))

let codegen_list_clear id ctyp =
  string (Printf.sprintf "static void KILL(%s)(%s *rop) {\n" (sgen_id id) (sgen_id id))
  ^^ string (Printf.sprintf "  if (*rop == NULL) return;")
  ^^ (if is_stack_ctyp ctyp then empty
      else string (Printf.sprintf "  KILL(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp)))
  ^^ string (Printf.sprintf "  KILL(%s)(&(*rop)->tl);\n" (sgen_id id))
  ^^ string "  free(*rop);"
  ^^ string "}"

let codegen_list_set id ctyp =
  string (Printf.sprintf "static void internal_set_%s(%s *rop, const %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id))
  ^^ string "  if (op == NULL) { *rop = NULL; return; };\n"
  ^^ string (Printf.sprintf "  *rop = malloc(sizeof(struct node_%s));\n" (sgen_id id))
  ^^ (if is_stack_ctyp ctyp then
        string "  (*rop)->hd = op->hd;\n"
      else
        string (Printf.sprintf "  CREATE(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp))
        ^^ string (Printf.sprintf "  COPY(%s)(&(*rop)->hd, op->hd);\n" (sgen_ctyp_name ctyp)))
  ^^ string (Printf.sprintf "  internal_set_%s(&(*rop)->tl, op->tl);\n" (sgen_id id))
  ^^ string "}"
  ^^ twice hardline
  ^^ string (Printf.sprintf "static void COPY(%s)(%s *rop, const %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id))
  ^^ string (Printf.sprintf "  KILL(%s)(rop);\n" (sgen_id id))
  ^^ string (Printf.sprintf "  internal_set_%s(rop, op);\n" (sgen_id id))
  ^^ string "}"

let codegen_cons id ctyp =
  let cons_id = mk_id ("cons#" ^ string_of_ctyp ctyp) in
  string (Printf.sprintf "static void %s(%s *rop, const %s x, const %s xs) {\n" (sgen_id cons_id) (sgen_id id) (sgen_ctyp ctyp) (sgen_id id))
  ^^ string (Printf.sprintf "  *rop = malloc(sizeof(struct node_%s));\n" (sgen_id id))
  ^^ (if is_stack_ctyp ctyp then
        string "  (*rop)->hd = x;\n"
      else
        string (Printf.sprintf "  CREATE(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp))
        ^^ string (Printf.sprintf "  COPY(%s)(&(*rop)->hd, x);\n" (sgen_ctyp_name ctyp)))
  ^^ string "  (*rop)->tl = xs;\n"
  ^^ string "}"

let codegen_pick id ctyp =
  if is_stack_ctyp ctyp then
    string (Printf.sprintf "static %s pick_%s(const %s xs) { return xs->hd; }" (sgen_ctyp ctyp) (sgen_ctyp_name ctyp) (sgen_id id))
  else
    string (Printf.sprintf "static void pick_%s(%s *x, const %s xs) { COPY(%s)(x, xs->hd); }" (sgen_ctyp_name ctyp) (sgen_ctyp ctyp) (sgen_id id) (sgen_ctyp_name ctyp))

let codegen_list ctx ctyp =
  let id = mk_id (string_of_ctyp (CT_list ctyp)) in
  if IdSet.mem id !generated then
    empty
  else
    begin
      generated := IdSet.add id !generated;
      codegen_node id ctyp ^^ twice hardline
      ^^ codegen_list_init id ^^ twice hardline
      ^^ codegen_list_clear id ctyp ^^ twice hardline
      ^^ codegen_list_set id ctyp ^^ twice hardline
      ^^ codegen_cons id ctyp ^^ twice hardline
      ^^ codegen_pick id ctyp ^^ twice hardline
    end

(* Generate functions for working with non-bit vectors of some specific type. *)
let codegen_vector ctx (direction, ctyp) =
  let id = mk_id (string_of_ctyp (CT_vector (direction, ctyp))) in
  if IdSet.mem id !generated then
    empty
  else
    let vector_typedef =
      string (Printf.sprintf "struct %s {\n  size_t len;\n  %s *data;\n};\n" (sgen_id id) (sgen_ctyp ctyp))
      ^^ string (Printf.sprintf "typedef struct %s %s;" (sgen_id id) (sgen_id id))
    in
    let vector_init =
      string (Printf.sprintf "static void CREATE(%s)(%s *rop) {\n  rop->len = 0;\n  rop->data = NULL;\n}" (sgen_id id) (sgen_id id))
    in
    let vector_set =
      string (Printf.sprintf "static void COPY(%s)(%s *rop, %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id))
      ^^ string (Printf.sprintf "  KILL(%s)(rop);\n" (sgen_id id))
      ^^ string "  rop->len = op.len;\n"
      ^^ string (Printf.sprintf "  rop->data = malloc((rop->len) * sizeof(%s));\n" (sgen_ctyp ctyp))
      ^^ string "  for (int i = 0; i < op.len; i++) {\n"
      ^^ string (if is_stack_ctyp ctyp then
                   "    (rop->data)[i] = op.data[i];\n"
                 else
                   Printf.sprintf "    CREATE(%s)((rop->data) + i);\n    COPY(%s)((rop->data) + i, op.data[i]);\n" (sgen_ctyp_name ctyp) (sgen_ctyp_name ctyp))
      ^^ string "  }\n"
      ^^ string "}"
    in
    let vector_clear =
      string (Printf.sprintf "static void KILL(%s)(%s *rop) {\n" (sgen_id id) (sgen_id id))
      ^^ (if is_stack_ctyp ctyp then empty
         else
           string "  for (int i = 0; i < (rop->len); i++) {\n"
           ^^ string (Printf.sprintf "    KILL(%s)((rop->data) + i);\n" (sgen_ctyp_name ctyp))
           ^^ string "  }\n")
      ^^ string "  if (rop->data != NULL) free(rop->data);\n"
      ^^ string "}"
    in
    let vector_update =
      string (Printf.sprintf "static void vector_update_%s(%s *rop, %s op, mpz_t n, %s elem) {\n" (sgen_id id) (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
      ^^ string "  int m = mpz_get_ui(n);\n"
      ^^ string "  if (rop->data == op.data) {\n"
      ^^ string (if is_stack_ctyp ctyp then
                   "    rop->data[m] = elem;\n"
                 else
                   Printf.sprintf "  COPY(%s)((rop->data) + m, elem);\n" (sgen_ctyp_name ctyp))
      ^^ string "  } else {\n"
      ^^ string (Printf.sprintf "    COPY(%s)(rop, op);\n" (sgen_id id))
      ^^ string (if is_stack_ctyp ctyp then
                   "    rop->data[m] = elem;\n"
                 else
                   Printf.sprintf "  COPY(%s)((rop->data) + m, elem);\n" (sgen_ctyp_name ctyp))
      ^^ string "  }\n"
      ^^ string "}"
    in
    let internal_vector_update =
      string (Printf.sprintf "static void internal_vector_update_%s(%s *rop, %s op, const int64_t n, %s elem) {\n" (sgen_id id) (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
      ^^ string (if is_stack_ctyp ctyp then
                   "  rop->data[n] = elem;\n"
                 else
                   Printf.sprintf "  COPY(%s)((rop->data) + n, elem);\n" (sgen_ctyp_name ctyp))
      ^^ string "}"
    in
    let vector_access =
      if is_stack_ctyp ctyp then
        string (Printf.sprintf "static %s vector_access_%s(%s op, mpz_t n) {\n" (sgen_ctyp ctyp) (sgen_id id) (sgen_id id))
        ^^ string "  int m = mpz_get_ui(n);\n"
        ^^ string "  return op.data[m];\n"
        ^^ string "}"
      else
        string (Printf.sprintf "static void vector_access_%s(%s *rop, %s op, mpz_t n) {\n" (sgen_id id) (sgen_ctyp ctyp) (sgen_id id))
        ^^ string "  int m = mpz_get_ui(n);\n"
        ^^ string (Printf.sprintf "  COPY(%s)(rop, op.data[m]);\n" (sgen_ctyp_name ctyp))
        ^^ string "}"
    in
    let internal_vector_init =
      string (Printf.sprintf "static void internal_vector_init_%s(%s *rop, const int64_t len) {\n" (sgen_id id) (sgen_id id))
      ^^ string "  rop->len = len;\n"
      ^^ string (Printf.sprintf "  rop->data = malloc(len * sizeof(%s));\n" (sgen_ctyp ctyp))
      ^^ string "}"
    in
    let vector_undefined =
      string (Printf.sprintf "static void undefined_vector_%s(%s *rop, mpz_t len, %s elem) {\n" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
      ^^ string (Printf.sprintf "  rop->len = mpz_get_ui(len);\n")
      ^^ string (Printf.sprintf "  rop->data = malloc((rop->len) * sizeof(%s));\n" (sgen_ctyp ctyp))
      ^^ string "  for (int i = 0; i < (rop->len); i++) {\n"
      ^^ string (if is_stack_ctyp ctyp then
                   "    (rop->data)[i] = elem;\n"
                 else
                   Printf.sprintf "    CREATE(%s)((rop->data) + i);\n    COPY(%s)((rop->data) + i, elem);\n" (sgen_ctyp_name ctyp) (sgen_ctyp_name ctyp))
      ^^ string "  }\n"
      ^^ string "}"
    in
    begin
      generated := IdSet.add id !generated;
      vector_typedef ^^ twice hardline
      ^^ vector_init ^^ twice hardline
      ^^ vector_clear ^^ twice hardline
      ^^ vector_undefined ^^ twice hardline
      ^^ vector_access ^^ twice hardline
      ^^ vector_set ^^ twice hardline
      ^^ vector_update ^^ twice hardline
      ^^ internal_vector_update ^^ twice hardline
      ^^ internal_vector_init ^^ twice hardline
    end

let is_decl = function
  | I_aux (I_decl _, _) -> true
  | _ -> false

let codegen_decl = function
  | I_aux (I_decl (ctyp, id), _) ->
     string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_id id))
  | _ -> assert false

let codegen_alloc = function
  | I_aux (I_decl (ctyp, id), _) when is_stack_ctyp ctyp -> empty
  | I_aux (I_decl (ctyp, id), _) ->
     string (Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id))
  | _ -> assert false

let codegen_def' ctx = function
  | CDEF_reg_dec (id, ctyp, _) ->
     string (Printf.sprintf "// register %s" (string_of_id id)) ^^ hardline
     ^^ string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_id id))

  | CDEF_spec (id, arg_ctyps, ret_ctyp) ->
     let static = if !opt_static then "static " else "" in
     if Env.is_extern id ctx.tc_env "c" then
       empty
     else if is_stack_ctyp ret_ctyp then
       string (Printf.sprintf "%s%s %s(%s);" static (sgen_ctyp ret_ctyp) (sgen_id id) (Util.string_of_list ", " sgen_ctyp arg_ctyps))
     else
       string (Printf.sprintf "%svoid %s(%s *rop, %s);" static (sgen_id id) (sgen_ctyp ret_ctyp) (Util.string_of_list ", " sgen_ctyp arg_ctyps))

  | CDEF_fundef (id, ret_arg, args, instrs) as def ->
     if !opt_ddump_flow_graphs then make_dot id (instrs_graph instrs) else ();
     let instrs = add_local_labels instrs in
     let quant, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let arg_typs, ret_typ = match fn_typ with
       | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
       | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
       | _ -> assert false
     in
     let ctx' = { ctx with local_env = add_typquant (id_loc id) quant ctx.local_env } in
     let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ in
     if (List.length arg_ctyps <> List.length args) then
       c_error ~loc:(id_loc id) ("function arguments "
                                 ^ Util.string_of_list ", " string_of_id args
                                 ^ " matched against type "
                                 ^ Util.string_of_list ", " string_of_ctyp arg_ctyps)
     else ();
     let args = Util.string_of_list ", " (fun x -> x) (List.map2 (fun ctyp arg -> sgen_ctyp ctyp ^ " " ^ sgen_id arg) arg_ctyps args) in
     let function_header =
       match ret_arg with
       | None ->
          assert (is_stack_ctyp ret_ctyp);
          (if !opt_static then string "static " else empty)
          ^^ string (sgen_ctyp ret_ctyp) ^^ space ^^ codegen_id id ^^ parens (string args) ^^ hardline
       | Some gs ->
          assert (not (is_stack_ctyp ret_ctyp));
          (if !opt_static then string "static " else empty)
          ^^ string "void" ^^ space ^^ codegen_id id
          ^^ parens (string (sgen_ctyp ret_ctyp ^ " *" ^ sgen_id gs ^ ", ") ^^ string args)
          ^^ hardline
     in
     function_header
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs) ^^ hardline
     ^^ string "}"

  | CDEF_type ctype_def ->
     codegen_type_def ctx ctype_def

  | CDEF_startup (id, instrs) ->
     let static = if !opt_static then "static " else "" in
     let startup_header = string (Printf.sprintf "%svoid startup_%s(void)" static (sgen_id id)) in
     separate_map hardline codegen_decl instrs
     ^^ twice hardline
     ^^ startup_header ^^ hardline
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline codegen_alloc instrs) ^^ hardline
     ^^ string "}"

  | CDEF_finish (id, instrs) ->
     let static = if !opt_static then "static " else "" in
     let finish_header = string (Printf.sprintf "%svoid finish_%s(void)" static (sgen_id id)) in
     separate_map hardline codegen_decl (List.filter is_decl instrs)
     ^^ twice hardline
     ^^ finish_header ^^ hardline
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs) ^^ hardline
     ^^ string "}"

  | CDEF_let (number, bindings, instrs) ->
     let instrs = add_local_labels instrs in
     let setup =
       List.concat (List.map (fun (id, ctyp) -> [idecl ctyp id]) bindings)
     in
     let cleanup =
       List.concat (List.map (fun (id, ctyp) -> [iclear ctyp id]) bindings)
     in
     separate_map hardline (fun (id, ctyp) -> string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_id id))) bindings
     ^^ hardline ^^ string (Printf.sprintf "static void create_letbind_%d(void) " number)
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline codegen_alloc setup) ^^ hardline
     ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") { ctx with no_raw = true }) instrs) ^^ hardline
     ^^ string "}"
     ^^ hardline ^^ string (Printf.sprintf "static void kill_letbind_%d(void) " number)
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") ctx) cleanup) ^^ hardline
     ^^ string "}"

let codegen_def ctx def =
  let untup = function
    | CT_tup ctyps -> ctyps
    | _ -> assert false
  in
  let unlist = function
    | CT_list ctyp -> ctyp
    | _ -> assert false
  in
  let unvector = function
    | CT_vector (direction, ctyp) -> (direction, ctyp)
    | _ -> assert false
  in
  let tups = List.filter is_ct_tup (cdef_ctyps ctx def) in
  let tups = List.map (fun ctyp -> codegen_tup ctx (untup ctyp)) tups in
  let lists = List.filter is_ct_list (cdef_ctyps ctx def) in
  let lists = List.map (fun ctyp -> codegen_list ctx (unlist ctyp)) lists in
  let vectors = List.filter is_ct_vector (cdef_ctyps ctx def) in
  let vectors = List.map (fun ctyp -> codegen_vector ctx (unvector ctyp)) vectors in
  (* prerr_endline (Pretty_print_sail.to_string (pp_cdef def)); *)
  concat tups
  ^^ concat lists
  ^^ concat vectors
  ^^ codegen_def' ctx def

let is_cdef_startup = function
  | CDEF_startup _ -> true
  | _ -> false

let sgen_startup = function
  | CDEF_startup (id, _) ->
     Printf.sprintf "  startup_%s();" (sgen_id id)
  | _ -> assert false

let sgen_instr id ctx instr =
  Pretty_print_sail.to_string (codegen_instr id ctx instr)

let is_cdef_finish = function
  | CDEF_startup _ -> true
  | _ -> false

let sgen_finish = function
  | CDEF_startup (id, _) ->
     Printf.sprintf "  finish_%s();" (sgen_id id)
  | _ -> assert false

let instrument_tracing ctx =
  let module StringSet = Set.Make(String) in
  let traceable = StringSet.of_list ["mach_bits"; "sail_string"; "sail_bits"; "sail_int"; "unit"; "bool"] in
  let rec instrument = function
    | (I_aux (I_funcall (clexp, _, id, args, ctyp), _) as instr) :: instrs ->
       let trace_start =
         iraw (Printf.sprintf "trace_start(\"%s\");" (String.escaped (string_of_id id)))
       in
       let trace_arg cval =
         let ctyp_name = sgen_ctyp_name (cval_ctyp cval) in
         if StringSet.mem ctyp_name traceable then
           iraw (Printf.sprintf "trace_%s(%s);" ctyp_name (sgen_cval cval))
         else
           iraw "trace_unknown();"
       in
       let rec trace_args = function
         | [] -> []
         | [cval] -> [trace_arg cval]
         | cval :: cvals ->
            trace_arg cval :: iraw "trace_argsep();" :: trace_args cvals
       in
       let trace_end = iraw "trace_end();" in
       let trace_ret =
         let ctyp_name = sgen_ctyp_name ctyp in
         if StringSet.mem ctyp_name traceable then
           iraw (Printf.sprintf "trace_%s(%s);" (sgen_ctyp_name ctyp) (sgen_clexp_pure clexp))
         else
           iraw "trace_unknown();"
       in
       [trace_start]
       @ trace_args args
       @ [iraw "trace_argend();";
          instr;
          trace_end;
          trace_ret;
          iraw "trace_retend();"]
       @ instrument instrs

    | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (instrument block), aux) :: instrument instrs
    | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (instrument block), aux) :: instrument instrs
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: instrs ->
       I_aux (I_if (cval, instrument then_instrs, instrument else_instrs, ctyp), aux) :: instrument instrs

    | instr :: instrs -> instr :: instrument instrs
    | [] -> []
  in
  function
  | CDEF_fundef (function_id, heap_return, args, body) ->
     CDEF_fundef (function_id, heap_return, args, instrument body)
  | cdef -> cdef

let bytecode_ast ctx rewrites (Defs defs) =
  let assert_vs = Initial_check.extern_of_string dec_ord (mk_id "sail_assert") "(bool, string) -> unit effect {escape}" in
  let exit_vs = Initial_check.extern_of_string dec_ord (mk_id "sail_exit") "unit -> unit effect {escape}" in

  let ctx = { ctx with tc_env = snd (Type_error.check ctx.tc_env (Defs [assert_vs; exit_vs])) } in
  let chunks, ctx = List.fold_left (fun (chunks, ctx) def -> let defs, ctx = compile_def ctx def in defs :: chunks, ctx) ([], ctx) defs in
  let cdefs = List.concat (List.rev chunks) in
  rewrites cdefs

let rec get_recursive_functions (Defs defs) =
  match defs with
  | DEF_internal_mutrec fundefs :: defs ->
     IdSet.union (List.map id_of_fundef fundefs |> IdSet.of_list) (get_recursive_functions (Defs defs))

  | (DEF_fundef fdef as def) :: defs ->
     let open Rewriter in
     let ids = ref IdSet.empty in
     let collect_funcalls e_aux annot =
       match e_aux with
       | E_app (id, args) -> (ids := IdSet.add id !ids; E_aux (e_aux, annot))
       | _ -> E_aux (e_aux, annot)
     in
     let map_exp = {
         id_exp_alg with
         e_aux = (fun (e_aux, annot) -> collect_funcalls e_aux annot)
       } in
     let map_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp map_exp) } in
     let _ = rewrite_def map_defs def in
     if IdSet.mem (id_of_fundef fdef) !ids then
       IdSet.add (id_of_fundef fdef) (get_recursive_functions (Defs defs))
     else
       get_recursive_functions (Defs defs)

  | _ :: defs -> get_recursive_functions (Defs defs)
  | [] -> IdSet.empty

let compile_ast ctx (Defs defs) =
  try
    c_debug (lazy (Util.log_line __MODULE__ __LINE__ "Identifying recursive functions"));
    let recursive_functions = Spec_analysis.top_sort_defs (Defs defs) |> get_recursive_functions in
    let ctx = { ctx with recursive_functions = recursive_functions } in
    c_debug (lazy (Util.string_of_list ", " string_of_id (IdSet.elements recursive_functions)));

    let assert_vs = Initial_check.extern_of_string dec_ord (mk_id "sail_assert") "(bool, string) -> unit effect {escape}" in
    let exit_vs = Initial_check.extern_of_string dec_ord (mk_id "sail_exit") "unit -> unit effect {escape}" in
    let ctx = { ctx with tc_env = snd (Type_error.check ctx.tc_env (Defs [assert_vs; exit_vs])) } in
    let chunks, ctx = List.fold_left (fun (chunks, ctx) def -> let defs, ctx = compile_def ctx def in defs :: chunks, ctx) ([], ctx) defs in
    let cdefs = List.concat (List.rev chunks) in

    let cdefs = optimize ctx cdefs in
    let cdefs = if !opt_trace then List.map (instrument_tracing ctx) cdefs else cdefs in

    let docs = List.map (codegen_def ctx) cdefs in

    let preamble = separate hardline
                     [ string "#include \"sail.h\"";
                       string "#include \"rts.h\"";
                       string "#include \"elf.h\"" ]
    in

    let exn_boilerplate =
      if not (Bindings.mem (mk_id "exception") ctx.variants) then ([], []) else
        ([ "  current_exception = malloc(sizeof(struct zexception));";
           "  CREATE(zexception)(current_exception);" ],
         [ "  KILL(zexception)(current_exception);";
           "  free(current_exception);";
           "  if (have_exception) fprintf(stderr, \"Exiting due to uncaught exception\\n\");" ])
    in

    let letbind_initializers =
      List.map (fun n -> Printf.sprintf "  create_letbind_%d();" n) (List.rev ctx.letbinds)
    in
    let letbind_finalizers =
      List.map (fun n -> Printf.sprintf "  kill_letbind_%d();" n) ctx.letbinds
    in
    let startup cdefs =
      List.map sgen_startup (List.filter is_cdef_startup cdefs)
    in
    let finish cdefs =
      List.map sgen_finish (List.filter is_cdef_finish cdefs)
    in

    let regs = c_ast_registers cdefs in

    let register_init_clear (id, ctyp, instrs) =
      if is_stack_ctyp ctyp then
        List.map (sgen_instr (mk_id "reg") ctx) instrs, []
      else
        [ Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id) ]
        @ List.map (sgen_instr (mk_id "reg") ctx) instrs,
        [ Printf.sprintf "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id) ]
    in

    let postamble = separate hardline (List.map string
       ( [ "int main(int argc, char *argv[])";
           "{";
           "  setup_rts();" ]
       @ fst exn_boilerplate
       @ startup cdefs
       @ List.concat (List.map (fun r -> fst (register_init_clear r)) regs)
       @ (if regs = [] then [] else [ "  zinitializze_registers(UNIT);" ])
       @ letbind_initializers
       @ [  "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);" ]
       @ [ "  zmain(UNIT);" ]
       @ letbind_finalizers
       @ List.concat (List.map (fun r -> snd (register_init_clear r)) regs)
       @ finish cdefs
       @ snd exn_boilerplate
       @ [ "  cleanup_rts();";
           "  return EXIT_SUCCESS;";
           "}" ] ))
    in

    let hlhl = hardline ^^ hardline in

    Pretty_print_sail.to_string (preamble ^^ hlhl ^^ separate hlhl docs ^^ hlhl ^^ postamble)
    |> print_endline
  with
    Type_error (l, err) -> c_error ("Unexpected type error when compiling to C:\n" ^ Type_error.string_of_type_error err)
