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

open Ast_util
open Jib
open Jib_compile
open Jib_util

let optimize_unit instrs =
  let unit_cval cval = match cval_ctyp cval with CT_unit -> V_lit (VL_unit, CT_unit) | _ -> cval in
  let unit_instr = function
    | I_aux (I_funcall (clexp, extern, id, args), annot) as instr -> begin
        match clexp_ctyp clexp with
        | CT_unit -> I_aux (I_funcall (CL_void, extern, id, List.map unit_cval args), annot)
        | _ -> instr
      end
    | I_aux (I_copy (clexp, cval), annot) as instr -> begin
        match clexp_ctyp clexp with CT_unit -> I_aux (I_copy (CL_void, unit_cval cval), annot) | _ -> instr
      end
    | instr -> instr
  in
  let non_pointless_copy (I_aux (aux, annot)) =
    match aux with I_decl (CT_unit, _) -> false | I_copy (CL_void, _) -> false | _ -> true
  in
  filter_instrs non_pointless_copy (map_instr_list unit_instr instrs)

let flat_counter = ref 0

let reset_flat_counter () = flat_counter := 0

let flat_id orig_id =
  let id = mk_id ("$" ^ string_of_int !flat_counter) in
  incr flat_counter;
  name id

let rec flatten_instrs = function
  | I_aux (I_decl (ctyp, decl_id), aux) :: instrs ->
      let fid = flat_id decl_id in
      I_aux (I_decl (ctyp, fid), aux) :: flatten_instrs (instrs_rename decl_id fid instrs)
  | I_aux (I_init (ctyp, decl_id, cval), aux) :: instrs ->
      let fid = flat_id decl_id in
      I_aux (I_init (ctyp, fid, cval), aux) :: flatten_instrs (instrs_rename decl_id fid instrs)
  | I_aux ((I_block block | I_try_block block), _) :: instrs -> flatten_instrs block @ flatten_instrs instrs
  | I_aux (I_if (cval, then_instrs, else_instrs, _), (_, l)) :: instrs ->
      let then_label = label "then_" in
      let endif_label = label "endif_" in
      [ijump l cval then_label]
      @ flatten_instrs else_instrs
      @ [igoto endif_label]
      @ [ilabel then_label]
      @ flatten_instrs then_instrs
      @ [ilabel endif_label]
      @ flatten_instrs instrs
  | I_aux (I_comment _, _) :: instrs -> flatten_instrs instrs
  | instr :: instrs -> instr :: flatten_instrs instrs
  | [] -> []

let flatten_cdef = function
  | CDEF_fundef (function_id, heap_return, args, body) ->
      flat_counter := 0;
      CDEF_fundef (function_id, heap_return, args, flatten_instrs body)
  | CDEF_let (n, bindings, instrs) ->
      flat_counter := 0;
      CDEF_let (n, bindings, flatten_instrs instrs)
  | cdef -> cdef

let unique_per_function_ids cdefs =
  let unique_id i = function
    | Name (id, ssa_num) -> Name (append_id id ("#u" ^ string_of_int i), ssa_num)
    | name -> name
  in
  let rec unique_instrs i = function
    | I_aux (I_decl (ctyp, id), aux) :: rest ->
        I_aux (I_decl (ctyp, unique_id i id), aux) :: unique_instrs i (instrs_rename id (unique_id i id) rest)
    | I_aux (I_init (ctyp, id, cval), aux) :: rest ->
        I_aux (I_init (ctyp, unique_id i id, cval), aux) :: unique_instrs i (instrs_rename id (unique_id i id) rest)
    | I_aux (I_block instrs, aux) :: rest -> I_aux (I_block (unique_instrs i instrs), aux) :: unique_instrs i rest
    | I_aux (I_try_block instrs, aux) :: rest ->
        I_aux (I_try_block (unique_instrs i instrs), aux) :: unique_instrs i rest
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: rest ->
        I_aux (I_if (cval, unique_instrs i then_instrs, unique_instrs i else_instrs, ctyp), aux) :: unique_instrs i rest
    | instr :: instrs -> instr :: unique_instrs i instrs
    | [] -> []
  in
  let unique_cdef i = function
    | CDEF_register (id, ctyp, instrs) -> CDEF_register (id, ctyp, unique_instrs i instrs)
    | CDEF_type ctd -> CDEF_type ctd
    | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, unique_instrs i instrs)
    | CDEF_val (id, extern, ctyps, ctyp) -> CDEF_val (id, extern, ctyps, ctyp)
    | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, unique_instrs i instrs)
    | CDEF_startup (id, instrs) -> CDEF_startup (id, unique_instrs i instrs)
    | CDEF_finish (id, instrs) -> CDEF_finish (id, unique_instrs i instrs)
    | CDEF_pragma (name, str) -> CDEF_pragma (name, str)
  in
  List.mapi unique_cdef cdefs

let rec cval_subst id subst = function
  | V_id (id', ctyp) -> if Name.compare id id' = 0 then subst else V_id (id', ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
  | V_call (op, cvals) -> V_call (op, List.map (cval_subst id subst) cvals)
  | V_field (cval, field) -> V_field (cval_subst id subst cval, field)
  | V_tuple_member (cval, len, n) -> V_tuple_member (cval_subst id subst cval, len, n)
  | V_ctor_kind (cval, ctor, ctyp) -> V_ctor_kind (cval_subst id subst cval, ctor, ctyp)
  | V_ctor_unwrap (cval, ctor, ctyp) -> V_ctor_unwrap (cval_subst id subst cval, ctor, ctyp)
  | V_struct (fields, ctyp) -> V_struct (List.map (fun (field, cval) -> (field, cval_subst id subst cval)) fields, ctyp)
  | V_tuple (members, ctyp) -> V_tuple (List.map (cval_subst id subst) members, ctyp)

let rec cval_map_id f = function
  | V_id (id, ctyp) -> V_id (f id, ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
  | V_call (call, cvals) -> V_call (call, List.map (cval_map_id f) cvals)
  | V_field (cval, field) -> V_field (cval_map_id f cval, field)
  | V_tuple_member (cval, len, n) -> V_tuple_member (cval_map_id f cval, len, n)
  | V_ctor_kind (cval, ctor, ctyp) -> V_ctor_kind (cval_map_id f cval, ctor, ctyp)
  | V_ctor_unwrap (cval, ctor, ctyp) -> V_ctor_unwrap (cval_map_id f cval, ctor, ctyp)
  | V_struct (fields, ctyp) -> V_struct (List.map (fun (field, cval) -> (field, cval_map_id f cval)) fields, ctyp)
  | V_tuple (members, ctyp) -> V_tuple (List.map (cval_map_id f) members, ctyp)

let remove_undefined =
  let gensym, _ = symbol_generator "gz" in
  let rec create_value l = function
    | CT_unit -> ([], V_lit (VL_unit, CT_unit))
    | CT_bool -> ([], V_lit (VL_bool false, CT_bool))
    | CT_bit -> ([], V_lit (VL_bit Sail2_values.B0, CT_bit))
    | CT_string -> ([], V_lit (VL_string "", CT_string))
    | CT_tup ctyps ->
        let setup, values =
          List.fold_right
            (fun ctyp (setups, values) ->
              let setup, value = create_value l ctyp in
              (setup @ setups, value :: values)
            )
            ctyps ([], [])
        in
        (setup, V_tuple (values, CT_tup ctyps))
    | ctyp ->
        let gs = name (gensym ()) in
        ([idecl l ctyp gs], V_id (gs, ctyp))
  in
  let rewrite_instr = function
    | I_aux (I_undefined ctyp, (_, l)) ->
        let setup, value = create_value l ctyp in
        begin
          match setup with [] -> ireturn value | _ -> iblock (setup @ [ireturn value])
        end
    | instr -> instr
  in
  map_instr_list rewrite_instr

let rec instrs_subst id subst = function
  | I_aux (I_decl (_, id'), _) :: _ as instrs when Name.compare id id' = 0 -> instrs
  | I_aux (I_init (ctyp, id', cval), aux) :: rest when Name.compare id id' = 0 ->
      I_aux (I_init (ctyp, id', cval_subst id subst cval), aux) :: rest
  | I_aux (I_reset (_, id'), _) :: _ as instrs when Name.compare id id' = 0 -> instrs
  | I_aux (I_reinit (ctyp, id', cval), aux) :: rest when Name.compare id id' = 0 ->
      I_aux (I_reinit (ctyp, id', cval_subst id subst cval), aux) :: rest
  | I_aux (instr, aux) :: instrs ->
      let instrs = instrs_subst id subst instrs in
      let instr =
        match instr with
        | I_decl (ctyp, id') -> I_decl (ctyp, id')
        | I_init (ctyp, id', cval) -> I_init (ctyp, id', cval_subst id subst cval)
        | I_jump (cval, label) -> I_jump (cval_subst id subst cval, label)
        | I_goto label -> I_goto label
        | I_label label -> I_label label
        | I_funcall (clexp, extern, fid, args) -> I_funcall (clexp, extern, fid, List.map (cval_subst id subst) args)
        | I_copy (clexp, cval) -> I_copy (clexp, cval_subst id subst cval)
        | I_clear (clexp, id') -> I_clear (clexp, id')
        | I_undefined ctyp -> I_undefined ctyp
        | I_exit cause -> I_exit cause
        | I_end id' -> I_end id'
        | I_if (cval, then_instrs, else_instrs, ctyp) ->
            I_if (cval_subst id subst cval, instrs_subst id subst then_instrs, instrs_subst id subst else_instrs, ctyp)
        | I_block instrs -> I_block (instrs_subst id subst instrs)
        | I_try_block instrs -> I_try_block (instrs_subst id subst instrs)
        | I_throw cval -> I_throw (cval_subst id subst cval)
        | I_comment str -> I_comment str
        | I_raw str -> I_raw str
        | I_return cval -> I_return (cval_subst id subst cval)
        | I_reset (ctyp, id') -> I_reset (ctyp, id')
        | I_reinit (ctyp, id', cval) -> I_reinit (ctyp, id', cval_subst id subst cval)
      in
      I_aux (instr, aux) :: instrs
  | [] -> []

let rec clexp_subst id subst = function
  | CL_id (id', ctyp) when Name.compare id id' = 0 -> subst
  | CL_id (id', ctyp) -> CL_id (id', ctyp)
  | CL_field (clexp, field) -> CL_field (clexp_subst id subst clexp, field)
  | CL_addr clexp -> CL_addr (clexp_subst id subst clexp)
  | CL_tuple (clexp, n) -> CL_tuple (clexp_subst id subst clexp, n)
  | CL_void -> CL_void
  | CL_rmw _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot substitute into read-modify-write construct"

let rec find_function fid = function
  | CDEF_fundef (fid', heap_return, args, body) :: _ when Id.compare fid fid' = 0 -> Some (heap_return, args, body)
  | cdef :: cdefs -> find_function fid cdefs
  | [] -> None

let ssa_name i = function
  | Name (id, _) -> Name (id, i)
  | Global (id, _) -> Global (id, i)
  | Have_exception _ -> Have_exception i
  | Current_exception _ -> Current_exception i
  | Throw_location _ -> Throw_location i
  | Return _ -> Return i

let inline cdefs should_inline instrs =
  let inlines = ref (-1) in
  let label_count = ref (-1) in

  let replace_return subst = function
    | I_aux (I_funcall (clexp, extern, fid, args), aux) ->
        I_aux (I_funcall (clexp_subst return subst clexp, extern, fid, args), aux)
    | I_aux (I_copy (clexp, cval), aux) -> I_aux (I_copy (clexp_subst return subst clexp, cval), aux)
    | instr -> instr
  in

  let replace_end label = function
    | I_aux (I_end _, aux) -> I_aux (I_goto label, aux)
    | I_aux (I_undefined _, aux) -> I_aux (I_goto label, aux)
    | instr -> instr
  in

  let fix_labels =
    let fix_label l = "inline" ^ string_of_int !label_count ^ "_" ^ l in
    function
    | I_aux (I_goto label, aux) -> I_aux (I_goto (fix_label label), aux)
    | I_aux (I_label label, aux) -> I_aux (I_label (fix_label label), aux)
    | I_aux (I_jump (cval, label), aux) -> I_aux (I_jump (cval, fix_label label), aux)
    | instr -> instr
  in

  let fix_substs =
    let f = cval_map_id (ssa_name (-1)) in
    function
    | I_aux (I_init (ctyp, id, cval), aux) -> I_aux (I_init (ctyp, id, f cval), aux)
    | I_aux (I_jump (cval, label), aux) -> I_aux (I_jump (f cval, label), aux)
    | I_aux (I_funcall (clexp, extern, function_id, args), aux) ->
        I_aux (I_funcall (clexp, extern, function_id, List.map f args), aux)
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) ->
        I_aux (I_if (f cval, then_instrs, else_instrs, ctyp), aux)
    | I_aux (I_copy (clexp, cval), aux) -> I_aux (I_copy (clexp, f cval), aux)
    | I_aux (I_return cval, aux) -> I_aux (I_return (f cval), aux)
    | I_aux (I_throw cval, aux) -> I_aux (I_throw (f cval), aux)
    | instr -> instr
  in

  let inline_instr = function
    | I_aux (I_funcall (clexp, false, function_id, args), aux) as instr when should_inline (fst function_id) -> begin
        match find_function (fst function_id) cdefs with
        | Some (None, ids, body) ->
            incr inlines;
            incr label_count;
            let inline_label = label "end_inline_" in
            (* For situations where we have e.g. x => x' and x' => y, we
               use a dummy SSA number turning this into x => x'/-2 and
               x' => y/-2, ensuring x's won't get turned into y's. This
               is undone by fix_substs which removes the -2 SSA
               numbers. *)
            let args = List.map (cval_map_id (ssa_name (-2))) args in
            let body = List.fold_right2 instrs_subst (List.map name ids) args body in
            let body = List.map (map_instr fix_substs) body in
            let body = List.map (map_instr fix_labels) body in
            let body = List.map (map_instr (replace_end inline_label)) body in
            let body = List.map (map_instr (replace_return clexp)) body in
            I_aux (I_block (body @ [ilabel inline_label]), aux)
        | Some (Some _, ids, body) ->
            (* Some _ is only introduced by C backend, so we don't
               expect it at this point. *)
            raise (Reporting.err_general (snd aux) "Unexpected return method in IR")
        | None -> instr
      end
    | instr -> instr
  in

  let rec go instrs =
    if !inlines <> 0 then begin
      inlines := 0;
      let instrs = List.map (map_instr inline_instr) instrs in
      go instrs
    end
    else instrs
  in
  go instrs

let remove_pointless_goto instrs =
  let rec go acc = function
    | I_aux (I_goto label, _) :: I_aux (I_label label', aux) :: instrs when label = label' ->
        go (I_aux (I_label label', aux) :: acc) instrs
    | I_aux (I_goto label, aux) :: I_aux (I_goto _, _) :: instrs -> go (I_aux (I_goto label, aux) :: acc) instrs
    | instr :: instrs -> go (instr :: acc) instrs
    | [] -> List.rev acc
  in
  go [] instrs

let remove_pointless_exit instrs =
  let rec go acc = function
    | I_aux (I_end id, aux) :: I_aux (I_end _, _) :: instrs -> go (I_aux (I_end id, aux) :: acc) instrs
    | I_aux (I_end id, aux) :: I_aux (I_undefined _, _) :: instrs -> go (I_aux (I_end id, aux) :: acc) instrs
    | instr :: instrs -> go (instr :: acc) instrs
    | [] -> List.rev acc
  in
  go [] instrs

module StringSet = Set.Make (String)

let rec get_used_labels set = function
  | I_aux (I_goto label, _) :: instrs -> get_used_labels (StringSet.add label set) instrs
  | I_aux (I_jump (_, label), _) :: instrs -> get_used_labels (StringSet.add label set) instrs
  | _ :: instrs -> get_used_labels set instrs
  | [] -> set

let remove_unused_labels instrs =
  let used = get_used_labels StringSet.empty instrs in
  let rec go acc = function
    | I_aux (I_label label, _) :: instrs when not (StringSet.mem label used) -> go acc instrs
    | instr :: instrs -> go (instr :: acc) instrs
    | [] -> List.rev acc
  in
  go [] instrs

let remove_dead_after_goto instrs =
  let rec go acc = function
    | (I_aux (I_goto _, _) as instr) :: instrs -> go_dead (instr :: acc) instrs
    | instr :: instrs -> go (instr :: acc) instrs
    | [] -> acc
  and go_dead acc = function
    | (I_aux (I_label _, _) as instr) :: instrs -> go (instr :: acc) instrs
    | instr :: instrs -> go acc instrs
    | [] -> acc
  in
  List.rev (go [] instrs)

let rec remove_dead_code instrs =
  let instrs' =
    instrs |> remove_unused_labels |> remove_pointless_goto |> remove_dead_after_goto |> remove_pointless_exit
  in
  if List.length instrs' < List.length instrs then remove_dead_code instrs' else instrs'

let rec remove_clear = function
  | I_aux (I_clear _, _) :: instrs -> remove_clear instrs
  | instr :: instrs -> instr :: remove_clear instrs
  | [] -> []

let remove_tuples cdefs ctx =
  let already_removed = ref CTSet.empty in
  let rec all_tuples = function
    | CT_tup ctyps as ctyp -> CTSet.add ctyp (List.fold_left CTSet.union CTSet.empty (List.map all_tuples ctyps))
    | CT_struct (_, id_ctyps) | CT_variant (_, id_ctyps) ->
        List.fold_left (fun cts (_, ctyp) -> CTSet.union (all_tuples ctyp) cts) CTSet.empty id_ctyps
    | CT_list ctyp | CT_vector (_, ctyp) | CT_fvector (_, _, ctyp) | CT_ref ctyp -> all_tuples ctyp
    | CT_lint | CT_fint _ | CT_lbits _ | CT_sbits _ | CT_fbits _ | CT_constant _ | CT_float _ | CT_unit | CT_bool
    | CT_real | CT_bit | CT_poly _ | CT_string | CT_enum _ | CT_rounding_mode ->
        CTSet.empty
  in
  let rec tuple_depth = function
    | CT_tup ctyps -> 1 + List.fold_left (fun d ctyp -> max d (tuple_depth ctyp)) 0 ctyps
    | CT_struct (_, id_ctyps) | CT_variant (_, id_ctyps) ->
        List.fold_left (fun d (_, ctyp) -> max (tuple_depth ctyp) d) 0 id_ctyps
    | CT_list ctyp | CT_vector (_, ctyp) | CT_fvector (_, _, ctyp) | CT_ref ctyp -> tuple_depth ctyp
    | CT_lint | CT_fint _ | CT_lbits _ | CT_sbits _ | CT_fbits _ | CT_constant _ | CT_unit | CT_bool | CT_real | CT_bit
    | CT_poly _ | CT_string | CT_enum _ | CT_float _ | CT_rounding_mode ->
        0
  in
  let rec fix_tuples = function
    | CT_tup ctyps ->
        let ctyps = List.map fix_tuples ctyps in
        let name = "tuple#" ^ Util.string_of_list "_" string_of_ctyp ctyps in
        CT_struct (mk_id name, List.mapi (fun n ctyp -> (mk_id (name ^ string_of_int n), ctyp)) ctyps)
    | CT_struct (id, id_ctyps) -> CT_struct (id, List.map (fun (id, ctyp) -> (id, fix_tuples ctyp)) id_ctyps)
    | CT_variant (id, id_ctyps) -> CT_variant (id, List.map (fun (id, ctyp) -> (id, fix_tuples ctyp)) id_ctyps)
    | CT_list ctyp -> CT_list (fix_tuples ctyp)
    | CT_vector (d, ctyp) -> CT_vector (d, fix_tuples ctyp)
    | CT_fvector (n, d, ctyp) -> CT_fvector (n, d, fix_tuples ctyp)
    | CT_ref ctyp -> CT_ref (fix_tuples ctyp)
    | ( CT_lint | CT_fint _ | CT_lbits _ | CT_sbits _ | CT_fbits _ | CT_constant _ | CT_float _ | CT_unit | CT_bool
      | CT_real | CT_bit | CT_poly _ | CT_string | CT_enum _ | CT_rounding_mode ) as ctyp ->
        ctyp
  and fix_cval = function
    | V_id (id, ctyp) -> V_id (id, ctyp)
    | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
    | V_ctor_kind (cval, ctor, ctyp) -> V_ctor_kind (fix_cval cval, ctor, ctyp)
    | V_ctor_unwrap (cval, ctor, ctyp) -> V_ctor_unwrap (fix_cval cval, ctor, ctyp)
    | V_tuple_member (cval, _, n) ->
        let ctyp = fix_tuples (cval_ctyp cval) in
        let cval = fix_cval cval in
        let field =
          match ctyp with CT_struct (id, _) -> mk_id (string_of_id id ^ string_of_int n) | _ -> assert false
        in
        V_field (cval, field)
    | V_call (op, cvals) -> V_call (op, List.map fix_cval cvals)
    | V_field (cval, field) -> V_field (fix_cval cval, field)
    | V_struct (fields, ctyp) -> V_struct (List.map (fun (id, cval) -> (id, fix_cval cval)) fields, ctyp)
    | V_tuple (members, ctyp) -> begin
        match ctyp with
        | CT_tup ctyps ->
            let ctyps = List.map fix_tuples ctyps in
            let name = "tuple#" ^ Util.string_of_list "_" string_of_ctyp ctyps in
            let struct_ctyp =
              CT_struct (mk_id name, List.mapi (fun n ctyp -> (mk_id (name ^ string_of_int n), ctyp)) ctyps)
            in
            V_struct (List.mapi (fun n member -> (mk_id (name ^ string_of_int n), fix_cval member)) members, struct_ctyp)
        | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Tuple without tuple type"
      end
  in
  let rec fix_clexp = function
    | CL_id (id, ctyp) -> CL_id (id, ctyp)
    | CL_addr clexp -> CL_addr (fix_clexp clexp)
    | CL_tuple (clexp, n) ->
        let ctyp = fix_tuples (clexp_ctyp clexp) in
        let clexp = fix_clexp clexp in
        let field =
          match ctyp with CT_struct (id, _) -> mk_id (string_of_id id ^ string_of_int n) | _ -> assert false
        in
        CL_field (clexp, field)
    | CL_field (clexp, field) -> CL_field (fix_clexp clexp, field)
    | CL_void -> CL_void
    | CL_rmw (read, write, ctyp) -> CL_rmw (read, write, ctyp)
  in
  let rec fix_instr_aux = function
    | I_funcall (clexp, extern, id, args) -> I_funcall (fix_clexp clexp, extern, id, List.map fix_cval args)
    | I_copy (clexp, cval) -> I_copy (fix_clexp clexp, fix_cval cval)
    | I_init (ctyp, id, cval) -> I_init (ctyp, id, fix_cval cval)
    | I_reinit (ctyp, id, cval) -> I_reinit (ctyp, id, fix_cval cval)
    | I_jump (cval, label) -> I_jump (fix_cval cval, label)
    | I_throw cval -> I_throw (fix_cval cval)
    | I_return cval -> I_return (fix_cval cval)
    | I_if (cval, then_instrs, else_instrs, ctyp) ->
        I_if (fix_cval cval, List.map fix_instr then_instrs, List.map fix_instr else_instrs, ctyp)
    | I_block instrs -> I_block (List.map fix_instr instrs)
    | I_try_block instrs -> I_try_block (List.map fix_instr instrs)
    | ( I_goto _ | I_label _ | I_decl _ | I_clear _ | I_end _ | I_comment _ | I_reset _ | I_undefined _ | I_exit _
      | I_raw _ ) as instr ->
        instr
  and fix_instr (I_aux (instr, aux)) = I_aux (fix_instr_aux instr, aux) in
  let fix_conversions = function
    | I_aux (I_copy (clexp, cval), (_, l)) as instr -> begin
        match (clexp_ctyp clexp, cval_ctyp cval) with
        | CT_tup lhs_ctyps, CT_tup rhs_ctyps when List.length lhs_ctyps = List.length rhs_ctyps ->
            let elems = List.length lhs_ctyps in
            if List.for_all2 ctyp_equal lhs_ctyps rhs_ctyps then [instr]
            else List.mapi (fun n _ -> icopy l (CL_tuple (clexp, n)) (V_tuple_member (cval, elems, n))) lhs_ctyps
        | _ -> [instr]
      end
    | instr -> [instr]
  in
  let fix_ctx ctx =
    {
      ctx with
      records = Bindings.map (fun (params, fields) -> (params, Bindings.map fix_tuples fields)) ctx.records;
      variants = Bindings.map (fun (params, ctors) -> (params, Bindings.map fix_tuples ctors)) ctx.variants;
      valspecs =
        Bindings.map (fun (extern, ctyps, ctyp) -> (extern, List.map fix_tuples ctyps, fix_tuples ctyp)) ctx.valspecs;
      locals = Bindings.map (fun (mut, ctyp) -> (mut, fix_tuples ctyp)) ctx.locals;
    }
  in
  let to_struct = function
    | CT_tup ctyps ->
        let ctyps = List.map fix_tuples ctyps in
        let name = "tuple#" ^ Util.string_of_list "_" string_of_ctyp ctyps in
        let fields = List.mapi (fun n ctyp -> (mk_id (name ^ string_of_int n), ctyp)) ctyps in
        [
          CDEF_type (CTD_struct (mk_id name, fields));
          CDEF_pragma
            ( "tuplestruct",
              Util.string_of_list " "
                (fun x -> x)
                (Util.zencode_string name :: List.map (fun (id, _) -> Util.zencode_string (string_of_id id)) fields)
            );
        ]
    | _ -> assert false
  in
  let rec go acc = function
    | cdef :: cdefs ->
        let tuples = CTSet.fold (fun ctyp -> CTSet.union (all_tuples ctyp)) (cdef_ctyps cdef) CTSet.empty in
        let tuples = CTSet.diff tuples !already_removed in
        (* In the case where we have ((x, y), z) and (x, y) we need to
           generate (x, y) first, so we sort by the depth of nesting in
           the tuples (note we build acc in reverse order) *)
        let sorted_tuples =
          CTSet.elements tuples
          |> List.map (fun ctyp -> (tuple_depth ctyp, ctyp))
          |> List.sort (fun (d1, _) (d2, _) -> compare d2 d1)
          |> List.map snd
        in
        let structs = List.concat (List.map to_struct sorted_tuples) in
        already_removed := CTSet.union tuples !already_removed;
        let cdef =
          cdef |> cdef_concatmap_instr fix_conversions |> cdef_map_instr fix_instr |> cdef_map_ctyp fix_tuples
        in
        go ((cdef :: structs) @ acc) cdefs
    | [] -> List.rev acc
  in
  (go [] cdefs, fix_ctx ctx)

let structure_control_flow_block instrs =
  let rec labels_in_block = function
    | I_aux (I_label label, (_, l)) :: instrs -> (label, l) :: labels_in_block instrs
    | _ :: instrs -> labels_in_block instrs
    | [] -> []
  in

  let label_var label = "goto_" ^ label |> mk_id |> name in

  let guard_condition guarded =
    match NameSet.elements guarded with
    | [] -> None
    | guarded -> Some (V_call (Bnot, [V_call (Bor, List.map (fun name -> V_id (name, CT_bool)) guarded)]))
  in

  (* Find new labels in this block and create boolean variables for them *)
  let new_labels = labels_in_block instrs in
  let label_variables =
    List.map
      (fun (label, l) ->
        (label, iinit (gen_loc l) CT_bool (name (mk_id ("goto_" ^ label))) (V_lit (VL_bool false, CT_bool)))
      )
      new_labels
  in

  let rec split_after_jump (instrs : instr list) =
    match instrs with
    | [] -> ([], [])
    | (I_aux (I_goto _, _) | I_aux (I_jump _, _) | I_aux (I_label _, _) | I_aux (I_decl _, _) | I_aux (I_init _, _))
      :: _ as instrs ->
        ([], instrs)
    | instr :: instrs ->
        let prefix, suffix = split_after_jump instrs in
        (instr :: prefix, suffix)
  in

  let iguard l guarded = function
    | [] -> icomment "nop"
    | instrs -> (
        match guard_condition guarded with None -> iblock instrs | Some cond -> iif l cond instrs [] CT_unit
      )
  in

  let rec fix_block guarded = function
    | [] -> []
    | (I_aux ((I_decl _ | I_init _), (_, l)) as instr) :: instrs ->
        let after_decl, rest = split_after_jump instrs in
        instr :: iguard l guarded after_decl :: fix_block guarded rest
    | I_aux (I_goto label, (_, l)) :: instrs ->
        let v = label_var label in
        let set_goto = iguard l guarded [icopy l (CL_id (v, CT_bool)) (V_lit (VL_bool true, CT_bool))] in
        let guarded = NameSet.add v guarded in
        let after_jump, rest = split_after_jump instrs in
        set_goto :: iguard l guarded after_jump :: fix_block guarded rest
    | I_aux (I_label label, (_, l)) :: instrs ->
        let v = label_var label in
        let guarded = NameSet.remove v guarded in
        let after_label, rest = split_after_jump instrs in
        icomment label :: iguard l guarded after_label :: fix_block guarded rest
    | I_aux (I_jump (cond, label), (_, l)) :: instrs ->
        let v = label_var label in
        let set_goto =
          iguard l guarded
            [
              iif l cond
                [icopy l (CL_id (v, CT_bool)) (V_lit (VL_bool true, CT_bool))]
                [icopy l (CL_id (v, CT_bool)) (V_lit (VL_bool false, CT_bool))]
                CT_unit;
            ]
        in
        let guarded = NameSet.add v guarded in
        let after_jump, rest = split_after_jump instrs in
        set_goto :: iguard l guarded after_jump :: fix_block guarded rest
    | instr :: instrs -> instr :: fix_block guarded instrs
  in

  List.map snd label_variables @ fix_block NameSet.empty instrs
