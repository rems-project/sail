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

open Ast_util
open Jib
open Jib_util

let optimize_unit instrs =
  let unit_cval cval =
    match cval_ctyp cval with
    | CT_unit -> (V_lit (VL_unit, CT_unit))
    | _ -> cval
  in
  let unit_instr = function
    | I_aux (I_funcall (clexp, extern, id, args), annot) as instr ->
       begin match clexp_ctyp clexp with
       | CT_unit ->
          I_aux (I_funcall (CL_void, extern, id, List.map unit_cval args), annot)
       | _ -> instr
       end
    | I_aux (I_copy (clexp, cval), annot) as instr ->
       begin match clexp_ctyp clexp with
       | CT_unit ->
          I_aux (I_copy (CL_void, unit_cval cval), annot)
       | _ -> instr
       end
    | instr -> instr
  in
  let non_pointless_copy (I_aux (aux, annot)) =
    match aux with
    | I_copy (CL_void, _) -> false
    | _ -> true
  in
  filter_instrs non_pointless_copy (map_instr_list unit_instr instrs)

let flat_counter = ref 0
let flat_id orig_id =
  let id = mk_id (string_of_name ~zencode:false orig_id ^ "_l#" ^ string_of_int !flat_counter) in
  incr flat_counter;
  name id

let rec flatten_instrs = function
  | I_aux (I_decl (ctyp, decl_id), aux) :: instrs ->
     let fid = flat_id decl_id in
     I_aux (I_decl (ctyp, fid), aux) :: flatten_instrs (instrs_rename decl_id fid instrs)

  | I_aux (I_init (ctyp, decl_id, cval), aux) :: instrs ->
     let fid = flat_id decl_id in
     I_aux (I_init (ctyp, fid, cval), aux) :: flatten_instrs (instrs_rename decl_id fid instrs)

  | I_aux ((I_block block | I_try_block block), _) :: instrs ->
     flatten_instrs block @ flatten_instrs instrs

  | I_aux (I_if (cval, then_instrs, else_instrs, _), _) :: instrs ->
     let then_label = label "then_" in
     let endif_label = label "endif_" in
     [ijump cval then_label]
     @ flatten_instrs else_instrs
     @ [igoto endif_label]
     @ [ilabel then_label]
     @ flatten_instrs then_instrs
     @ [ilabel endif_label]
     @ flatten_instrs instrs

  | I_aux (I_comment _, _) :: instrs -> flatten_instrs instrs

  | instr :: instrs -> instr :: flatten_instrs instrs
  | [] -> []

let flatten_cdef =
  function
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
    | I_aux (I_block instrs, aux) :: rest ->
       I_aux (I_block (unique_instrs i instrs), aux) :: unique_instrs i rest
    | I_aux (I_try_block instrs, aux) :: rest ->
       I_aux (I_try_block (unique_instrs i instrs), aux) :: unique_instrs i rest
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: rest ->
       I_aux (I_if (cval, unique_instrs i then_instrs, unique_instrs i else_instrs, ctyp), aux) :: unique_instrs i rest
    | instr :: instrs -> instr :: unique_instrs i instrs
    | [] -> []
  in
  let unique_cdef i = function
    | CDEF_reg_dec (id, ctyp, instrs) -> CDEF_reg_dec (id, ctyp, unique_instrs i instrs)
    | CDEF_type ctd -> CDEF_type ctd
    | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, unique_instrs i instrs)
    | CDEF_spec (id, ctyps, ctyp) -> CDEF_spec (id, ctyps, ctyp)
    | CDEF_mapping_spec (id, ctyps, left_ctyp, right_ctyp) -> CDEF_mapping_spec (id, ctyps, left_ctyp, right_ctyp)
    | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, unique_instrs i instrs)
    | CDEF_startup (id, instrs) -> CDEF_startup (id, unique_instrs i instrs)
    | CDEF_finish (id, instrs) -> CDEF_finish (id, unique_instrs i instrs)
  in
  List.mapi unique_cdef cdefs

let rec cval_subst id subst = function
  | V_id (id', ctyp) -> if Name.compare id id' = 0 then subst else V_id (id', ctyp)
  | V_ref (reg_id, ctyp) -> V_ref (reg_id, ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
  | V_call (op, cvals) -> V_call (op, List.map (cval_subst id subst) cvals)
  | V_field (cval, field) -> V_field (cval_subst id subst cval, field)
  | V_tuple_member (cval, len, n) -> V_tuple_member (cval_subst id subst cval, len, n)
  | V_ctor_kind (cval, ctor, unifiers, ctyp) -> V_ctor_kind (cval_subst id subst cval, ctor, unifiers, ctyp)
  | V_ctor_unwrap (ctor, cval, unifiers, ctyp) -> V_ctor_unwrap (ctor, cval_subst id subst cval, unifiers, ctyp)
  | V_struct (fields, ctyp) -> V_struct (List.map (fun (field, cval) -> field, cval_subst id subst cval) fields, ctyp)
  | V_poly (cval, ctyp) -> V_poly (cval_subst id subst cval, ctyp)

let rec cval_map_id f = function
  | V_id (id, ctyp) -> V_id (f id, ctyp)
  | V_ref (id, ctyp) -> V_ref (f id, ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
  | V_call (call, cvals) -> V_call (call, List.map (cval_map_id f) cvals)
  | V_field (cval, field) -> V_field (cval_map_id f cval, field)
  | V_tuple_member (cval, len, n) -> V_tuple_member (cval_map_id f cval, len, n)
  | V_ctor_kind (cval, ctor, unifiers, ctyp) -> V_ctor_kind (cval_map_id f cval, ctor, unifiers, ctyp)
  | V_ctor_unwrap (ctor, cval, unifiers, ctyp) -> V_ctor_unwrap (ctor, cval_map_id f cval, unifiers, ctyp)
  | V_struct (fields, ctyp) ->
     V_struct (List.map (fun (field, cval) -> field, cval_map_id f cval) fields, ctyp)
  | V_poly (cval, ctyp) -> V_poly (cval_map_id f cval, ctyp)

let rec instrs_subst id subst =
  function
  | (I_aux (I_decl (_, id'), _) :: _) as instrs when Name.compare id id' = 0 ->
     instrs

  | I_aux (I_init (ctyp, id', cval), aux) :: rest when Name.compare id id' = 0 ->
     I_aux (I_init (ctyp, id', cval_subst id subst cval), aux) :: rest

  | (I_aux (I_reset (_, id'), _) :: _) as instrs when Name.compare id id' = 0 ->
     instrs

  | I_aux (I_reinit (ctyp, id', cval), aux) :: rest when Name.compare id id' = 0 ->
     I_aux (I_reinit (ctyp, id', cval_subst id subst cval), aux) :: rest

  | I_aux (instr, aux) :: instrs ->
     let instrs = instrs_subst id subst instrs in
     let instr = match instr with
       | I_decl (ctyp, id') -> I_decl (ctyp, id')
       | I_init (ctyp, id', cval) -> I_init (ctyp, id', cval_subst id subst cval)
       | I_jump (cval, label) -> I_jump (cval_subst id subst cval, label)
       | I_goto label -> I_goto label
       | I_label label -> I_label label
       | I_funcall (clexp, extern, fid, args) -> I_funcall (clexp, extern, fid, List.map (cval_subst id subst) args)
       | I_mapcall (clexp, mid, args, label) -> I_mapcall (clexp, mid, List.map (cval_subst id subst) args, label)
       | I_copy (clexp, cval) -> I_copy (clexp, cval_subst id subst cval)
       | I_clear (clexp, id') -> I_clear (clexp, id')
       | I_undefined ctyp -> I_undefined ctyp
       | I_match_failure -> I_match_failure
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
  | CDEF_fundef (fid', heap_return, args, body) :: _ when Id.compare fid fid' = 0 ->
     Some (heap_return, args, body)

  | cdef :: cdefs -> find_function fid cdefs

  | [] -> None

let ssa_name i = function
  | Name (id, _) -> Name (id, i)
  | Have_exception _ -> Have_exception i
  | Current_exception _ -> Current_exception i
  | Return _ -> Return i

let inline cdefs should_inline instrs =
  let inlines = ref (-1) in
  let label_count = ref (-1) in

  let replace_return subst = function
    | I_aux (I_funcall (clexp, extern, fid, args), aux) ->
       I_aux (I_funcall (clexp_subst return subst clexp, extern, fid, args), aux)
    | I_aux (I_copy (clexp, cval), aux) ->
       I_aux (I_copy (clexp_subst return subst clexp, cval), aux)
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
    | I_aux (I_init (ctyp, id, cval), aux) ->
       I_aux (I_init (ctyp, id, f cval), aux)
    | I_aux (I_jump (cval, label), aux) ->
       I_aux (I_jump (f cval, label), aux)
    | I_aux (I_funcall (clexp, extern, function_id, args), aux) ->
       I_aux (I_funcall (clexp, extern, function_id, List.map f args), aux)
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) ->
       I_aux (I_if (f cval, then_instrs, else_instrs, ctyp), aux)
    | I_aux (I_copy (clexp, cval), aux) ->
       I_aux (I_copy (clexp, f cval), aux)
    | I_aux (I_return cval, aux) ->
       I_aux (I_return (f cval), aux)
    | I_aux (I_throw cval, aux) ->
       I_aux (I_throw (f cval), aux)
    | instr -> instr
  in

  let rec inline_instr = function
    | I_aux (I_funcall (clexp, false, function_id, args), aux) as instr when should_inline function_id ->
       begin match find_function function_id cdefs with
       | Some (CC_stack, ids, body) ->
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
       | Some (CC_heap _, ids, body) ->
          (* CC_heap is only introduced by C backend, so we don't
             expect it at this point. *)
          raise (Reporting.err_general (snd aux) "Unexpected calling convention in IR")
       | None -> instr
       end
    | instr -> instr
  in

  let rec go instrs =
    if !inlines <> 0 then
      begin
        inlines := 0;
        let instrs = List.map (map_instr inline_instr) instrs in
        go instrs
      end
    else
      instrs
  in
  go instrs

let rec remove_pointless_goto = function
  | I_aux (I_goto label, _) :: I_aux (I_label label', aux) :: instrs when label = label' ->
     I_aux (I_label label', aux) :: remove_pointless_goto instrs
  | I_aux (I_goto label, aux) :: I_aux (I_goto _, _) :: instrs ->
     I_aux (I_goto label, aux) :: remove_pointless_goto instrs
  | instr :: instrs ->
     instr :: remove_pointless_goto instrs
  | [] -> []

module StringSet = Set.Make(String)

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

let rec remove_clear = function
  | I_aux (I_clear _, _) :: instrs -> remove_clear instrs
  | instr :: instrs -> instr :: remove_clear instrs
  | [] -> []
