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
    | CT_unit -> (F_lit V_unit, CT_unit)
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
    | I_aux (I_alias (clexp, cval), annot) as instr ->
       begin match clexp_ctyp clexp with
       | CT_unit ->
          I_aux (I_alias (CL_void, unit_cval cval), annot)
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
let flat_id () =
  let id = mk_id ("local#" ^ string_of_int !flat_counter) in
  incr flat_counter;
  name id

let rec flatten_instrs = function
  | I_aux (I_decl (ctyp, decl_id), aux) :: instrs ->
     let fid = flat_id () in
     I_aux (I_decl (ctyp, fid), aux) :: flatten_instrs (instrs_rename decl_id fid instrs)

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
