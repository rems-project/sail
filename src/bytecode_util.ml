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
open Value2
open PPrint

(* Define wrappers for creating bytecode instructions. Each function
   uses a counter to assign each instruction a unique identifier. *)

let instr_counter = ref 0

let instr_number () =
  let n = !instr_counter in
  incr instr_counter;
  n

let idecl ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_decl (ctyp, id), (instr_number (), l))

let ireset ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_reset (ctyp, id), (instr_number (), l))

let iinit ?loc:(l=Parse_ast.Unknown) ctyp id cval =
  I_aux (I_init (ctyp, id, cval), (instr_number (), l))

let iif ?loc:(l=Parse_ast.Unknown) cval then_instrs else_instrs ctyp =
  I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (instr_number (), l))

let ifuncall ?loc:(l=Parse_ast.Unknown) clexp id cvals =
  I_aux (I_funcall (clexp, false, id, cvals), (instr_number (), l))

let iextern ?loc:(l=Parse_ast.Unknown) clexp id cvals =
  I_aux (I_funcall (clexp, true, id, cvals), (instr_number (), l))

let icopy l clexp cval =
  I_aux (I_copy (clexp, cval), (instr_number (), l))

let ialias l clexp cval =
  I_aux (I_alias (clexp, cval), (instr_number (), l))

let iclear ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_clear (ctyp, id), (instr_number (), l))

let ireturn ?loc:(l=Parse_ast.Unknown) cval =
  I_aux (I_return cval, (instr_number (), l))

let iblock ?loc:(l=Parse_ast.Unknown) instrs =
  I_aux (I_block instrs, (instr_number (), l))

let itry_block ?loc:(l=Parse_ast.Unknown) instrs =
  I_aux (I_try_block instrs, (instr_number (), l))

let ithrow ?loc:(l=Parse_ast.Unknown) cval =
  I_aux (I_throw cval, (instr_number (), l))
let icomment ?loc:(l=Parse_ast.Unknown) str =
  I_aux (I_comment str, (instr_number (), l))

let ilabel ?loc:(l=Parse_ast.Unknown) label =
  I_aux (I_label label, (instr_number (), l))
let igoto ?loc:(l=Parse_ast.Unknown) label =
  I_aux (I_goto label, (instr_number (), l))

let iundefined ?loc:(l=Parse_ast.Unknown) ctyp =
  I_aux (I_undefined ctyp, (instr_number (), l))

let imatch_failure ?loc:(l=Parse_ast.Unknown) () =
  I_aux (I_match_failure, (instr_number (), l))

let iraw ?loc:(l=Parse_ast.Unknown) str =
  I_aux (I_raw str, (instr_number (), l))

let ijump ?loc:(l=Parse_ast.Unknown) cval label =
  I_aux (I_jump (cval, label), (instr_number (), l))

let rec frag_rename from_id to_id = function
  | F_id id when Id.compare id from_id = 0 -> F_id to_id
  | F_id id -> F_id id
  | F_ref id when Id.compare id from_id = 0 -> F_ref to_id
  | F_ref id -> F_ref id
  | F_lit v -> F_lit v
  | F_have_exception -> F_have_exception
  | F_current_exception -> F_current_exception
  | F_call (call, frags) -> F_call (call, List.map (frag_rename from_id to_id) frags)
  | F_op (f1, op, f2) -> F_op (frag_rename from_id to_id f1, op, frag_rename from_id to_id f2)
  | F_unary (op, f) -> F_unary (op, frag_rename from_id to_id f)
  | F_field (f, field) -> F_field (frag_rename from_id to_id f, field)
  | F_raw raw -> F_raw raw
  | F_poly f -> F_poly (frag_rename from_id to_id f)

let cval_rename from_id to_id (frag, ctyp) = (frag_rename from_id to_id frag, ctyp)

let rec clexp_rename from_id to_id = function
  | CL_id (id, ctyp) when Id.compare id from_id = 0 -> CL_id (to_id, ctyp)
  | CL_id (id, ctyp) -> CL_id (id, ctyp)
  | CL_field (clexp, field) ->
     CL_field (clexp_rename from_id to_id clexp, field)
  | CL_addr clexp ->
     CL_addr (clexp_rename from_id to_id clexp)
  | CL_tuple (clexp, n) ->
     CL_tuple (clexp_rename from_id to_id clexp, n)
  | CL_current_exception ctyp -> CL_current_exception ctyp
  | CL_have_exception -> CL_have_exception

let rec instr_rename from_id to_id (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl (ctyp, id) when Id.compare id from_id = 0 -> I_decl (ctyp, to_id)
    | I_decl (ctyp, id) -> I_decl (ctyp, id)

    | I_init (ctyp, id, cval) when Id.compare id from_id = 0 ->
       I_init (ctyp, to_id, cval_rename from_id to_id cval)
    | I_init (ctyp, id, cval) ->
       I_init (ctyp, id, cval_rename from_id to_id cval)

    | I_if (cval, then_instrs, else_instrs, ctyp2) ->
       I_if (cval_rename from_id to_id cval,
             List.map (instr_rename from_id to_id) then_instrs,
             List.map (instr_rename from_id to_id) else_instrs,
             ctyp2)

    | I_jump (cval, label) -> I_jump (cval_rename from_id to_id cval, label)

    | I_funcall (clexp, extern, id, args) ->
       I_funcall (clexp_rename from_id to_id clexp, extern, id, List.map (cval_rename from_id to_id) args)

    | I_copy (clexp, cval) -> I_copy (clexp_rename from_id to_id clexp, cval_rename from_id to_id cval)
    | I_alias (clexp, cval) -> I_alias (clexp_rename from_id to_id clexp, cval_rename from_id to_id cval)

    | I_clear (ctyp, id) when Id.compare id from_id = 0 -> I_clear (ctyp, to_id)
    | I_clear (ctyp, id) -> I_clear (ctyp, id)

    | I_return cval -> I_return (cval_rename from_id to_id cval)

    | I_block instrs -> I_block (List.map (instr_rename from_id to_id) instrs)

    | I_try_block instrs -> I_try_block (List.map (instr_rename from_id to_id) instrs)

    | I_throw cval -> I_throw (cval_rename from_id to_id cval)

    | I_comment str -> I_comment str

    | I_raw str -> I_raw str

    | I_label label -> I_label label

    | I_goto label -> I_goto label

    | I_undefined ctyp -> I_undefined ctyp

    | I_match_failure -> I_match_failure

    | I_reset (ctyp, id) when Id.compare id from_id = 0 -> I_reset (ctyp, to_id)
    | I_reset (ctyp, id) -> I_reset (ctyp, id)

    | I_reinit (ctyp, id, cval) when Id.compare id from_id = 0 ->
       I_reinit (ctyp, to_id, cval_rename from_id to_id cval)
    | I_reinit (ctyp, id, cval) ->
       I_reinit (ctyp, id, cval_rename from_id to_id cval)
  in
  I_aux (instr, aux)

(**************************************************************************)
(* 1. Instruction pretty printer                                          *)
(**************************************************************************)

let string_of_value = function
  | V_bits [] -> "UINT64_C(0)"
  | V_bits bs -> "UINT64_C(" ^ Sail2_values.show_bitlist bs ^ ")"
  | V_int i -> Big_int.to_string i ^ "l"
  | V_bool true -> "true"
  | V_bool false -> "false"
  | V_null -> "NULL"
  | V_unit -> "UNIT"
  | V_bit Sail2_values.B0 -> "UINT64_C(0)"
  | V_bit Sail2_values.B1 -> "UINT64_C(1)"
  | V_string str -> "\"" ^ str ^ "\""
  | V_ctor_kind str -> "Kind_" ^ Util.zencode_string str
  | _ -> failwith "Cannot convert value to string"

let rec string_of_fragment ?zencode:(zencode=true) = function
  | F_id id when zencode -> Util.zencode_string (string_of_id id)
  | F_id id -> string_of_id id
  | F_ref id when zencode -> "&" ^ Util.zencode_string (string_of_id id)
  | F_ref id -> "&" ^ string_of_id id
  | F_lit v -> string_of_value v
  | F_call (str, frags) ->
     Printf.sprintf "%s(%s)" str (Util.string_of_list ", " (string_of_fragment ~zencode:zencode) frags)
  | F_field (f, field) ->
     Printf.sprintf "%s.%s" (string_of_fragment' ~zencode:zencode f) field
  | F_op (f1, op, f2) ->
     Printf.sprintf "%s %s %s" (string_of_fragment' ~zencode:zencode f1) op (string_of_fragment' ~zencode:zencode f2)
  | F_unary (op, f) ->
     op ^ string_of_fragment' ~zencode:zencode f
  | F_have_exception -> "have_exception"
  | F_current_exception -> "(*current_exception)"
  | F_raw raw -> raw
  | F_poly f -> string_of_fragment ~zencode:zencode f
and string_of_fragment' ?zencode:(zencode=true) f =
  match f with
  | F_op _ | F_unary _ -> "(" ^ string_of_fragment ~zencode:zencode f ^ ")"
  | _ -> string_of_fragment ~zencode:zencode f

(* String representation of ctyps here is only for debugging and
   intermediate language pretty-printer. *)
and string_of_ctyp = function
  | CT_int -> "int"
  | CT_lbits true -> "lbits(dec)"
  | CT_lbits false -> "lbits(inc)"
  | CT_fbits (n, true) -> "fbits(" ^ string_of_int n ^ ", dec)"
  | CT_fbits (n, false) -> "fbits(" ^ string_of_int n ^ ", int)"
  | CT_sbits true -> "sbits(dec)"
  | CT_sbits false -> "sbits(inc)"
  | CT_int64 -> "int64"
  | CT_bit -> "bit"
  | CT_unit -> "unit"
  | CT_bool -> "bool"
  | CT_real -> "real"
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
  | CT_struct (id, _) | CT_enum (id, _) | CT_variant (id, _) -> string_of_id id
  | CT_string -> "string"
  | CT_vector (true, ctyp) -> "vector(dec, " ^ string_of_ctyp ctyp ^ ")"
  | CT_vector (false, ctyp) -> "vector(inc, " ^ string_of_ctyp ctyp ^ ")"
  | CT_list ctyp -> "list(" ^ string_of_ctyp ctyp ^ ")"
  | CT_ref ctyp -> "ref(" ^ string_of_ctyp ctyp ^ ")"
  | CT_poly -> "*"

(** This function is like string_of_ctyp, but recursively prints all
   constructors in variants and structs. Used for debug output. *)
and full_string_of_ctyp = function
  | CT_int -> "int"
  | CT_lbits true -> "lbits(dec)"
  | CT_lbits false -> "lbits(inc)"
  | CT_fbits (n, true) -> "fbits(" ^ string_of_int n ^ ", dec)"
  | CT_fbits (n, false) -> "fbits(" ^ string_of_int n ^ ", int)"
  | CT_sbits true -> "sbits(dec)"
  | CT_sbits false -> "sbits(inc)"
  | CT_int64 -> "int64"
  | CT_bit -> "bit"
  | CT_unit -> "unit"
  | CT_bool -> "bool"
  | CT_real -> "real"
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " full_string_of_ctyp ctyps ^ ")"
  | CT_enum (id, _) -> string_of_id id
  | CT_struct (id, ctors) | CT_variant (id, ctors) ->
     "struct " ^ string_of_id id
     ^ "{ "
     ^ Util.string_of_list ", " (fun (id, ctyp) -> string_of_id id ^ " : " ^ full_string_of_ctyp ctyp) ctors
     ^ "}"
  | CT_string -> "string"
  | CT_vector (true, ctyp) -> "vector(dec, " ^ full_string_of_ctyp ctyp ^ ")"
  | CT_vector (false, ctyp) -> "vector(inc, " ^ full_string_of_ctyp ctyp ^ ")"
  | CT_list ctyp -> "list(" ^ full_string_of_ctyp ctyp ^ ")"
  | CT_ref ctyp -> "ref(" ^ full_string_of_ctyp ctyp ^ ")"
  | CT_poly -> "*"

let rec map_ctyp f = function
  | (CT_int | CT_int64 | CT_lbits _ | CT_fbits _ | CT_sbits _
     | CT_bit | CT_unit | CT_bool | CT_real | CT_string | CT_poly | CT_enum _) as ctyp -> f ctyp
  | CT_tup ctyps -> f (CT_tup (List.map (map_ctyp f) ctyps))
  | CT_ref ctyp -> f (CT_ref (map_ctyp f ctyp))
  | CT_vector (direction, ctyp) -> f (CT_vector (direction, map_ctyp f ctyp))
  | CT_list ctyp -> f (CT_list (map_ctyp f ctyp))
  | CT_struct (id, ctors) -> f (CT_struct (id, List.map (fun (id, ctyp) -> id, map_ctyp f ctyp) ctors))
  | CT_variant (id, ctors) -> f (CT_variant (id, List.map (fun (id, ctyp) -> id, map_ctyp f ctyp) ctors))

let rec ctyp_equal ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_int, CT_int -> true
  | CT_lbits d1, CT_lbits d2 -> d1 = d2
  | CT_sbits d1, CT_sbits d2 -> d1 = d2
  | CT_fbits (m1, d1), CT_fbits (m2, d2) -> m1 = m2 && d1 = d2
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
  | CT_poly, CT_poly -> true
  | _, _ -> false

let rec ctyp_unify ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_tup ctyps1, CT_tup ctyps2 when List.length ctyps1 = List.length ctyps2 ->
     List.concat (List.map2 ctyp_unify ctyps1 ctyps2)

  | CT_vector (b1, ctyp1), CT_vector (b2, ctyp2) when b1 = b2 ->
     ctyp_unify ctyp1 ctyp2

  | CT_list ctyp1, CT_list ctyp2 -> ctyp_unify ctyp1 ctyp2

  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_unify ctyp1 ctyp2

  | CT_poly, _ -> [ctyp2]

  | _, _ when ctyp_equal ctyp1 ctyp2 -> []
  | _, _ -> raise (Invalid_argument "ctyp_unify")

let rec ctyp_suprema = function
  | CT_int -> CT_int
  | CT_lbits d -> CT_lbits d
  | CT_fbits (_, d) -> CT_lbits d
  | CT_sbits d -> CT_lbits d
  | CT_int64 -> CT_int
  | CT_unit -> CT_unit
  | CT_bool -> CT_bool
  | CT_real -> CT_real
  | CT_bit -> CT_bit
  | CT_tup ctyps -> CT_tup (List.map ctyp_suprema ctyps)
  | CT_string -> CT_string
  | CT_enum (id, ids) -> CT_enum (id, ids)
  (* Do we really never want to never call ctyp_suprema on constructor
     fields?  Doing it causes issues for structs (see
     test/c/stack_struct.sail) but it might be wrong to not call it
     for nested variants... *)
  | CT_struct (id, ctors) -> CT_struct (id, ctors)
  | CT_variant (id, ctors) -> CT_variant (id, ctors)
  | CT_vector (d, ctyp) -> CT_vector (d, ctyp_suprema ctyp)
  | CT_list ctyp -> CT_list (ctyp_suprema ctyp)
  | CT_ref ctyp -> CT_ref (ctyp_suprema ctyp)
  | CT_poly -> CT_poly

let rec ctyp_ids = function
  | CT_enum (id, _) -> IdSet.singleton id
  | CT_struct (id, ctors) | CT_variant (id, ctors) ->
     IdSet.add id (List.fold_left (fun ids (_, ctyp) -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctors)
  | CT_tup ctyps -> List.fold_left (fun ids ctyp -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctyps
  | CT_vector (_, ctyp) | CT_list ctyp | CT_ref ctyp -> ctyp_ids ctyp
  | CT_int | CT_int64 | CT_lbits _ | CT_fbits _ | CT_sbits _ | CT_unit
    | CT_bool | CT_real | CT_bit | CT_string | CT_poly -> IdSet.empty

let rec unpoly = function
  | F_poly f -> unpoly f
  | F_call (call, fs) -> F_call (call, List.map unpoly fs)
  | F_field (f, field) -> F_field (unpoly f, field)
  | F_op (f1, op, f2) -> F_op (unpoly f1, op, unpoly f2)
  | F_unary (op, f) -> F_unary (op, unpoly f)
  | f -> f

let rec is_polymorphic = function
  | CT_int | CT_int64 | CT_lbits _ | CT_fbits _ | CT_sbits _ | CT_bit | CT_unit | CT_bool | CT_real | CT_string -> false
  | CT_tup ctyps -> List.exists is_polymorphic ctyps
  | CT_enum _ -> false
  | CT_struct (_, ctors) | CT_variant (_, ctors) -> List.exists (fun (_, ctyp) -> is_polymorphic ctyp) ctors
  | CT_vector (_, ctyp) | CT_list ctyp | CT_ref ctyp -> is_polymorphic ctyp
  | CT_poly -> true

let pp_id id =
  string (string_of_id id)

let pp_ctyp ctyp =
  string (string_of_ctyp ctyp |> Util.yellow |> Util.clear)

let pp_keyword str =
  string ((str |> Util.red |> Util.clear) ^ " ")

let pp_cval (frag, ctyp) =
  string (string_of_fragment ~zencode:false frag) ^^ string " : " ^^ pp_ctyp ctyp

let rec pp_clexp = function
  | CL_id (id, ctyp) -> pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | CL_field (clexp, field) -> parens (pp_clexp clexp) ^^ string "." ^^ string field
  | CL_tuple (clexp, n) -> parens (pp_clexp clexp) ^^ string "." ^^ string (string_of_int n)
  | CL_addr clexp -> string "*" ^^ pp_clexp clexp
  | CL_current_exception ctyp -> string "current_exception : " ^^ pp_ctyp ctyp
  | CL_have_exception -> string "have_exception"

let rec pp_instr ?short:(short=false) (I_aux (instr, aux)) =
  match instr with
  | I_decl (ctyp, id) ->
     pp_keyword "var" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | I_if (cval, then_instrs, else_instrs, ctyp) ->
     let pp_if_block = function
       | [] -> string "{}"
       | instrs -> surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     in
     parens (pp_ctyp ctyp) ^^ space
     ^^ pp_keyword "if" ^^ pp_cval cval
     ^^ if short then
          empty
        else
          pp_keyword " then" ^^ pp_if_block then_instrs
          ^^ pp_keyword " else" ^^ pp_if_block else_instrs
  | I_jump (cval, label) ->
     pp_keyword "jump" ^^ pp_cval cval ^^ space ^^ string (label |> Util.blue |> Util.clear)
  | I_block instrs ->
     surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
  | I_try_block instrs ->
     pp_keyword "try" ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
  | I_reset (ctyp, id) ->
     pp_keyword "recreate" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | I_init (ctyp, id, cval) ->
     pp_keyword "create" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp ^^ string " = " ^^ pp_cval cval
  | I_reinit (ctyp, id, cval) ->
     pp_keyword "recreate" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp ^^ string " = " ^^ pp_cval cval
  | I_funcall (x, _, f, args) ->
     separate space [ pp_clexp x; string "=";
                      string (string_of_id f |> Util.green |> Util.clear) ^^ parens (separate_map (string ", ") pp_cval args) ]
  | I_copy (clexp, cval) ->
     separate space [pp_clexp clexp; string "="; pp_cval cval]
  | I_alias (clexp, cval) ->
     pp_keyword "alias" ^^ separate space [pp_clexp clexp; string "="; pp_cval cval]
  | I_clear (ctyp, id) ->
     pp_keyword "kill" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | I_return cval ->
     pp_keyword "return" ^^ pp_cval cval
  | I_throw cval ->
     pp_keyword "throw" ^^ pp_cval cval
  | I_comment str ->
     string ("// " ^ str |> Util.magenta |> Util.clear)
  | I_label str ->
     string (str |> Util.blue |> Util.clear) ^^ string ":"
  | I_goto str ->
     pp_keyword "goto" ^^ string (str |> Util.blue |> Util.clear)
  | I_match_failure ->
     pp_keyword "match_failure"
  | I_undefined ctyp ->
     pp_keyword "undefined" ^^ pp_ctyp ctyp
  | I_raw str ->
     pp_keyword "C" ^^ string (str |> Util.cyan |> Util.clear)

let pp_ctype_def = function
  | CTD_enum (id, ids) ->
     pp_keyword "enum" ^^ pp_id id ^^ string " = "
     ^^ separate_map (string " | ") pp_id ids
  | CTD_struct (id, fields) ->
     pp_keyword "struct" ^^ pp_id id ^^ string " = "
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) (fun (id, ctyp) -> pp_id id ^^ string " : " ^^ pp_ctyp ctyp) fields) rbrace
  | CTD_variant (id, ctors) ->
     pp_keyword "union" ^^ pp_id id ^^ string " = "
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) (fun (id, ctyp) -> pp_id id ^^ string " : " ^^ pp_ctyp ctyp) ctors) rbrace

let pp_cdef = function
  | CDEF_spec (id, ctyps, ctyp) ->
     pp_keyword "val" ^^ pp_id id ^^ string " : " ^^ parens (separate_map (comma ^^ space) pp_ctyp ctyps) ^^ string " -> " ^^ pp_ctyp ctyp
     ^^ hardline
  | CDEF_fundef (id, ret, args, instrs) ->
     let ret = match ret with
       | None -> empty
       | Some id -> space ^^ pp_id id
     in
     pp_keyword "function" ^^ pp_id id ^^ ret ^^ parens (separate_map (comma ^^ space) pp_id args) ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline
  | CDEF_reg_dec (id, ctyp, instrs) ->
     pp_keyword "register" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline
  | CDEF_type tdef -> pp_ctype_def tdef ^^ hardline
  | CDEF_let (n, bindings, instrs) ->
     let pp_binding (id, ctyp) = pp_id id ^^ string " : " ^^ pp_ctyp ctyp in
     pp_keyword "let" ^^ string (string_of_int n) ^^ parens (separate_map (comma ^^ space) pp_binding bindings) ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace ^^ space
     ^^ hardline
  | CDEF_startup (id, instrs)->
     pp_keyword "startup" ^^ pp_id id ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline
  | CDEF_finish (id, instrs)->
     pp_keyword "finish" ^^ pp_id id ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline

(**************************************************************************)
(* 2. Dependency Graphs                                                   *)
(**************************************************************************)

type graph_node =
  | G_id of id
  | G_label of string
  | G_instr of int * instr
  | G_start

let string_of_node = function
  | G_id id -> string_of_id id
  | G_label label -> label
  | G_instr (n, instr) -> string_of_int n ^ ": " ^ Pretty_print_sail.to_string (pp_instr ~short:true instr)
  | G_start -> "START"

module Node = struct
  type t = graph_node
  let compare gn1 gn2 =
    match gn1, gn2 with
    | G_id id1, G_id id2 -> Id.compare id1 id2
    | G_label str1, G_label str2 -> String.compare str1 str2
    | G_instr (n1, _), G_instr (n2, _) -> compare n1 n2
    | G_start  , _         -> 1
    | _        , G_start   -> -1
    | G_instr _, _         -> 1
    | _        , G_instr _ -> -1
    | G_id _   , _         -> 1
    | _        , G_id _    -> -1
end

module NM = Map.Make(Node)
module NS = Set.Make(Node)

type dep_graph = NS.t NM.t

let rec fragment_deps = function
  | F_id id | F_ref id -> NS.singleton (G_id id)
  | F_lit _ -> NS.empty
  | F_field (frag, _) | F_unary (_, frag) | F_poly frag -> fragment_deps frag
  | F_call (_, frags) -> List.fold_left NS.union NS.empty (List.map fragment_deps frags)
  | F_op (frag1, _, frag2) -> NS.union (fragment_deps frag1) (fragment_deps frag2)
  | F_current_exception -> NS.empty
  | F_have_exception -> NS.empty
  | F_raw _ -> NS.empty

let cval_deps = function (frag, _) -> fragment_deps frag

let rec clexp_deps = function
  | CL_id (id, _) -> NS.singleton (G_id id)
  | CL_field (clexp, _) -> clexp_deps clexp
  | CL_tuple (clexp, _) -> clexp_deps clexp
  | CL_addr clexp -> clexp_deps clexp
  | CL_have_exception -> NS.empty
  | CL_current_exception _ -> NS.empty

(** Return the direct, non program-order dependencies of a single
   instruction **)
let instr_deps = function
  | I_decl (ctyp, id) -> NS.empty, NS.singleton (G_id id)
  | I_reset (ctyp, id) -> NS.empty, NS.singleton (G_id id)
  | I_init (ctyp, id, cval) | I_reinit (ctyp, id, cval) -> cval_deps cval, NS.singleton (G_id id)
  | I_if (cval, _, _, _) -> cval_deps cval, NS.empty
  | I_jump (cval, label) -> cval_deps cval, NS.singleton (G_label label)
  | I_funcall (clexp, _, _, cvals) -> List.fold_left NS.union NS.empty (List.map cval_deps cvals), clexp_deps clexp
  | I_copy (clexp, cval) -> cval_deps cval, clexp_deps clexp
  | I_alias (clexp, cval) -> cval_deps cval, clexp_deps clexp
  | I_clear (_, id) -> NS.singleton (G_id id), NS.singleton (G_id id)
  | I_throw cval | I_return cval -> cval_deps cval, NS.empty
  | I_block _ | I_try_block _ -> NS.empty, NS.empty
  | I_comment _ | I_raw _ -> NS.empty, NS.empty
  | I_label label -> NS.singleton (G_label label), NS.empty
  | I_goto label -> NS.empty, NS.singleton (G_label label)
  | I_undefined _ -> NS.empty, NS.empty
  | I_match_failure -> NS.empty, NS.empty

let add_link from_node to_node graph =
  try
    NM.add from_node (NS.add to_node (NM.find from_node graph)) graph
  with
  | Not_found -> NM.add from_node (NS.singleton to_node) graph

let leaves graph =
  List.fold_left (fun acc (from_node, to_nodes) -> NS.filter (fun to_node -> Node.compare to_node from_node != 0) (NS.union acc to_nodes))
                 NS.empty
                 (NM.bindings graph)

(* Ensure that all leaves exist in the graph *)
let fix_leaves graph =
  NS.fold (fun leaf graph -> if NM.mem leaf graph then graph else NM.add leaf NS.empty graph) (leaves graph) graph

let instrs_graph instrs =
  let icounter = ref 0 in
  let graph = ref NM.empty in

  let rec add_instr last_instr (I_aux (instr, _) as iaux) =
    incr icounter;
    let node = G_instr (!icounter, iaux) in
    match instr with
    | I_block instrs | I_try_block instrs ->
       List.fold_left add_instr last_instr instrs
    | I_if (_, then_instrs, else_instrs, _) ->
       begin
         let inputs, _ = instr_deps instr in (* if has no outputs *)
         graph := add_link last_instr node !graph;
         NS.iter (fun input -> graph := add_link input node !graph) inputs;
         let n1 = List.fold_left add_instr node then_instrs in
         let n2 = List.fold_left add_instr node else_instrs in
         incr icounter;
         let join = G_instr (!icounter, icomment "join") in
         graph := add_link n1 join !graph;
         graph := add_link n2 join !graph;
         join
       end
    | I_goto label ->
       begin
         let _, outputs = instr_deps instr in
         graph := add_link last_instr node !graph;
         NS.iter (fun output -> graph := add_link node output !graph) outputs;
         incr icounter;
         G_instr (!icounter, icomment "after goto")
       end
    | _ ->
       begin
         let inputs, outputs = instr_deps instr in
         graph := add_link last_instr node !graph;
         NS.iter (fun input -> graph := add_link input node !graph) inputs;
         NS.iter (fun output -> graph := add_link node output !graph) outputs;
         node
       end
  in
  ignore (List.fold_left add_instr G_start instrs);
  fix_leaves !graph

let make_dot id graph =
  Util.opt_colors := false;
  let to_string node = String.escaped (string_of_node node) in
  let node_color = function
    | G_start                           -> "lightpink"
    | G_id _                            -> "yellow"
    | G_instr (_, I_aux (I_decl _, _))  -> "olivedrab1"
    | G_instr (_, I_aux (I_init _, _))  -> "springgreen"
    | G_instr (_, I_aux (I_clear _, _)) -> "peachpuff"
    | G_instr (_, I_aux (I_goto _, _))  -> "orange1"
    | G_instr (_, I_aux (I_label _, _)) -> "white"
    | G_instr (_, I_aux (I_raw _, _))   -> "khaki"
    | G_instr _                         -> "azure"
    | G_label _                         -> "lightpink"
  in
  let edge_color from_node to_node =
    match from_node, to_node with
    | G_start  , _         -> "goldenrod4"
    | G_label _, _         -> "darkgreen"
    | _        , G_label _ -> "goldenrod4"
    | G_instr _, G_instr _ -> "black"
    | G_id _   , G_instr _ -> "blue3"
    | G_instr _, G_id _    -> "red3"
    | _        , _         -> "coral3"
  in
  let out_chan = open_out (Util.zencode_string (string_of_id id) ^ ".gv") in
  output_string out_chan "digraph DEPS {\n";
  let make_node from_node =
    output_string out_chan (Printf.sprintf "  \"%s\" [fillcolor=%s;style=filled];\n" (to_string from_node) (node_color from_node))
  in
  let make_line from_node to_node =
    output_string out_chan (Printf.sprintf "  \"%s\" -> \"%s\" [color=%s];\n" (to_string from_node) (to_string to_node) (edge_color from_node to_node))
  in
  NM.bindings graph |> List.iter (fun (from_node, _) -> make_node from_node);
  NM.bindings graph |> List.iter (fun (from_node, to_nodes) -> NS.iter (make_line from_node) to_nodes);
  output_string out_chan "}\n";
  Util.opt_colors := true;
  close_out out_chan

let rec map_clexp_ctyp f = function
  | CL_id (id, ctyp) -> CL_id (id, f ctyp)
  | CL_field (clexp, field) -> CL_field (map_clexp_ctyp f clexp, field)
  | CL_tuple (clexp, n) -> CL_tuple (map_clexp_ctyp f clexp, n)
  | CL_addr clexp -> CL_addr (map_clexp_ctyp f clexp)
  | CL_current_exception ctyp -> CL_current_exception (f ctyp)
  | CL_have_exception -> CL_have_exception

let rec map_instr_ctyp f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl (ctyp, id) -> I_decl (f ctyp, id)
    | I_init (ctyp1, id, (frag, ctyp2)) -> I_init (f ctyp1, id, (frag, f ctyp2))
    | I_if ((frag, ctyp1), then_instrs, else_instrs, ctyp2) ->
       I_if ((frag, f ctyp1), List.map (map_instr_ctyp f) then_instrs, List.map (map_instr_ctyp f) else_instrs, f ctyp2)
    | I_jump ((frag, ctyp), label) -> I_jump ((frag, f ctyp), label)
    | I_funcall (clexp, extern, id, cvals) ->
       I_funcall (map_clexp_ctyp f clexp, extern, id, List.map (fun (frag, ctyp) -> frag, f ctyp) cvals)
    | I_copy (clexp, (frag, ctyp)) -> I_copy (map_clexp_ctyp f clexp, (frag, f ctyp))
    | I_alias (clexp, (frag, ctyp)) -> I_alias (map_clexp_ctyp f clexp, (frag, f ctyp))
    | I_clear (ctyp, id) -> I_clear (f ctyp, id)
    | I_return (frag, ctyp) -> I_return (frag, f ctyp)
    | I_block instrs -> I_block (List.map (map_instr_ctyp f) instrs)
    | I_try_block instrs -> I_try_block (List.map (map_instr_ctyp f) instrs)
    | I_throw (frag, ctyp) -> I_throw (frag, f ctyp)
    | I_undefined ctyp -> I_undefined (f ctyp)
    | I_reset (ctyp, id) -> I_reset (f ctyp, id)
    | I_reinit (ctyp1, id, (frag, ctyp2)) -> I_reinit (f ctyp1, id, (frag, f ctyp2))
    | (I_comment _ | I_raw _ | I_label _ | I_goto _ | I_match_failure) as instr -> instr
  in
  I_aux (instr, aux)

(** Map over each instruction within an instruction, bottom-up *)
let rec map_instr f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _
      | I_funcall _ | I_copy _ | I_alias _ | I_clear _ | I_jump _ | I_throw _ | I_return _
      | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_undefined _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, List.map (map_instr f) instrs1, List.map (map_instr f) instrs2, ctyp)
    | I_block instrs ->
       I_block (List.map (map_instr f) instrs)
    | I_try_block instrs ->
       I_try_block (List.map (map_instr f) instrs)
  in
  f (I_aux (instr, aux))

(** Map over each instruction in a cdef using map_instr *)
let cdef_map_instr f = function
  | CDEF_reg_dec (id, ctyp, instrs) -> CDEF_reg_dec (id, ctyp, List.map (map_instr f) instrs)
  | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, List.map (map_instr f) instrs)
  | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, List.map (map_instr f) instrs)
  | CDEF_startup (id, instrs) -> CDEF_startup (id, List.map (map_instr f) instrs)
  | CDEF_finish (id, instrs) -> CDEF_finish (id, List.map (map_instr f) instrs)
  | CDEF_spec (id, ctyps, ctyp) -> CDEF_spec (id, ctyps, ctyp)
  | CDEF_type tdef -> CDEF_type tdef

let ctype_def_map_ctyp f = function
  | CTD_enum (id, ids) -> CTD_enum (id, ids)
  | CTD_struct (id, ctors) -> CTD_struct (id, List.map (fun (field, ctyp) -> (field, f ctyp)) ctors)
  | CTD_variant (id, ctors) -> CTD_variant (id, List.map (fun (field, ctyp) -> (field, f ctyp)) ctors)

(** Map over each ctyp in a cdef using map_instr_ctyp *)
let cdef_map_ctyp f = function
  | CDEF_reg_dec (id, ctyp, instrs) -> CDEF_reg_dec (id, f ctyp, List.map (map_instr_ctyp f) instrs)
  | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, List.map (map_instr_ctyp f) instrs)
  | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, List.map (map_instr_ctyp f) instrs)
  | CDEF_startup (id, instrs) -> CDEF_startup (id, List.map (map_instr_ctyp f) instrs)
  | CDEF_finish (id, instrs) -> CDEF_finish (id, List.map (map_instr_ctyp f) instrs)
  | CDEF_spec (id, ctyps, ctyp) -> CDEF_spec (id, List.map f ctyps, f ctyp)
  | CDEF_type tdef -> CDEF_type (ctype_def_map_ctyp f tdef)

(* Map over all sequences of instructions contained within an instruction *)
let rec map_instrs f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, f (List.map (map_instrs f) instrs1), f (List.map (map_instrs f) instrs2), ctyp)
    | I_funcall _ | I_copy _ | I_alias _ | I_clear _ | I_jump _ | I_throw _ | I_return _ -> instr
    | I_block instrs -> I_block (f (List.map (map_instrs f) instrs))
    | I_try_block instrs -> I_try_block (f (List.map (map_instrs f) instrs))
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_undefined _ -> instr
  in
  I_aux (instr, aux)

let rec instr_ids (I_aux (instr, _)) =
  let reads, writes = instr_deps instr in
  let get_id = function
    | G_id id -> Some id
    | _ -> None
  in
  NS.elements reads @ NS.elements writes
  |> List.map get_id
  |> Util.option_these
  |> IdSet.of_list

let rec instr_reads (I_aux (instr, _)) =
  let reads, _ = instr_deps instr in
  let get_id = function
    | G_id id -> Some id
    | _ -> None
  in
  NS.elements reads
  |> List.map get_id
  |> Util.option_these
  |> IdSet.of_list

let rec instr_writes (I_aux (instr, _)) =
  let _, writes = instr_deps instr in
  let get_id = function
    | G_id id -> Some id
    | _ -> None
  in
  NS.elements writes
  |> List.map get_id
  |> Util.option_these
  |> IdSet.of_list

let rec filter_instrs f instrs =
  let filter_instrs' = function
    | I_aux (I_block instrs, aux) -> I_aux (I_block (filter_instrs f instrs), aux)
    | I_aux (I_try_block instrs, aux) -> I_aux (I_try_block (filter_instrs f instrs), aux)
    | I_aux (I_if (cval, instrs1, instrs2, ctyp), aux) ->
       I_aux (I_if (cval, filter_instrs f instrs1, filter_instrs f instrs2, ctyp), aux)
    | instr -> instr
  in
  List.filter f (List.map filter_instrs' instrs)
