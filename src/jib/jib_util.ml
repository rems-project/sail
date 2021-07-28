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
open Ast_util
open Jib
open Value2
open PPrint

let symbol_generator str =
  let counter = ref 0 in
  let gensym () =
    let id = mk_id (str ^ "#" ^ string_of_int !counter) in
    incr counter;
    id
  in
  let reset () = counter := 0 in
  (gensym, reset)

(* Define wrappers for creating bytecode instructions. Each function
   uses a counter to assign each instruction a unique identifier. *)

let instr_counter = ref 0

let instr_number () =
  let n = !instr_counter in
  incr instr_counter;
  n

let idecl l ctyp id =
  I_aux (I_decl (ctyp, id), (instr_number (), l))

let ireset ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_reset (ctyp, id), (instr_number (), l))

let iinit l ctyp id cval =
  I_aux (I_init (ctyp, id, cval), (instr_number (), l))

let iif l cval then_instrs else_instrs ctyp =
  I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (instr_number (), l))

let ifuncall l clexp id cvals =
  I_aux (I_funcall (clexp, false, id, cvals), (instr_number (), l))

let iextern ?loc:(l=Parse_ast.Unknown) clexp id cvals =
  I_aux (I_funcall (clexp, true, id, cvals), (instr_number (), l))

let icall ?loc:(l=Parse_ast.Unknown) clexp extern id cvals =
  I_aux (I_funcall (clexp, extern, id, cvals), (instr_number (), l))

let icopy l clexp cval =
  I_aux (I_copy (clexp, cval), (instr_number (), l))

let iclear ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_clear (ctyp, id), (instr_number (), l))

let ireturn ?loc:(l=Parse_ast.Unknown) cval =
  I_aux (I_return cval, (instr_number (), l))

let iend ?loc:(l=Parse_ast.Unknown) () =
  I_aux (I_end (Return (-1)), (instr_number (), l))

let iblock ?loc:(l=Parse_ast.Unknown) instrs =
  I_aux (I_block instrs, (instr_number (), l))

let itry_block ?loc:(l=Parse_ast.Unknown) instrs =
  I_aux (I_try_block instrs, (instr_number (), l))

let ithrow l cval =
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

let ijump l cval label =
  I_aux (I_jump (cval, label), (instr_number (), l))

module Name = struct
  type t = name
  let compare id1 id2 =
    match id1, id2 with
    | Name (x, n), Name (y, m) ->
       let c1 = Id.compare x y in
       if c1 = 0 then compare n m else c1
    | Global (x, n), Global (y, m) ->
       let c1 = Id.compare x y in
       if c1 = 0 then compare n m else c1
    | Have_exception n, Have_exception m -> compare n m
    | Current_exception n, Current_exception m -> compare n m
    | Return n, Return m -> compare n m
    | Name _, _ -> 1
    | _, Name _ -> -1
    | Global _, _ -> 1
    | _, Global _ -> -1
    | Have_exception _, _ -> 1
    | _, Have_exception _ -> -1
    | Current_exception _, _ -> 1
    | _, Current_exception _ -> -1
    | Throw_location _, _ -> 1
    | _, Throw_location _ -> -1
end

module NameSet = Set.Make(Name)
module NameMap = Map.Make(Name)

let current_exception = Current_exception (-1)
let have_exception = Have_exception (-1)
let throw_location = Throw_location (-1)
let return = Return (-1)

let name id = Name (id, -1)
let global id = Global (id, -1)

let rec cval_rename from_id to_id = function
  | V_id (id, ctyp) when Name.compare id from_id = 0 -> V_id (to_id, ctyp)
  | V_id (id, ctyp) -> V_id (id, ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
  | V_call (call, cvals) -> V_call (call, List.map (cval_rename from_id to_id) cvals)
  | V_field (f, field) -> V_field (cval_rename from_id to_id f, field)
  | V_tuple_member (f, len, n) -> V_tuple_member (cval_rename from_id to_id f, len, n)
  | V_ctor_kind (f, ctor, unifiers, ctyp) -> V_ctor_kind (cval_rename from_id to_id f, ctor, unifiers, ctyp)
  | V_ctor_unwrap (ctor, f, unifiers, ctyp) -> V_ctor_unwrap (ctor, cval_rename from_id to_id f, unifiers, ctyp)
  | V_struct (fields, ctyp) ->
     V_struct (List.map (fun (field, cval) -> field, cval_rename from_id to_id cval) fields, ctyp)
  | V_poly (f, ctyp) -> V_poly (cval_rename from_id to_id f, ctyp)

let rec clexp_rename from_id to_id = function
  | CL_id (id, ctyp) when Name.compare id from_id = 0 -> CL_id (to_id, ctyp)
  | CL_id (id, ctyp) -> CL_id (id, ctyp)
  | CL_rmw (read, write, ctyp) ->
     CL_rmw ((if Name.compare read from_id = 0 then to_id else read),
             (if Name.compare write from_id = 0 then to_id else write),
             ctyp)
  | CL_field (clexp, field) ->
     CL_field (clexp_rename from_id to_id clexp, field)
  | CL_addr clexp ->
     CL_addr (clexp_rename from_id to_id clexp)
  | CL_tuple (clexp, n) ->
     CL_tuple (clexp_rename from_id to_id clexp, n)
  | CL_void -> CL_void

let rec instr_rename from_id to_id (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl (ctyp, id) when Name.compare id from_id = 0 -> I_decl (ctyp, to_id)
    | I_decl (ctyp, id) -> I_decl (ctyp, id)

    | I_init (ctyp, id, cval) when Name.compare id from_id = 0 ->
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

    | I_clear (ctyp, id) when Name.compare id from_id = 0 -> I_clear (ctyp, to_id)
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

    | I_end id when Name.compare id from_id = 0 -> I_end to_id
    | I_end id -> I_end id

    | I_reset (ctyp, id) when Name.compare id from_id = 0 -> I_reset (ctyp, to_id)
    | I_reset (ctyp, id) -> I_reset (ctyp, id)

    | I_reinit (ctyp, id, cval) when Name.compare id from_id = 0 ->
       I_reinit (ctyp, to_id, cval_rename from_id to_id cval)
    | I_reinit (ctyp, id, cval) ->
       I_reinit (ctyp, id, cval_rename from_id to_id cval)
  in
  I_aux (instr, aux)

(**************************************************************************)
(* 1. Instruction pretty printer                                          *)
(**************************************************************************)

let string_of_name ?deref_current_exception:(dce=false) ?zencode:(zencode=true) =
  let ssa_num n = if n = -1 then "" else ("/" ^ string_of_int n) in
  function
  | Name (id, n) | Global (id, n) ->
     (if zencode then Util.zencode_string (string_of_id id) else string_of_id id) ^ ssa_num n
  | Have_exception n ->
     "have_exception" ^ ssa_num n
  | Return n ->
     "return" ^ ssa_num n
  | Current_exception n when dce ->
     "(*current_exception)" ^ ssa_num n
  | Current_exception n ->
     "current_exception" ^ ssa_num n
  | Throw_location n ->
     "throw_location" ^ ssa_num n

let string_of_op = function
  | Bnot -> "@not"
  | Band -> "@and"
  | Bor -> "@or"
  | List_hd -> "@hd"
  | List_tl -> "@tl"
  | Eq -> "@eq"
  | Neq -> "@neq"
  | Bvnot -> "@bvnot"
  | Bvor -> "@bvor"
  | Bvand -> "@bvand"
  | Bvxor -> "@bvxor"
  | Bvadd -> "@bvadd"
  | Bvsub -> "@bvsub"
  | Bvaccess -> "@bvaccess"
  | Ilt -> "@lt"
  | Igt -> "@gt"
  | Ilteq -> "@lteq"
  | Igteq -> "@gteq"
  | Iadd -> "@iadd"
  | Isub -> "@isub"
  | Unsigned n -> "@unsigned::<" ^ string_of_int n ^ ">"
  | Signed n -> "@signed::<" ^ string_of_int n ^ ">"
  | Zero_extend n -> "@zero_extend::<" ^ string_of_int n ^ ">"
  | Sign_extend n -> "@sign_extend::<" ^ string_of_int n ^ ">"
  | Slice n -> "@slice::<" ^ string_of_int n ^ ">"
  | Sslice n -> "@sslice::<" ^ string_of_int n ^ ">"
  | Replicate n -> "@replicate::<" ^ string_of_int n ^ ">"
  | Set_slice -> "@set_slice"
  | Concat -> "@concat"

(* String representation of ctyps here is only for debugging and
   intermediate language pretty-printer. *)
let rec string_of_ctyp = function
  | CT_lint -> "%i"
  | CT_fint n -> "%i" ^ string_of_int n
  | CT_lbits _ -> "%bv"
  | CT_sbits (n, _) -> "%sbv" ^ string_of_int n
  | CT_fbits (n, _) -> "%bv" ^ string_of_int n
  | CT_constant n -> Big_int.to_string n
  | CT_bit -> "%bit"
  | CT_unit -> "%unit"
  | CT_bool -> "%bool"
  | CT_real -> "%real"
  | CT_string -> "%string"
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
  | CT_struct (id, _) -> "%struct " ^ Util.zencode_string (string_of_id id)
  | CT_enum (id, _) -> "%enum " ^ Util.zencode_string (string_of_id id)
  | CT_variant (id, _) -> "%union " ^ Util.zencode_string (string_of_id id)
  | CT_vector (_, ctyp) -> "%vec(" ^ string_of_ctyp ctyp ^ ")"
  | CT_fvector (n, _, ctyp) -> "%fvec(" ^ string_of_int n ^ ", " ^ string_of_ctyp ctyp ^ ")"
  | CT_list ctyp -> "%list(" ^ string_of_ctyp ctyp ^ ")"
  | CT_ref ctyp -> "&(" ^ string_of_ctyp ctyp ^ ")"
  | CT_poly -> "*"

and string_of_uid (id, ctyps) =
  match ctyps with
  | [] -> Util.zencode_string (string_of_id id)
  | _ -> Util.zencode_string (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

(** This function is like string_of_ctyp, but recursively prints all
   constructors in variants and structs. Used for debug output. *)
and full_string_of_ctyp = function
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " full_string_of_ctyp ctyps ^ ")"
  | CT_struct (id, ctors) ->
     "struct " ^ string_of_id id
     ^ "{"
     ^ Util.string_of_list ", " (fun ((id, _), ctyp) -> string_of_id id ^ " : " ^ full_string_of_ctyp ctyp) ctors
     ^ "}"
  | CT_variant (id, ctors) ->
     "union " ^ string_of_id id
     ^ "{"
     ^ Util.string_of_list ", " (fun ((id, _), ctyp) -> string_of_id id ^ " : " ^ full_string_of_ctyp ctyp) ctors
     ^ "}"
  | CT_vector (true, ctyp) -> "vector(dec, " ^ full_string_of_ctyp ctyp ^ ")"
  | CT_vector (false, ctyp) -> "vector(inc, " ^ full_string_of_ctyp ctyp ^ ")"
  | CT_list ctyp -> "list(" ^ full_string_of_ctyp ctyp ^ ")"
  | CT_ref ctyp -> "ref(" ^ full_string_of_ctyp ctyp ^ ")"
  | ctyp -> string_of_ctyp ctyp

let rec string_of_value = function
  | VL_bits ([], _) -> "UINT64_C(0)"
  | VL_bits (bs, true) -> Sail2_values.show_bitlist bs
  | VL_bits (bs, false) -> Sail2_values.show_bitlist (List.rev bs)
  | VL_int i -> Big_int.to_string i
  | VL_bool true -> "true"
  | VL_bool false -> "false"
  | VL_unit -> "()"
  | VL_bit Sail2_values.B0 -> "bitzero"
  | VL_bit Sail2_values.B1 -> "bitone"
  | VL_bit Sail2_values.BU -> failwith "Undefined bit found in value"
  | VL_real str -> str
  | VL_string str -> "\"" ^ str ^ "\""
  | VL_empty_list -> "NULL"
  | VL_enum element -> Util.zencode_string element
  | VL_ref r -> "&" ^ Util.zencode_string r
  | VL_undefined -> "undefined"

let rec string_of_cval = function
  | V_id (id, ctyp) -> string_of_name id
  | V_lit (VL_undefined, ctyp) -> string_of_value VL_undefined ^ " : " ^ string_of_ctyp ctyp
  | V_lit (vl, ctyp) -> string_of_value vl
  | V_call (op, cvals) ->
     Printf.sprintf "%s(%s)" (string_of_op op) (Util.string_of_list ", " string_of_cval cvals)
  | V_field (f, field) ->
     Printf.sprintf "%s.%s" (string_of_cval f) (string_of_uid field)
  | V_tuple_member (f, _, n) ->
     Printf.sprintf "%s.ztup%d" (string_of_cval f) n
  | V_ctor_kind (f, ctor, unifiers, _) ->
     string_of_cval f ^ " is " ^ string_of_uid (ctor, unifiers)
  | V_ctor_unwrap (ctor, f, unifiers, _) ->
     string_of_cval f ^ " as " ^ string_of_uid (ctor, unifiers)
  | V_struct (fields, _) ->
     Printf.sprintf "{%s}"
       (Util.string_of_list ", " (fun (field, cval) -> string_of_uid field ^ " = " ^ string_of_cval cval) fields)
  | V_poly (f, _) -> string_of_cval f

let rec map_ctyp f = function
  | (CT_lint | CT_fint _ | CT_constant _ | CT_lbits _ | CT_fbits _ | CT_sbits _
     | CT_bit | CT_unit | CT_bool | CT_real | CT_string | CT_poly | CT_enum _) as ctyp -> f ctyp
  | CT_tup ctyps -> f (CT_tup (List.map (map_ctyp f) ctyps))
  | CT_ref ctyp -> f (CT_ref (map_ctyp f ctyp))
  | CT_vector (direction, ctyp) -> f (CT_vector (direction, map_ctyp f ctyp))
  | CT_fvector (n, direction, ctyp) -> f (CT_fvector (n, direction, map_ctyp f ctyp))
  | CT_list ctyp -> f (CT_list (map_ctyp f ctyp))
  | CT_struct (id, ctors) ->
     f (CT_struct (id, List.map (fun ((id, ctyps), ctyp) -> (id, List.map (map_ctyp f) ctyps), map_ctyp f ctyp) ctors))
  | CT_variant (id, ctors) ->
     f (CT_variant (id, List.map (fun ((id, ctyps), ctyp) -> (id, List.map (map_ctyp f) ctyps), map_ctyp f ctyp) ctors))

let rec ctyp_equal ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_lint, CT_lint -> true
  | CT_lbits d1, CT_lbits d2 -> d1 = d2
  | CT_sbits (m1, d1), CT_sbits (m2, d2) -> m1 = m2 && d1 = d2
  | CT_fbits (m1, d1), CT_fbits (m2, d2) -> m1 = m2 && d1 = d2
  | CT_bit, CT_bit -> true
  | CT_fint n, CT_fint m -> n = m
  | CT_constant n, CT_constant m -> Big_int.equal n m
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
  | CT_fvector (n1, d1, ctyp1), CT_fvector (n2, d2, ctyp2) -> n1 = n2 && d1 = d2 && ctyp_equal ctyp1 ctyp2
  | CT_list ctyp1, CT_list ctyp2 -> ctyp_equal ctyp1 ctyp2
  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_equal ctyp1 ctyp2
  | CT_poly, CT_poly -> true
  | _, _ -> false

let rec ctyp_compare ctyp1 ctyp2 =
  let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
  match ctyp1, ctyp2 with
  | CT_lint, CT_lint -> 0
  | CT_lint, _ -> 1
  | _, CT_lint -> -1

  | CT_fint n, CT_fint m -> compare n m
  | CT_fint _, _ -> 1
  | _, CT_fint _ -> -1

  | CT_constant n, CT_constant m -> Big_int.compare n m
  | CT_constant _, _ -> 1
  | _, CT_constant _ -> -1

  | CT_fbits (n, ord1), CT_fbits (m, ord2) -> lex_ord (compare n m) (compare ord1 ord2)
  | CT_fbits _, _ -> 1
  | _, CT_fbits _ -> -1

  | CT_sbits (n, ord1), CT_sbits (m, ord2) -> lex_ord (compare n m) (compare ord1 ord2)
  | CT_sbits _, _ -> 1
  | _, CT_sbits _ -> -1

  | CT_lbits ord1 , CT_lbits ord2 -> compare ord1 ord2
  | CT_lbits _, _ -> 1
  | _, CT_lbits _ -> -1

  | CT_bit, CT_bit -> 0
  | CT_bit, _ -> 1
  | _, CT_bit -> -1

  | CT_unit, CT_unit -> 0
  | CT_unit, _ -> 1
  | _, CT_unit -> -1

  | CT_real, CT_real -> 0
  | CT_real, _ -> 1
  | _, CT_real -> -1

  | CT_poly, CT_poly -> 0
  | CT_poly, _ -> 1
  | _, CT_poly -> -1

  | CT_bool, CT_bool -> 0
  | CT_bool, _ -> 1
  | _, CT_bool -> -1

  | CT_string, CT_string -> 0
  | CT_string, _ -> 1
  | _, CT_string -> -1

  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_compare ctyp1 ctyp2
  | CT_ref _, _ -> 1
  | _, CT_ref _ -> -1

  | CT_list ctyp1, CT_list ctyp2 -> ctyp_compare ctyp1 ctyp2
  | CT_list _, _ -> 1
  | _, CT_list _ -> -1

  | CT_vector (d1, ctyp1), CT_vector (d2, ctyp2) ->
     lex_ord (ctyp_compare ctyp1 ctyp2) (compare d1 d2)
  | CT_vector _, _ -> 1
  | _, CT_vector _ -> -1

  | CT_fvector (n1, d1, ctyp1), CT_fvector (n2, d2, ctyp2) ->
     lex_ord (compare n1 n2) (lex_ord (ctyp_compare ctyp1 ctyp2) (compare d1 d2))
  | CT_fvector _, _ -> 1
  | _, CT_fvector _ -> -1

  | ctyp1, ctyp2 -> String.compare (full_string_of_ctyp ctyp1) (full_string_of_ctyp ctyp2)

module CT = struct
  type t = ctyp
  let compare ctyp1 ctyp2 = ctyp_compare ctyp1 ctyp2
end

module CTSet = Set.Make(CT)
module CTMap = Map.Make(CT)

module UId = struct
  type t = (id * ctyp list)
  let lex_ord c1 c2 = if c1 = 0 then c2 else c1
  let rec compare_ctyps ctyps1 ctyps2 =
    match ctyps1, ctyps2 with
    | (ctyp1 :: ctyps1), (ctyp2 :: ctyps2) ->
       lex_ord (CT.compare ctyp1 ctyp2) (compare_ctyps ctyps1 ctyps2)
    | [], [] -> 0
    | [], _ -> 1
    | _, [] -> -1
  let compare (id1, ctyps1) (id2, ctyps2) =
    let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
    lex_ord (Id.compare id1 id2) (compare_ctyps ctyps1 ctyps2)
end

module UBindings = Map.Make(UId)

let rec ctyp_unify ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_tup ctyps1, CT_tup ctyps2 when List.length ctyps1 = List.length ctyps2 ->
     List.concat (List.map2 ctyp_unify ctyps1 ctyps2)

  | CT_vector (b1, ctyp1), CT_vector (b2, ctyp2) when b1 = b2 ->
     ctyp_unify ctyp1 ctyp2

  | CT_list ctyp1, CT_list ctyp2 -> ctyp_unify ctyp1 ctyp2

  | CT_struct (id1, fields1), CT_struct (id2, fields2)
       when Id.compare id1 id2 = 0 && List.length fields1 == List.length fields2 ->
     if List.for_all2 (fun x y -> x = y) (List.map fst fields1) (List.map fst fields2) then
       List.concat (List.map2 ctyp_unify (List.map snd fields1) (List.map snd fields2))
     else
       raise (Invalid_argument "ctyp_unify")

  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_unify ctyp1 ctyp2

  | CT_poly, _ -> [ctyp2]

  | _, _ when ctyp_equal ctyp1 ctyp2 -> []
  | _, _ -> raise (Invalid_argument "ctyp_unify")

let rec ctyp_suprema = function
  | CT_lint -> CT_lint
  | CT_lbits d -> CT_lbits d
  | CT_fbits (_, d) -> CT_lbits d
  | CT_sbits (_, d) -> CT_lbits d
  | CT_fint _ -> CT_lint
  | CT_constant _ -> CT_lint
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
  | CT_fvector (n, d, ctyp) -> CT_fvector (n, d, ctyp_suprema ctyp)
  | CT_list ctyp -> CT_list (ctyp_suprema ctyp)
  | CT_ref ctyp -> CT_ref (ctyp_suprema ctyp)
  | CT_poly -> CT_poly

let rec ctyp_ids = function
  | CT_enum (id, _) -> IdSet.singleton id
  | CT_struct (id, ctors) | CT_variant (id, ctors) ->
     IdSet.add id (List.fold_left (fun ids (_, ctyp) -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctors)
  | CT_tup ctyps -> List.fold_left (fun ids ctyp -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctyps
  | CT_vector (_, ctyp) | CT_fvector (_, _, ctyp) | CT_list ctyp | CT_ref ctyp -> ctyp_ids ctyp
  | CT_lint | CT_fint _ | CT_constant _ | CT_lbits _ | CT_fbits _ | CT_sbits _ | CT_unit
    | CT_bool | CT_real | CT_bit | CT_string | CT_poly -> IdSet.empty

let rec unpoly = function
  | V_poly (cval, _) -> unpoly cval
  | V_call (call, cvals) -> V_call (call, List.map unpoly cvals)
  | V_field (cval, field) -> V_field (unpoly cval, field)
  | cval -> cval

let rec is_polymorphic = function
  | CT_lint | CT_fint _ | CT_constant _ | CT_lbits _ | CT_fbits _ | CT_sbits _ | CT_bit | CT_unit | CT_bool | CT_real | CT_string -> false
  | CT_tup ctyps -> List.exists is_polymorphic ctyps
  | CT_enum _ -> false
  | CT_struct (_, ctors) | CT_variant (_, ctors) -> List.exists (fun (_, ctyp) -> is_polymorphic ctyp) ctors
  | CT_fvector (_, _, ctyp) | CT_vector (_, ctyp) | CT_list ctyp | CT_ref ctyp -> is_polymorphic ctyp
  | CT_poly -> true

let rec cval_deps = function
  | V_id (id, _) -> NameSet.singleton id
  | V_lit _ -> NameSet.empty
  | V_field (cval, _) | V_poly (cval, _) | V_tuple_member (cval, _, _) -> cval_deps cval
  | V_call (_, cvals) -> List.fold_left NameSet.union NameSet.empty (List.map cval_deps cvals)
  | V_ctor_kind (cval, _, _, _) -> cval_deps cval
  | V_ctor_unwrap (_, cval, _, _) -> cval_deps cval
  | V_struct (fields, ctyp) -> List.fold_left (fun ns (_, cval) -> NameSet.union ns (cval_deps cval)) NameSet.empty fields

let rec clexp_deps = function
  | CL_id (id, _) -> NameSet.empty, NameSet.singleton id
  | CL_rmw (read, write, _) -> NameSet.singleton read, NameSet.singleton write
  | CL_field (clexp, _) -> clexp_deps clexp
  | CL_tuple (clexp, _) -> clexp_deps clexp
  | CL_addr clexp -> clexp_deps clexp
  | CL_void -> NameSet.empty, NameSet.empty

(* Return the direct, read/write dependencies of a single instruction *)
let instr_deps = function
  | I_decl (ctyp, id) -> NameSet.empty, NameSet.singleton id
  | I_reset (ctyp, id) -> NameSet.empty, NameSet.singleton id
  | I_init (ctyp, id, cval) | I_reinit (ctyp, id, cval) -> cval_deps cval, NameSet.singleton id
  | I_if (cval, _, _, _) -> cval_deps cval, NameSet.empty
  | I_jump (cval, label) -> cval_deps cval, NameSet.empty
  | I_funcall (clexp, _, _, cvals) ->
     let reads, writes = clexp_deps clexp in
     List.fold_left NameSet.union reads (List.map cval_deps cvals), writes
  | I_copy (clexp, cval) ->
     let reads, writes = clexp_deps clexp in
     NameSet.union reads (cval_deps cval), writes
  | I_clear (_, id) -> NameSet.singleton id, NameSet.empty
  | I_throw cval | I_return cval -> cval_deps cval, NameSet.empty
  | I_block _ | I_try_block _ -> NameSet.empty, NameSet.empty
  | I_comment _ | I_raw _ -> NameSet.empty, NameSet.empty
  | I_label label -> NameSet.empty, NameSet.empty
  | I_goto label -> NameSet.empty, NameSet.empty
  | I_undefined _ -> NameSet.empty, NameSet.empty
  | I_match_failure -> NameSet.empty, NameSet.empty
  | I_end id -> NameSet.singleton id, NameSet.empty

module NameCT = struct
  type t = name * ctyp
  let compare (n1, ctyp1) (n2, ctyp2) =
    let c = Name.compare n1 n2 in
    if c = 0 then CT.compare ctyp1 ctyp2 else c
end

module NameCTSet = Set.Make(NameCT)
module NameCTMap = Map.Make(NameCT)

let rec clexp_typed_writes = function
  | CL_id (id, ctyp) -> NameCTSet.singleton (id, ctyp)
  | CL_rmw (_, id, ctyp) -> NameCTSet.singleton (id, ctyp)
  | CL_field (clexp, _) -> clexp_typed_writes clexp
  | CL_tuple (clexp, _) -> clexp_typed_writes clexp
  | CL_addr clexp -> clexp_typed_writes clexp
  | CL_void -> NameCTSet.empty

let instr_typed_writes (I_aux (aux, _)) =
  match aux with
  | I_decl (ctyp, id) | I_reset (ctyp, id) -> NameCTSet.singleton (id, ctyp)
  | I_init (ctyp, id, _) | I_reinit (ctyp, id, _) -> NameCTSet.singleton (id, ctyp)
  | I_funcall (clexp, _, _, _) | I_copy (clexp, _) -> clexp_typed_writes clexp
  | _ -> NameCTSet.empty

let rec map_clexp_ctyp f = function
  | CL_id (id, ctyp) -> CL_id (id, f ctyp)
  | CL_rmw (read, write, ctyp) -> CL_rmw (read, write, f ctyp)
  | CL_field (clexp, (id, ctyps)) -> CL_field (map_clexp_ctyp f clexp, (id, List.map f ctyps))
  | CL_tuple (clexp, n) -> CL_tuple (map_clexp_ctyp f clexp, n)
  | CL_addr clexp -> CL_addr (map_clexp_ctyp f clexp)
  | CL_void -> CL_void

let rec map_cval_ctyp f = function
  | V_id (id, ctyp) -> V_id (id, f ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, f ctyp)
  | V_ctor_kind (cval, id, unifiers, ctyp) ->
     V_ctor_kind (map_cval_ctyp f cval, id, List.map f unifiers, f ctyp)
  | V_ctor_unwrap (id, cval, unifiers, ctyp) ->
     V_ctor_unwrap (id, map_cval_ctyp f cval, List.map f unifiers, f ctyp)
  | V_tuple_member (cval, i, j) ->
     V_tuple_member (map_cval_ctyp f cval, i, j)
  | V_call (op, cvals) ->
     V_call (op, List.map (map_cval_ctyp f) cvals)
  | V_field (cval, (id, ctyps)) ->
     V_field (map_cval_ctyp f cval, (id, List.map f ctyps))
  | V_struct (fields, ctyp) ->
     V_struct (List.map (fun ((id, ctyps), cval) -> (id, List.map f ctyps), map_cval_ctyp f cval) fields, f ctyp)
  | V_poly (cval, ctyp) -> V_poly (map_cval_ctyp f cval, f ctyp)

let rec map_instr_ctyp f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl (ctyp, id) -> I_decl (f ctyp, id)
    | I_init (ctyp, id, cval) -> I_init (f ctyp, id, map_cval_ctyp f cval)
    | I_if (cval, then_instrs, else_instrs, ctyp) ->
       I_if (map_cval_ctyp f cval, List.map (map_instr_ctyp f) then_instrs, List.map (map_instr_ctyp f) else_instrs, f ctyp)
    | I_jump (cval, label) -> I_jump (map_cval_ctyp f cval, label)
    | I_funcall (clexp, extern, (id, ctyps), cvals) ->
       I_funcall (map_clexp_ctyp f clexp, extern, (id, List.map f ctyps), List.map (map_cval_ctyp f) cvals)
    | I_copy (clexp, cval) -> I_copy (map_clexp_ctyp f clexp, map_cval_ctyp f cval)
    | I_clear (ctyp, id) -> I_clear (f ctyp, id)
    | I_return cval -> I_return (map_cval_ctyp f cval)
    | I_block instrs -> I_block (List.map (map_instr_ctyp f) instrs)
    | I_try_block instrs -> I_try_block (List.map (map_instr_ctyp f) instrs)
    | I_throw cval -> I_throw (map_cval_ctyp f cval)
    | I_undefined ctyp -> I_undefined (f ctyp)
    | I_reset (ctyp, id) -> I_reset (f ctyp, id)
    | I_reinit (ctyp, id, cval) -> I_reinit (f ctyp, id, map_cval_ctyp f cval)
    | I_end id -> I_end id
    | (I_comment _ | I_raw _ | I_label _ | I_goto _ | I_match_failure) as instr -> instr
  in
  I_aux (instr, aux)

(** Map over each instruction within an instruction, bottom-up *)
let rec map_instr f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _
      | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _ | I_return _
      | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_undefined _ | I_end _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, List.map (map_instr f) instrs1, List.map (map_instr f) instrs2, ctyp)
    | I_block instrs ->
       I_block (List.map (map_instr f) instrs)
    | I_try_block instrs ->
       I_try_block (List.map (map_instr f) instrs)
  in
  f (I_aux (instr, aux))

(** Map over each instruction within an instruction, bottom-up *)
let rec concatmap_instr f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _
      | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _ | I_return _
      | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_undefined _ | I_end _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, List.concat (List.map (concatmap_instr f) instrs1), List.concat (List.map (concatmap_instr f) instrs2), ctyp)
    | I_block instrs ->
       I_block (List.concat (List.map (concatmap_instr f) instrs))
    | I_try_block instrs ->
       I_try_block (List.concat (List.map (concatmap_instr f) instrs))
  in
  f (I_aux (instr, aux))

(** Iterate over each instruction within an instruction, bottom-up *)
let rec iter_instr f (I_aux (instr, aux)) =
  match instr with
  | I_decl _ | I_init _ | I_reset _ | I_reinit _
    | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _ | I_return _
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_undefined _ | I_end _ -> f (I_aux (instr, aux))
  | I_if (cval, instrs1, instrs2, ctyp) ->
     List.iter (iter_instr f) instrs1;
     List.iter (iter_instr f) instrs2
  | I_block instrs | I_try_block instrs ->
     List.iter (iter_instr f) instrs

(** Map over each instruction in a cdef using map_instr *)
let cdef_map_instr f = function
  | CDEF_reg_dec (id, ctyp, instrs) -> CDEF_reg_dec (id, ctyp, List.map (map_instr f) instrs)
  | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, List.map (map_instr f) instrs)
  | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, List.map (map_instr f) instrs)
  | CDEF_startup (id, instrs) -> CDEF_startup (id, List.map (map_instr f) instrs)
  | CDEF_finish (id, instrs) -> CDEF_finish (id, List.map (map_instr f) instrs)
  | CDEF_spec (id, extern, ctyps, ctyp) -> CDEF_spec (id, extern, ctyps, ctyp)
  | CDEF_type tdef -> CDEF_type tdef

(** Map over each instruction in a cdef using concatmap_instr *)
let cdef_concatmap_instr f = function
  | CDEF_reg_dec (id, ctyp, instrs) ->
     CDEF_reg_dec (id, ctyp, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_let (n, bindings, instrs) ->
     CDEF_let (n, bindings, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_fundef (id, heap_return, args, instrs) ->
     CDEF_fundef (id, heap_return, args, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_startup (id, instrs) ->
     CDEF_startup (id, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_finish (id, instrs) ->
     CDEF_finish (id, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_spec (id, extern, ctyps, ctyp) -> CDEF_spec (id, extern, ctyps, ctyp)
  | CDEF_type tdef -> CDEF_type tdef

let ctype_def_map_ctyp f = function
  | CTD_enum (id, ids) -> CTD_enum (id, ids)
  | CTD_struct (id, ctors) -> CTD_struct (id, List.map (fun ((id, ctyps), ctyp) -> ((id, List.map f ctyps), f ctyp)) ctors)
  | CTD_variant (id, ctors) -> CTD_variant (id, List.map (fun ((id, ctyps), ctyp) -> ((id, List.map f ctyps), f ctyp)) ctors)

(** Map over each ctyp in a cdef using map_instr_ctyp *)
let cdef_map_ctyp f = function
  | CDEF_reg_dec (id, ctyp, instrs) -> CDEF_reg_dec (id, f ctyp, List.map (map_instr_ctyp f) instrs)
  | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, List.map (map_instr_ctyp f) instrs)
  | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, List.map (map_instr_ctyp f) instrs)
  | CDEF_startup (id, instrs) -> CDEF_startup (id, List.map (map_instr_ctyp f) instrs)
  | CDEF_finish (id, instrs) -> CDEF_finish (id, List.map (map_instr_ctyp f) instrs)
  | CDEF_spec (id, extern, ctyps, ctyp) -> CDEF_spec (id, extern, List.map f ctyps, f ctyp)
  | CDEF_type tdef -> CDEF_type (ctype_def_map_ctyp f tdef)

(* Map over all sequences of instructions contained within an instruction *)
let rec map_instrs f (I_aux (instr, aux)) =
  let instr = match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _ -> instr
    | I_if (cval, instrs1, instrs2, ctyp) ->
       I_if (cval, f (List.map (map_instrs f) instrs1), f (List.map (map_instrs f) instrs2), ctyp)
    | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _ | I_return _ -> instr
    | I_block instrs -> I_block (f (List.map (map_instrs f) instrs))
    | I_try_block instrs -> I_try_block (f (List.map (map_instrs f) instrs))
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_undefined _  | I_end _ -> instr
  in
  I_aux (instr, aux)

let map_instr_list f instrs =
  List.map (map_instr f) instrs

let map_instrs_list f instrs =
  f (List.map (map_instrs f) instrs)

let rec instr_ids (I_aux (instr, _)) =
  let reads, writes = instr_deps instr in
  NameSet.union reads writes

let rec instr_reads (I_aux (instr, _)) =
  fst (instr_deps instr)

let rec instr_writes (I_aux (instr, _)) =
  snd (instr_deps instr)

let rec filter_instrs f instrs =
  let filter_instrs' = function
    | I_aux (I_block instrs, aux) -> I_aux (I_block (filter_instrs f instrs), aux)
    | I_aux (I_try_block instrs, aux) -> I_aux (I_try_block (filter_instrs f instrs), aux)
    | I_aux (I_if (cval, instrs1, instrs2, ctyp), aux) ->
       I_aux (I_if (cval, filter_instrs f instrs1, filter_instrs f instrs2, ctyp), aux)
    | instr -> instr
  in
  List.filter f (List.map filter_instrs' instrs)

(** GLOBAL: label_counter is used to make sure all labels have unique
   names. Like gensym_counter it should be safe to reset between
   top-level definitions. **)
let label_counter = ref 0

let label str =
  let str = str ^ string_of_int !label_counter in
  incr label_counter;
  str

let rec infer_call op vs =
  match op, vs with
  | Bnot, _ -> CT_bool
  | Band, _ -> CT_bool
  | Bor, _ -> CT_bool
  | List_hd, [v] ->
     begin match cval_ctyp v with
     | CT_list ctyp -> ctyp
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid call to hd"
     end
  | List_tl, [v] ->
     begin match cval_ctyp v with
     | CT_list ctyp -> CT_list ctyp
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid call to tl"
     end
  | (Eq | Neq), _ -> CT_bool
  | Bvnot, [v] -> cval_ctyp v
  | Bvaccess, _ -> CT_bit
  | (Bvor | Bvand | Bvxor | Bvadd | Bvsub), [v; _] -> cval_ctyp v
  | (Ilt | Igt | Ilteq | Igteq), _ -> CT_bool
  | (Iadd | Isub), _ -> CT_fint 64
  | (Unsigned n | Signed n), _ -> CT_fint n
  | (Zero_extend n | Sign_extend n), [v] ->
     begin match cval_ctyp v with
     | CT_fbits (_, ord) | CT_sbits (_, ord) ->
        CT_fbits (n, ord)
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for zero/sign_extend argument"
     end
  | Slice n, [vec; start] ->
     begin match cval_ctyp vec with
     | CT_fbits (_, ord) | CT_sbits (_, ord) ->
        CT_fbits (n, ord)
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for extract argument"
     end
  | Sslice n, [vec; start; len] ->
     begin match cval_ctyp vec with
     | CT_fbits (_, ord) | CT_sbits (_, ord) ->
        CT_sbits (n, ord)
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for extract argument"
     end
  | Set_slice, [vec; _; _] -> cval_ctyp vec
  | Replicate n, [vec] ->
     begin match cval_ctyp vec with
     | CT_fbits (m, ord) -> CT_fbits (n * m, ord)
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for replicate argument"
     end
  | Concat, [v1; v2] ->
     begin match cval_ctyp v1, cval_ctyp v2 with
     | CT_fbits (n, ord), CT_fbits (m, _) ->
        CT_fbits (n + m, ord)
     | CT_fbits (n, ord), CT_sbits (m, _) ->
        CT_sbits (m, ord)
     | CT_sbits (n, ord), CT_fbits (m, _) ->
        CT_sbits (n, ord)
     | CT_sbits (n, ord), CT_sbits (m, _) ->
        CT_sbits (max n m, ord)
     | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for concat argument"
     end
  | _, _ ->
     Reporting.unreachable Parse_ast.Unknown __POS__ ("Invalid call to function " ^ string_of_op op)

and cval_ctyp = function
  | V_id (_, ctyp) -> ctyp
  | V_lit (vl, ctyp) -> ctyp
  | V_ctor_kind _ -> CT_bool
  | V_ctor_unwrap (ctor, cval, unifiers, ctyp) -> ctyp
  | V_poly (_, ctyp) -> ctyp
  | V_tuple_member (cval, _, n) ->
     begin match cval_ctyp cval with
     | CT_tup ctyps ->
        List.nth ctyps n
     | ctyp -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Invalid tuple type " ^ full_string_of_ctyp ctyp)
     end
  | V_field (cval, field) ->
     begin match cval_ctyp cval with
     | CT_struct (id, ctors) ->
        begin
          try snd (List.find (fun (uid, ctyp) -> UId.compare uid field = 0) ctors) with
          | Not_found -> failwith ("Struct type " ^ string_of_id id ^ " does not have a constructor " ^ string_of_uid field)
        end
     | ctyp -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Inavlid type for V_field " ^ full_string_of_ctyp ctyp)
     end
  | V_struct (fields, ctyp) -> ctyp
  | V_call (op, vs) -> infer_call op vs

let rec clexp_ctyp = function
  | CL_id (_, ctyp) -> ctyp
  | CL_rmw (_, _, ctyp) -> ctyp
  | CL_field (clexp, field) ->
     begin match clexp_ctyp clexp with
     | CT_struct (id, ctors) ->
        begin
          try snd (List.find (fun (uid, ctyp) -> UId.compare uid field = 0) ctors) with
          | Not_found -> failwith ("Struct type " ^ string_of_id id ^ " does not have a constructor " ^ string_of_uid field)
        end
     | ctyp -> failwith ("Bad ctyp for CL_field " ^ string_of_ctyp ctyp)
     end
  | CL_addr clexp ->
     begin match clexp_ctyp clexp with
     | CT_ref ctyp -> ctyp
     | ctyp -> failwith ("Bad ctyp for CL_addr " ^ string_of_ctyp ctyp)
     end
  | CL_tuple (clexp, n) ->
     begin match clexp_ctyp clexp with
     | CT_tup typs ->
        begin
          try List.nth typs n with
          | _ -> failwith "Tuple assignment index out of bounds"
        end
     | ctyp -> failwith ("Bad ctyp for CL_addr " ^ string_of_ctyp ctyp)
     end
  | CL_void -> CT_unit

let rec instr_ctyps (I_aux (instr, aux)) =
  match instr with
  | I_decl (ctyp, _) | I_reset (ctyp, _) | I_clear (ctyp, _) | I_undefined ctyp ->
     CTSet.singleton ctyp
  | I_init (ctyp, _, cval) | I_reinit (ctyp, _, cval) ->
     CTSet.add ctyp (CTSet.singleton (cval_ctyp cval))
  | I_if (cval, instrs1, instrs2, ctyp) ->
     CTSet.union (instrs_ctyps instrs1) (instrs_ctyps instrs2)
     |> CTSet.add (cval_ctyp cval)
     |> CTSet.add ctyp
  | I_funcall (clexp, _, (_, ctyps), cvals) ->
     List.fold_left (fun m ctyp -> CTSet.add ctyp m) CTSet.empty (List.map cval_ctyp cvals)
     |> CTSet.union (CTSet.of_list ctyps)
     |> CTSet.add (clexp_ctyp clexp)
  | I_copy (clexp, cval)  ->
     CTSet.add (clexp_ctyp clexp) (CTSet.singleton (cval_ctyp cval))
  | I_block instrs | I_try_block instrs ->
     instrs_ctyps instrs
  | I_throw cval | I_jump (cval, _) | I_return cval ->
     CTSet.singleton (cval_ctyp cval)
  | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_match_failure | I_end _ ->
     CTSet.empty

and instrs_ctyps instrs = List.fold_left CTSet.union CTSet.empty (List.map instr_ctyps instrs)

let ctype_def_ctyps = function
  | CTD_enum _ -> []
  | CTD_struct (_, fields) -> List.map snd fields
  | CTD_variant (_, ctors) -> List.map snd ctors

let cdef_ctyps = function
  | CDEF_reg_dec (_, ctyp, instrs) ->
     CTSet.add ctyp (instrs_ctyps instrs)
  | CDEF_spec (_, _, ctyps, ctyp) ->
     CTSet.add ctyp (List.fold_left (fun m ctyp -> CTSet.add ctyp m) CTSet.empty ctyps)
  | CDEF_fundef (_, _, _, instrs) | CDEF_startup (_, instrs) | CDEF_finish (_, instrs) ->
     instrs_ctyps instrs
  | CDEF_type tdef ->
     List.fold_right CTSet.add (ctype_def_ctyps tdef) CTSet.empty
  | CDEF_let (_, bindings, instrs) ->
     List.fold_left (fun m ctyp -> CTSet.add ctyp m) CTSet.empty (List.map snd bindings)
     |> CTSet.union (instrs_ctyps instrs)

let rec c_ast_registers = function
  | CDEF_reg_dec (id, ctyp, instrs) :: ast -> (id, ctyp, instrs) :: c_ast_registers ast
  | _ :: ast -> c_ast_registers ast
  | [] -> []

let instr_split_at f =
  let rec instr_split_at' f before = function
    | [] -> (List.rev before, [])
    | instr :: instrs when f instr -> (List.rev before, instr :: instrs)
    | instr :: instrs -> instr_split_at' f (instr :: before) instrs
  in
  instr_split_at' f []

let rec instrs_rename from_id to_id =
  let rename id = if Name.compare id from_id = 0 then to_id else id in
  let crename = cval_rename from_id to_id in
  let irename instrs = instrs_rename from_id to_id instrs in
  let lrename = clexp_rename from_id to_id in
  function
  | (I_aux (I_decl (ctyp, new_id), _) :: _) as instrs when Name.compare from_id new_id = 0 -> instrs
  | I_aux (I_decl (ctyp, new_id), aux) :: instrs -> I_aux (I_decl (ctyp, new_id), aux) :: irename instrs
  | I_aux (I_reset (ctyp, id), aux) :: instrs -> I_aux (I_reset (ctyp, rename id), aux) :: irename instrs
  | I_aux (I_init (ctyp, id, cval), aux) :: instrs -> I_aux (I_init (ctyp, rename id, crename cval), aux) :: irename instrs
  | I_aux (I_reinit (ctyp, id, cval), aux) :: instrs -> I_aux (I_reinit (ctyp, rename id, crename cval), aux) :: irename instrs
  | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: instrs ->
     I_aux (I_if (crename cval, irename then_instrs, irename else_instrs, ctyp), aux) :: irename instrs
  | I_aux (I_jump (cval, label), aux) :: instrs -> I_aux (I_jump (crename cval, label), aux) :: irename instrs
  | I_aux (I_funcall (clexp, extern, function_id, cvals), aux) :: instrs ->
     I_aux (I_funcall (lrename clexp, extern, function_id, List.map crename cvals), aux) :: irename instrs
  | I_aux (I_copy (clexp, cval), aux) :: instrs -> I_aux (I_copy (lrename clexp, crename cval), aux) :: irename instrs
  | I_aux (I_clear (ctyp, id), aux) :: instrs -> I_aux (I_clear (ctyp, rename id), aux) :: irename instrs
  | I_aux (I_return cval, aux) :: instrs -> I_aux (I_return (crename cval), aux) :: irename instrs
  | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (irename block), aux) :: irename instrs
  | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (irename block), aux) :: irename instrs
  | I_aux (I_throw cval, aux) :: instrs -> I_aux (I_throw (crename cval), aux) :: irename instrs
  | I_aux (I_end id, aux) :: instrs -> I_aux (I_end (rename id), aux) :: irename instrs
  | (I_aux ((I_comment _ | I_raw _ | I_label _ | I_goto _ | I_match_failure | I_undefined _), _) as instr) :: instrs -> instr :: irename instrs
  | [] -> []
