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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
open Ast_util
open Jib
open Jib_visitor
open Value2
open PPrint
module Document = Pretty_print_sail.Document

let generators = ref 0

let symbol_generator () =
  let gen_no = !generators in
  incr generators;
  let counter = ref 0 in
  let gensym () =
    let id = Gen (gen_no, !counter, -1) in
    incr counter;
    id
  in
  gensym

module Name = struct
  type t = name
  let compare id1 id2 =
    match (id1, id2) with
    | Gen (x1, x2, n), Gen (y1, y2, m) ->
        let c1 = Int.compare x1 y1 in
        if c1 = 0 then (
          let c2 = Int.compare x2 y2 in
          if c2 = 0 then Int.compare n m else c2
        )
        else c1
    | Name (x, n), Name (y, m) ->
        let c1 = Id.compare x y in
        if c1 = 0 then Int.compare n m else c1
    | Abstract x, Abstract y -> Id.compare x y
    | Have_exception n, Have_exception m -> compare n m
    | Current_exception n, Current_exception m -> compare n m
    | Return n, Return m -> compare n m
    | Memory_writes n, Memory_writes m -> compare n m
    | Channel (c1, n), Channel (c2, m) -> begin
        match (c1, c2) with
        | Chan_stdout, Chan_stdout -> compare n m
        | Chan_stderr, Chan_stderr -> compare n m
        | Chan_stdout, Chan_stderr -> 1
        | Chan_stderr, Chan_stdout -> -1
      end
    | Gen _, _ -> 1
    | _, Gen _ -> -1
    | Name _, _ -> 1
    | _, Name _ -> -1
    | Abstract _, _ -> 1
    | _, Abstract _ -> -1
    | Have_exception _, _ -> 1
    | _, Have_exception _ -> -1
    | Current_exception _, _ -> 1
    | _, Current_exception _ -> -1
    | Throw_location _, _ -> 1
    | _, Throw_location _ -> -1
    | Return _, _ -> 1
    | _, Return _ -> -1
    | Memory_writes _, _ -> 1
    | _, Memory_writes _ -> -1
end

module NameSet = Set.Make (Name)
module NameMap = Map.Make (Name)

let current_exception = Current_exception (-1)
let have_exception = Have_exception (-1)
let throw_location = Throw_location (-1)
let return = Return (-1)

let name id = Name (id, -1)

class rename_visitor from_name to_name : jib_visitor =
  object
    inherit empty_jib_visitor

    method! vctyp _ = SkipChildren

    method! vname name = if Name.compare name from_name = 0 then Some to_name else None
  end

let cval_rename from_name to_name = visit_cval (new rename_visitor from_name to_name)

class map_cval_visitor f : jib_visitor =
  object
    inherit empty_jib_visitor

    method! vctyp _ = SkipChildren
    method! vclexp _ = SkipChildren

    method! vcval cval = ChangeDoChildrenPost (cval, f)
  end

let map_cval f = visit_cval (new map_cval_visitor f)

let clexp_rename from_name to_name = visit_clexp (new rename_visitor from_name to_name)

let instr_rename from_name to_name = visit_instr (new rename_visitor from_name to_name)

let instrs_rename from_name to_name = visit_instrs (new rename_visitor from_name to_name)

(**************************************************************************)
(* 1. Instruction pretty printer                                          *)
(**************************************************************************)

let string_of_name ?deref_current_exception:(dce = false) ?(zencode = true) =
  let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n in
  function
  | Gen (v1, v2, n) ->
      let s = "%" ^ string_of_int v1 ^ "." ^ string_of_int v2 in
      (if zencode then Util.zencode_string s else s) ^ ssa_num n
  | Name (id, n) -> (if zencode then Util.zencode_string (string_of_id id) else string_of_id id) ^ ssa_num n
  | Abstract id -> string_of_id id
  | Have_exception n -> "have_exception" ^ ssa_num n
  | Return n -> "return" ^ ssa_num n
  | Current_exception n when dce -> "(*current_exception)" ^ ssa_num n
  | Current_exception n -> "current_exception" ^ ssa_num n
  | Throw_location n -> "throw_location" ^ ssa_num n
  | Memory_writes n -> "memory_writes" ^ ssa_num n
  | Channel (chan, n) -> (
      match chan with Chan_stdout -> "stdout" ^ ssa_num n | Chan_stderr -> "stderr" ^ ssa_num n
    )

let string_of_op = function
  | Bnot -> "@not"
  | Band -> "@and"
  | Bor -> "@or"
  | List_hd -> "@hd"
  | List_tl -> "@tl"
  | List_is_empty -> "@is_empty"
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
  | Ite -> "@ite"
  | String_eq -> "@string_eq"
  | Index n -> "@index::<" ^ string_of_int n ^ ">"

(* String representation of ctyps here is only for debugging and
   intermediate language pretty-printer. *)
let rec string_of_ctyp = function
  | CT_lint -> "%i"
  | CT_fint n -> "%i" ^ string_of_int n
  | CT_float n -> "%f" ^ string_of_int n
  | CT_rounding_mode -> "%rounding_mode"
  | CT_lbits -> "%bv"
  | CT_sbits n -> "%sbv" ^ string_of_int n
  | CT_fbits n -> "%bv" ^ string_of_int n
  | CT_constant n -> Big_int.to_string n
  | CT_unit -> "%unit"
  | CT_bool -> "%bool"
  | CT_real -> "%real"
  | CT_string -> "%string"
  | CT_memory_writes -> "%memory_writes"
  | CT_json -> "%json"
  | CT_json_key -> "%json_key"
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
  | CT_struct (id, ctyps) -> (
      "%struct "
      ^ Util.zencode_string (string_of_id id)
      ^ match ctyps with [] -> "" | ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
    )
  | CT_enum id -> "%enum " ^ Util.zencode_string (string_of_id id)
  | CT_variant (id, ctyps) -> (
      "%union "
      ^ Util.zencode_string (string_of_id id)
      ^ match ctyps with [] -> "" | ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
    )
  | CT_vector ctyp -> "%vec(" ^ string_of_ctyp ctyp ^ ")"
  | CT_fvector (n, ctyp) -> "%fvec(" ^ string_of_int n ^ ", " ^ string_of_ctyp ctyp ^ ")"
  | CT_list ctyp -> "%list(" ^ string_of_ctyp ctyp ^ ")"
  | CT_ref ctyp -> "&(" ^ string_of_ctyp ctyp ^ ")"
  | CT_poly kid -> string_of_kid kid

and string_of_uid (id, ctyps) =
  match ctyps with
  | [] -> Util.zencode_string (string_of_id id)
  | _ -> Util.zencode_string (string_of_id id) ^ "<" ^ Util.string_of_list "," string_of_ctyp ctyps ^ ">"

let string_of_value = function
  | VL_bits [] -> "UINT64_C(0)"
  | VL_bits bs -> Sail2_values.show_bitlist bs
  | VL_int i -> Big_int.to_string i
  | VL_bool true -> "true"
  | VL_bool false -> "false"
  | VL_unit -> "()"
  | VL_real str -> str
  | VL_string str -> "\"" ^ str ^ "\""
  | VL_enum element -> Util.zencode_string element
  | VL_ref r -> "&" ^ Util.zencode_string r
  | VL_undefined -> "undefined"

let rec string_of_cval = function
  | V_id (id, _) -> string_of_name id
  | V_member (id, _) -> Util.zencode_string (string_of_id id)
  | V_lit (VL_undefined, ctyp) -> string_of_value VL_undefined ^ " : " ^ string_of_ctyp ctyp
  | V_lit (vl, ctyp) -> string_of_value vl
  | V_call (op, cvals) -> Printf.sprintf "%s(%s)" (string_of_op op) (Util.string_of_list ", " string_of_cval cvals)
  | V_field (f, field, _) -> Printf.sprintf "%s.%s" (string_of_cval f) (Util.zencode_string (string_of_id field))
  | V_tuple_member (f, _, n) -> Printf.sprintf "%s.ztup%d" (string_of_cval f) n
  | V_ctor_kind (f, ctor) -> string_of_cval f ^ " is " ^ string_of_uid ctor
  | V_ctor_unwrap (f, ctor, _) -> string_of_cval f ^ " as " ^ string_of_uid ctor
  | V_struct (fields, ctyp) -> begin
      match ctyp with
      | CT_struct (id, _) ->
          Printf.sprintf "struct %s {%s}"
            (Util.zencode_string (string_of_id id))
            (Util.string_of_list ", "
               (fun (field, cval) -> Util.zencode_string (string_of_id field) ^ " = " ^ string_of_cval cval)
               fields
            )
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Struct without struct type found"
    end
  | V_tuple members -> "(" ^ Util.string_of_list ", " string_of_cval members ^ ")"

let rec string_of_clexp = function
  | CL_id (id, _) -> string_of_name id
  | CL_field (clexp, field, _) -> string_of_clexp clexp ^ "." ^ string_of_id field
  | CL_addr clexp -> string_of_clexp clexp ^ "*"
  | CL_tuple (clexp, n) -> string_of_clexp clexp ^ "." ^ string_of_int n
  | CL_void _ -> "void"
  | CL_rmw (id1, id2, _) -> Printf.sprintf "rmw(%s, %s)" (string_of_name id1) (string_of_name id2)

let string_of_creturn = function
  | CR_one clexp -> string_of_clexp clexp
  | CR_multi clexps -> "(" ^ Util.string_of_list ", " string_of_clexp clexps ^ ")"

let string_of_init = function
  | Init_cval cval -> string_of_cval cval
  | Init_static vl -> "static " ^ string_of_value vl
  | Init_json_key parts -> Util.string_of_list "." (fun part -> "\"" ^ part ^ "\"") parts

let rec doc_instr (I_aux (aux, _)) =
  let open Printf in
  let instr s = twice space ^^ string s in
  match aux with
  | I_decl (ctyp, id) -> ksprintf instr "%s : %s" (string_of_name id) (string_of_ctyp ctyp)
  | I_reset (ctyp, id) -> ksprintf instr "reset %s : %s" (string_of_name id) (string_of_ctyp ctyp)
  | I_init (ctyp, id, init) ->
      ksprintf instr "%s : %s = %s" (string_of_name id) (string_of_ctyp ctyp) (string_of_init init)
  | I_reinit (ctyp, id, cval) ->
      ksprintf instr "reinit %s : %s = %s" (string_of_name id) (string_of_ctyp ctyp) (string_of_cval cval)
  | I_clear (ctyp, id) -> ksprintf instr "clear %s : %s" (string_of_name id) (string_of_ctyp ctyp)
  | I_label label -> ksprintf string "%s:" label
  | I_jump (cval, label) -> ksprintf instr "jump %s goto %s" (string_of_cval cval) label
  | I_goto label -> ksprintf instr "goto %s" label
  | I_exit cause -> ksprintf instr "exit %s" cause
  | I_undefined ctyp -> ksprintf instr "arbitrary %s" (string_of_ctyp ctyp)
  | I_end id -> ksprintf instr "end %s" (string_of_name id)
  | I_raw str -> string str
  | I_comment str -> twice space ^^ string "//" ^^ string str
  | I_throw cval -> ksprintf instr "throw %s" (string_of_cval cval)
  | I_return cval -> ksprintf instr "return %s" (string_of_cval cval)
  | I_funcall (creturn, Call, uid, args) ->
      ksprintf instr "%s = %s(%s)" (string_of_creturn creturn) (string_of_uid uid)
        (Util.string_of_list ", " string_of_cval args)
  | I_funcall (creturn, Extern _, uid, args) ->
      ksprintf instr "%s = $%s(%s)" (string_of_creturn creturn) (string_of_uid uid)
        (Util.string_of_list ", " string_of_cval args)
  | I_copy (clexp, cval) -> ksprintf instr "%s = %s" (string_of_clexp clexp) (string_of_cval cval)
  | I_block instrs ->
      twice space ^^ char '{'
      ^^ nest 2 (hardline ^^ separate_map hardline doc_instr instrs)
      ^^ hardline ^^ twice space ^^ char '}'
  | I_try_block instrs ->
      twice space ^^ string "try {"
      ^^ nest 2 (hardline ^^ separate_map hardline doc_instr instrs)
      ^^ hardline ^^ twice space ^^ char '}'
  | I_if (cond, then_instrs, else_instrs) ->
      ksprintf instr "if %s {" (string_of_cval cond)
      ^^ nest 2 (hardline ^^ separate_map hardline doc_instr then_instrs)
      ^^ hardline ^^ twice space ^^ string "} else {"
      ^^ nest 2 (hardline ^^ separate_map hardline doc_instr else_instrs)
      ^^ hardline ^^ twice space ^^ char '}'

let string_of_instr i = Document.to_string (doc_instr i)

let rec clexp_ctyp = function
  | CL_id (_, ctyp) -> ctyp
  | CL_rmw (_, _, ctyp) -> ctyp
  | CL_field (_, _, ctyp) -> ctyp
  | CL_addr clexp -> begin
      match clexp_ctyp clexp with
      | CT_ref ctyp -> ctyp
      | ctyp -> failwith ("Bad ctyp for CL_addr " ^ string_of_ctyp ctyp)
    end
  | CL_tuple (clexp, n) -> begin
      match clexp_ctyp clexp with
      | CT_tup typs -> begin try List.nth typs n with _ -> failwith "Tuple assignment index out of bounds" end
      | ctyp -> failwith ("Bad ctyp for CL_tuple " ^ string_of_ctyp ctyp)
    end
  | CL_void ctyp -> ctyp

(* Define wrappers for creating bytecode instructions. Each function
   uses a counter to assign each instruction a unique identifier. *)

let instr_counter = ref 0

let instr_number () =
  let n = !instr_counter in
  incr instr_counter;
  n

let idecl l ctyp id = I_aux (I_decl (ctyp, id), (instr_number (), l))

let ireset l ctyp id = I_aux (I_reset (ctyp, id), (instr_number (), l))

let generate_static_var = symbol_generator ()

let istatic l ctyp value =
  let id = generate_static_var () in
  (id, I_aux (I_init (ctyp, id, Init_static value), (instr_number (), l)))

let iinit l ctyp id cval = I_aux (I_init (ctyp, id, Init_cval cval), (instr_number (), l))

let ijson_key l id parts = I_aux (I_init (CT_json_key, id, Init_json_key parts), (instr_number (), l))

let iif l cval then_instrs else_instrs = I_aux (I_if (cval, then_instrs, else_instrs), (instr_number (), l))

let ifuncall l clexp id cvals = I_aux (I_funcall (CR_one clexp, Call, id, cvals), (instr_number (), l))

let ifuncall_multi l clexps id cvals = I_aux (I_funcall (CR_multi clexps, Call, id, cvals), (instr_number (), l))

let iextern ?return_ctyp l clexp id cvals =
  let return_ctyp = match return_ctyp with None -> clexp_ctyp clexp | Some ctyp -> ctyp in
  I_aux (I_funcall (CR_one clexp, Extern return_ctyp, id, cvals), (instr_number (), l))

let icopy l clexp cval = I_aux (I_copy (clexp, cval), (instr_number (), l))

let iclear ?loc:(l = Parse_ast.Unknown) ctyp id = I_aux (I_clear (ctyp, id), (instr_number (), l))

let ireturn ?loc:(l = Parse_ast.Unknown) cval = I_aux (I_return cval, (instr_number (), l))

let iend l = I_aux (I_end (Return (-1)), (instr_number (), l))

let iend_name l name = I_aux (I_end name, (instr_number (), l))

let iblock ?loc:(l = Parse_ast.Unknown) instrs = I_aux (I_block instrs, (instr_number (), l))

let itry_block l instrs = I_aux (I_try_block instrs, (instr_number (), l))

let ithrow l cval = I_aux (I_throw cval, (instr_number (), l))

let icomment ?loc:(l = Parse_ast.Unknown) str = I_aux (I_comment str, (instr_number (), l))

let ilabel ?loc:(l = Parse_ast.Unknown) label = I_aux (I_label label, (instr_number (), l))

let igoto ?loc:(l = Parse_ast.Unknown) label = I_aux (I_goto label, (instr_number (), l))

let iundefined ?loc:(l = Parse_ast.Unknown) ctyp = I_aux (I_undefined ctyp, (instr_number (), l))

let imatch_failure l = I_aux (I_exit "match", (instr_number (), l))

let iexit l = I_aux (I_exit "explicit", (instr_number (), l))

let ibad_config l = I_aux (I_exit "bad config", (instr_number (), l))

let iraw ?loc:(l = Parse_ast.Unknown) str = I_aux (I_raw str, (instr_number (), l))

let ijump l cval label = I_aux (I_jump (cval, label), (instr_number (), l))

let rec map_ctyp f = function
  | ( CT_lint | CT_fint _ | CT_constant _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_float _ | CT_rounding_mode | CT_unit
    | CT_bool | CT_real | CT_string | CT_poly _ | CT_enum _ | CT_memory_writes | CT_json | CT_json_key ) as ctyp ->
      f ctyp
  | CT_tup ctyps -> f (CT_tup (List.map (map_ctyp f) ctyps))
  | CT_ref ctyp -> f (CT_ref (map_ctyp f ctyp))
  | CT_vector ctyp -> f (CT_vector (map_ctyp f ctyp))
  | CT_fvector (n, ctyp) -> f (CT_fvector (n, map_ctyp f ctyp))
  | CT_list ctyp -> f (CT_list (map_ctyp f ctyp))
  | CT_struct (id, ctyps) -> f (CT_struct (id, List.map (map_ctyp f) ctyps))
  | CT_variant (id, ctyps) -> f (CT_variant (id, List.map (map_ctyp f) ctyps))

let rec ctyp_has pred ctyp =
  pred ctyp
  ||
  match ctyp with
  | CT_lint | CT_fint _ | CT_constant _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_float _ | CT_rounding_mode | CT_unit
  | CT_bool | CT_real | CT_string | CT_poly _ | CT_enum _ | CT_memory_writes | CT_json | CT_json_key ->
      false
  | CT_struct (_, ctyps) | CT_variant (_, ctyps) | CT_tup ctyps -> List.exists (ctyp_has pred) ctyps
  | CT_ref ctyp | CT_vector ctyp | CT_fvector (_, ctyp) | CT_list ctyp -> ctyp_has pred ctyp

let rec ctyp_equal ctyp1 ctyp2 =
  match (ctyp1, ctyp2) with
  | CT_lint, CT_lint -> true
  | CT_lbits, CT_lbits -> true
  | CT_sbits m1, CT_sbits m2 -> m1 = m2
  | CT_fbits m1, CT_fbits m2 -> m1 = m2
  | CT_fint n, CT_fint m -> n = m
  | CT_float n, CT_float m -> n = m
  | CT_rounding_mode, CT_rounding_mode -> true
  | CT_constant n, CT_constant m -> Big_int.equal n m
  | CT_unit, CT_unit -> true
  | CT_bool, CT_bool -> true
  | CT_struct (id1, ctyps1), CT_struct (id2, ctyps2) when List.compare_lengths ctyps1 ctyps2 = 0 ->
      Id.compare id1 id2 = 0 && List.for_all2 ctyp_equal ctyps1 ctyps2
  | CT_enum id1, CT_enum id2 -> Id.compare id1 id2 = 0
  | CT_variant (id1, ctyps1), CT_variant (id2, ctyps2) when List.compare_lengths ctyps1 ctyps2 = 0 ->
      Id.compare id1 id2 = 0 && List.for_all2 ctyp_equal ctyps1 ctyps2
  | CT_tup ctyps1, CT_tup ctyps2 when List.length ctyps1 = List.length ctyps2 -> List.for_all2 ctyp_equal ctyps1 ctyps2
  | CT_string, CT_string -> true
  | CT_real, CT_real -> true
  | CT_vector ctyp1, CT_vector ctyp2 -> ctyp_equal ctyp1 ctyp2
  | CT_fvector (n1, ctyp1), CT_fvector (n2, ctyp2) -> n1 = n2 && ctyp_equal ctyp1 ctyp2
  | CT_list ctyp1, CT_list ctyp2 -> ctyp_equal ctyp1 ctyp2
  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_equal ctyp1 ctyp2
  | CT_memory_writes, CT_memory_writes -> true
  | CT_json, CT_json -> true
  | CT_json_key, CT_json_key -> true
  | CT_poly kid1, CT_poly kid2 -> Kid.compare kid1 kid2 = 0
  | _, _ -> false

let rec ctyp_compare ctyp1 ctyp2 =
  let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
  match (ctyp1, ctyp2) with
  | CT_lint, CT_lint -> 0
  | CT_lint, _ -> 1
  | _, CT_lint -> -1
  | CT_fint n, CT_fint m -> compare n m
  | CT_fint _, _ -> 1
  | _, CT_fint _ -> -1
  | CT_constant n, CT_constant m -> Big_int.compare n m
  | CT_constant _, _ -> 1
  | _, CT_constant _ -> -1
  | CT_fbits n, CT_fbits m -> compare n m
  | CT_fbits _, _ -> 1
  | _, CT_fbits _ -> -1
  | CT_sbits n, CT_sbits m -> compare n m
  | CT_sbits _, _ -> 1
  | _, CT_sbits _ -> -1
  | CT_lbits, CT_lbits -> 0
  | CT_lbits, _ -> 1
  | _, CT_lbits -> -1
  | CT_unit, CT_unit -> 0
  | CT_unit, _ -> 1
  | _, CT_unit -> -1
  | CT_real, CT_real -> 0
  | CT_real, _ -> 1
  | _, CT_real -> -1
  | CT_float n, CT_float m -> compare n m
  | CT_float _, _ -> 1
  | _, CT_float _ -> -1
  | CT_poly kid1, CT_poly kid2 -> Kid.compare kid1 kid2
  | CT_poly _, _ -> 1
  | _, CT_poly _ -> -1
  | CT_bool, CT_bool -> 0
  | CT_bool, _ -> 1
  | _, CT_bool -> -1
  | CT_string, CT_string -> 0
  | CT_string, _ -> 1
  | _, CT_string -> -1
  | CT_json, CT_json -> 0
  | CT_json, _ -> 1
  | _, CT_json -> -1
  | CT_json_key, CT_json_key -> 0
  | CT_json_key, _ -> 1
  | _, CT_json_key -> -1
  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_compare ctyp1 ctyp2
  | CT_ref _, _ -> 1
  | _, CT_ref _ -> -1
  | CT_list ctyp1, CT_list ctyp2 -> ctyp_compare ctyp1 ctyp2
  | CT_list _, _ -> 1
  | _, CT_list _ -> -1
  | CT_vector ctyp1, CT_vector ctyp2 -> ctyp_compare ctyp1 ctyp2
  | CT_vector _, _ -> 1
  | _, CT_vector _ -> -1
  | CT_fvector (n1, ctyp1), CT_fvector (n2, ctyp2) -> lex_ord (compare n1 n2) (ctyp_compare ctyp1 ctyp2)
  | CT_fvector _, _ -> 1
  | _, CT_fvector _ -> -1
  | CT_tup ctyps1, CT_tup ctyps2 -> Util.lex_ord_list ctyp_compare ctyps1 ctyps2
  | CT_tup _, _ -> 1
  | _, CT_tup _ -> -1
  | CT_struct (id1, ctyps1), CT_struct (id2, ctyps2) ->
      lex_ord (Id.compare id1 id2) (Util.lex_ord_list ctyp_compare ctyps1 ctyps2)
  | CT_struct _, _ -> 1
  | _, CT_struct _ -> -1
  | CT_variant (id1, ctyps1), CT_variant (id2, ctyps2) ->
      lex_ord (Id.compare id1 id2) (Util.lex_ord_list ctyp_compare ctyps1 ctyps2)
  | CT_variant _, _ -> 1
  | _, CT_variant _ -> -1
  | CT_enum id1, CT_enum id2 -> Id.compare id1 id2
  | CT_enum _, _ -> 1
  | _, CT_enum _ -> -1
  | CT_rounding_mode, CT_rounding_mode -> 0
  | CT_rounding_mode, _ -> 1
  | _, CT_rounding_mode -> -1
  | CT_memory_writes, CT_memory_writes -> 0

module CT = struct
  type t = ctyp
  let compare ctyp1 ctyp2 = ctyp_compare ctyp1 ctyp2
end

module CTList = struct
  type t = ctyp list
  let compare ctyps1 ctyps2 = Util.compare_list ctyp_compare ctyps1 ctyps2
end

module CTSet = Set.Make (CT)
module CTMap = Map.Make (CT)
module CTListSet = Set.Make (CTList)

let rec ctyp_vars = function
  | CT_poly kid -> KidSet.singleton kid
  | CT_list ctyp | CT_vector ctyp | CT_fvector (_, ctyp) | CT_ref ctyp -> ctyp_vars ctyp
  | CT_variant (_, ctyps) | CT_struct (_, ctyps) | CT_tup ctyps ->
      List.fold_left KidSet.union KidSet.empty (List.map ctyp_vars ctyps)
  | _ -> KidSet.empty

let rec ctyp_suprema = function
  | CT_lint -> CT_lint
  | CT_lbits -> CT_lbits
  | CT_fbits _ -> CT_lbits
  | CT_sbits _ -> CT_lbits
  | CT_fint _ -> CT_lint
  | CT_constant _ -> CT_lint
  | CT_unit -> CT_unit
  | CT_bool -> CT_bool
  | CT_real -> CT_real
  | CT_json -> CT_json
  | CT_json_key -> CT_json_key
  | CT_tup ctyps -> CT_tup (List.map ctyp_suprema ctyps)
  | CT_string -> CT_string
  | CT_float n -> CT_float n
  | CT_rounding_mode -> CT_rounding_mode
  | CT_memory_writes -> CT_memory_writes
  | CT_enum id -> CT_enum id
  (* Do we really never want to never call ctyp_suprema on constructor
     fields?  Doing it causes issues for structs (see
     test/c/stack_struct.sail) but it might be wrong to not call it
     for nested variants... *)
  | CT_struct (id, ctyps) -> CT_struct (id, ctyps)
  | CT_variant (id, ctyps) -> CT_variant (id, ctyps)
  | CT_vector ctyp -> CT_vector (ctyp_suprema ctyp)
  | CT_fvector (_, ctyp) -> CT_vector (ctyp_suprema ctyp)
  | CT_list ctyp -> CT_list (ctyp_suprema ctyp)
  | CT_ref ctyp -> CT_ref (ctyp_suprema ctyp)
  | CT_poly kid -> CT_poly kid

let merge_unifiers kid ctyp1 ctyp2 =
  if ctyp_equal ctyp1 ctyp2 then Some ctyp2
  else if ctyp_equal (ctyp_suprema ctyp1) (ctyp_suprema ctyp2) then Some (ctyp_suprema ctyp2)
  else
    Reporting.unreachable (kid_loc kid) __POS__
      ("Invalid unifiers in IR " ^ string_of_ctyp ctyp1 ^ " and " ^ string_of_ctyp ctyp2 ^ " for " ^ string_of_kid kid)

let rec ctyp_unify l ctyp1 ctyp2 =
  match (ctyp1, ctyp2) with
  | CT_tup ctyps1, CT_tup ctyps2 when List.length ctyps1 = List.length ctyps2 ->
      List.fold_left (KBindings.union merge_unifiers) KBindings.empty (List.map2 (ctyp_unify l) ctyps1 ctyps2)
  | CT_vector ctyp1, CT_vector ctyp2 -> ctyp_unify l ctyp1 ctyp2
  | CT_vector ctyp1, CT_fvector (_, ctyp2) -> ctyp_unify l ctyp1 ctyp2
  | CT_fvector (_, ctyp1), CT_vector ctyp2 -> ctyp_unify l ctyp1 ctyp2
  | CT_fvector (n1, ctyp1), CT_fvector (n2, ctyp2) when n1 = n2 -> ctyp_unify l ctyp1 ctyp2
  | CT_list ctyp1, CT_list ctyp2 -> ctyp_unify l ctyp1 ctyp2
  | CT_struct (id1, ctyps1), CT_struct (id2, ctyps2) when List.length ctyps1 == List.length ctyps2 ->
      List.fold_left (KBindings.union merge_unifiers) KBindings.empty (List.map2 (ctyp_unify l) ctyps1 ctyps2)
  | CT_variant (id1, ctyps1), CT_variant (id2, ctyps2) when List.length ctyps1 == List.length ctyps2 ->
      List.fold_left (KBindings.union merge_unifiers) KBindings.empty (List.map2 (ctyp_unify l) ctyps1 ctyps2)
  | CT_ref ctyp1, CT_ref ctyp2 -> ctyp_unify l ctyp1 ctyp2
  | CT_poly kid, _ -> KBindings.singleton kid ctyp2
  | _, _ when ctyp_equal ctyp1 ctyp2 -> KBindings.empty
  | CT_lbits, CT_fbits _ -> KBindings.empty
  | CT_lbits, CT_sbits _ -> KBindings.empty
  | CT_sbits n, CT_fbits m when m <= n -> KBindings.empty
  | CT_fbits _, CT_lbits -> KBindings.empty
  | CT_sbits _, CT_lbits -> KBindings.empty
  | CT_fbits n, CT_sbits m when n <= m -> KBindings.empty
  | CT_lint, CT_fint _ -> KBindings.empty
  | CT_fint _, CT_lint -> KBindings.empty
  | CT_lint, CT_constant _ -> KBindings.empty
  | CT_constant _, CT_lint -> KBindings.empty
  | CT_fint _, CT_constant _ -> KBindings.empty
  | CT_constant _, CT_fint _ -> KBindings.empty
  | _, _ ->
      Reporting.unreachable l __POS__ ("Invalid ctyp unifiers " ^ string_of_ctyp ctyp1 ^ " and " ^ string_of_ctyp ctyp2)

let rec ctyp_ids = function
  | CT_enum id -> IdSet.singleton id
  | CT_struct (id, ctyps) | CT_variant (id, ctyps) ->
      IdSet.add id (List.fold_left (fun ids ctyp -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctyps)
  | CT_tup ctyps -> List.fold_left (fun ids ctyp -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctyps
  | CT_vector ctyp | CT_fvector (_, ctyp) | CT_list ctyp | CT_ref ctyp -> ctyp_ids ctyp
  | CT_lint | CT_fint _ | CT_constant _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_string
  | CT_poly _ | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key ->
      IdSet.empty

let rec subst_poly substs = function
  | CT_poly kid -> begin match KBindings.find_opt kid substs with Some ctyp -> ctyp | None -> CT_poly kid end
  | CT_tup ctyps -> CT_tup (List.map (subst_poly substs) ctyps)
  | CT_list ctyp -> CT_list (subst_poly substs ctyp)
  | CT_vector ctyp -> CT_vector (subst_poly substs ctyp)
  | CT_fvector (n, ctyp) -> CT_fvector (n, subst_poly substs ctyp)
  | CT_ref ctyp -> CT_ref (subst_poly substs ctyp)
  | CT_variant (id, ctyps) -> CT_variant (id, List.map (subst_poly substs) ctyps)
  | CT_struct (id, ctyps) -> CT_struct (id, List.map (subst_poly substs) ctyps)
  | ( CT_lint | CT_fint _ | CT_constant _ | CT_unit | CT_bool | CT_string | CT_real | CT_lbits | CT_fbits _ | CT_sbits _
    | CT_enum _ | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key ) as ctyp ->
      ctyp

let rec is_polymorphic = function
  | CT_lint | CT_fint _ | CT_constant _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_string
  | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key ->
      false
  | CT_enum _ -> false
  | CT_tup ctyps | CT_struct (_, ctyps) | CT_variant (_, ctyps) -> List.exists is_polymorphic ctyps
  | CT_fvector (_, ctyp) | CT_vector ctyp | CT_list ctyp | CT_ref ctyp -> is_polymorphic ctyp
  | CT_poly _ -> true

let rec cval_deps = function
  | V_id (id, _) -> NameSet.singleton id
  | V_lit _ | V_member _ -> NameSet.empty
  | V_field (cval, _, _) | V_tuple_member (cval, _, _) -> cval_deps cval
  | V_call (_, cvals) | V_tuple cvals -> List.fold_left NameSet.union NameSet.empty (List.map cval_deps cvals)
  | V_ctor_kind (cval, _) -> cval_deps cval
  | V_ctor_unwrap (cval, _, _) -> cval_deps cval
  | V_struct (fields, _) -> List.fold_left (fun ns (_, cval) -> NameSet.union ns (cval_deps cval)) NameSet.empty fields

let rec clexp_deps = function
  | CL_id (id, _) -> (NameSet.empty, NameSet.singleton id)
  | CL_rmw (read, write, _) -> (NameSet.singleton read, NameSet.singleton write)
  | CL_field (clexp, _, _) -> clexp_deps clexp
  | CL_tuple (clexp, _) -> clexp_deps clexp
  | CL_addr clexp -> clexp_deps clexp
  | CL_void _ -> (NameSet.empty, NameSet.empty)

let creturn_deps = function
  | CR_one clexp -> clexp_deps clexp
  | CR_multi clexps ->
      List.fold_left
        (fun (reads, writes) clexp ->
          let new_reads, new_writes = clexp_deps clexp in
          (NameSet.union reads new_reads, NameSet.union writes new_writes)
        )
        (NameSet.empty, NameSet.empty) clexps

let init_deps = function Init_cval cval -> cval_deps cval | Init_static _ | Init_json_key _ -> NameSet.empty

let rec instr_deps ~direct = function
  | I_decl (_, id) -> (NameSet.empty, NameSet.singleton id)
  | I_reset (_, id) -> (NameSet.empty, NameSet.singleton id)
  | I_init (_, id, init) -> (init_deps init, NameSet.singleton id)
  | I_reinit (_, id, cval) -> (cval_deps cval, NameSet.singleton id)
  | I_if (cval, then_instrs, else_instrs) ->
      let cond_reads = cval_deps cval in
      if direct then (cond_reads, NameSet.empty)
      else (
        let then_reads, then_writes = instrs_deps ~direct:false then_instrs in
        let else_reads, else_writes = instrs_deps ~direct:false else_instrs in
        (NameSet.union cond_reads (NameSet.union then_reads else_reads), NameSet.union then_writes else_writes)
      )
  | I_jump (cval, _) -> (cval_deps cval, NameSet.empty)
  | I_funcall (creturn, _, _, cvals) ->
      let reads, writes = creturn_deps creturn in
      (List.fold_left NameSet.union reads (List.map cval_deps cvals), writes)
  | I_copy (clexp, cval) ->
      let reads, writes = clexp_deps clexp in
      (NameSet.union reads (cval_deps cval), writes)
  | I_clear (_, id) -> (NameSet.singleton id, NameSet.empty)
  | I_throw cval | I_return cval -> (cval_deps cval, NameSet.empty)
  | I_block instrs | I_try_block instrs ->
      if direct then (NameSet.empty, NameSet.empty) else instrs_deps ~direct:false instrs
  | I_comment _ | I_raw _ | I_label _ | I_goto _ | I_undefined _ | I_exit _ -> (NameSet.empty, NameSet.empty)
  | I_end id -> (NameSet.singleton id, NameSet.empty)

and instrs_deps ~direct instrs =
  List.fold_left
    (fun (reads, writes) (I_aux (instr, _)) ->
      let reads', writes' = instr_deps ~direct:false instr in
      (NameSet.union reads reads', NameSet.union writes writes')
    )
    (NameSet.empty, NameSet.empty) instrs

let is_reference_to id = function Some id' -> Name.compare id id' = 0 | None -> false

let rec cval_references read = function
  | V_id (id, _) -> is_reference_to id read
  | V_lit _ | V_member _ -> false
  | V_field (cval, _, _) | V_tuple_member (cval, _, _) | V_ctor_kind (cval, _) | V_ctor_unwrap (cval, _, _) ->
      cval_references read cval
  | V_call (_, cvals) | V_tuple cvals -> List.exists (cval_references read) cvals
  | V_struct (fields, _) -> List.exists (fun (_, cval) -> cval_references read cval) fields

let init_references read = function
  | Init_cval cval -> cval_references read cval
  | Init_json_key _ | Init_static _ -> false

let rec clexp_references ?read ?write = function
  | CL_id (id, _) -> is_reference_to id write
  | CL_rmw (read', write', _) -> is_reference_to read' read || is_reference_to write' write
  | CL_field (clexp, _, _) | CL_tuple (clexp, _) | CL_addr clexp -> clexp_references ?read ?write clexp
  | CL_void _ -> false

let creturn_references ?read ?write = function
  | CR_one clexp -> clexp_references ?read ?write clexp
  | CR_multi clexps -> List.exists (clexp_references ?read ?write) clexps

let rec instr_references ?read ?write ~direct (I_aux (instr, _)) =
  match instr with
  | I_decl (_, id) | I_reset (_, id) | I_clear (_, id) -> is_reference_to id write
  | I_init (_, id, init) -> is_reference_to id write || init_references read init
  | I_reinit (_, id, cval) -> is_reference_to id write || cval_references read cval
  | I_if (cval, then_instrs, else_instrs) ->
      if direct then cval_references read cval
      else
        cval_references read cval
        || instrs_references ?read ?write ~direct:false then_instrs
        || instrs_references ?read ?write ~direct:false else_instrs
  | I_jump (cval, _) | I_throw cval | I_return cval -> cval_references read cval
  | I_funcall (creturn, _, _, cvals) ->
      creturn_references ?read ?write creturn || List.exists (cval_references read) cvals
  | I_copy (clexp, cval) -> clexp_references ?read ?write clexp || cval_references read cval
  | I_block instrs | I_try_block instrs -> if direct then false else instrs_references ?read ?write ~direct:false instrs
  | I_comment _ | I_raw _ | I_label _ | I_goto _ | I_undefined _ | I_exit _ -> false
  | I_end id -> is_reference_to id read

and instrs_references ?read ?write ~direct instrs = List.exists (instr_references ?read ?write ~direct) instrs

module NameCT = struct
  type t = name * ctyp
  let compare (n1, ctyp1) (n2, ctyp2) =
    let c = Name.compare n1 n2 in
    if c = 0 then CT.compare ctyp1 ctyp2 else c
end

module NameCTSet = Set.Make (NameCT)
module NameCTMap = Map.Make (NameCT)

let rec clexp_typed_writes = function
  | CL_id (id, ctyp) -> NameCTSet.singleton (id, ctyp)
  | CL_rmw (_, id, ctyp) -> NameCTSet.singleton (id, ctyp)
  | CL_field (clexp, _, _) -> clexp_typed_writes clexp
  | CL_tuple (clexp, _) -> clexp_typed_writes clexp
  | CL_addr clexp -> clexp_typed_writes clexp
  | CL_void _ -> NameCTSet.empty

let creturn_typed_writes = function
  | CR_one clexp -> clexp_typed_writes clexp
  | CR_multi clexps ->
      List.fold_left (fun writes clexp -> NameCTSet.union writes (clexp_typed_writes clexp)) NameCTSet.empty clexps

let instr_typed_writes (I_aux (aux, _)) =
  match aux with
  | I_decl (ctyp, id) | I_reset (ctyp, id) -> NameCTSet.singleton (id, ctyp)
  | I_init (ctyp, id, _) | I_reinit (ctyp, id, _) -> NameCTSet.singleton (id, ctyp)
  | I_copy (clexp, _) -> clexp_typed_writes clexp
  | I_funcall (creturn, _, _, _) -> creturn_typed_writes creturn
  | _ -> NameCTSet.empty

let rec map_clexp_ctyp f = function
  | CL_id (id, ctyp) -> CL_id (id, f ctyp)
  | CL_rmw (read, write, ctyp) -> CL_rmw (read, write, f ctyp)
  | CL_field (clexp, id, ctyp) -> CL_field (map_clexp_ctyp f clexp, id, f ctyp)
  | CL_tuple (clexp, n) -> CL_tuple (map_clexp_ctyp f clexp, n)
  | CL_addr clexp -> CL_addr (map_clexp_ctyp f clexp)
  | CL_void ctyp -> CL_void (f ctyp)

let rec map_cval_ctyp f = function
  | V_id (id, ctyp) -> V_id (id, f ctyp)
  | V_member (id, ctyp) -> V_member (id, f ctyp)
  | V_lit (vl, ctyp) -> V_lit (vl, f ctyp)
  | V_ctor_kind (cval, (id, unifiers)) -> V_ctor_kind (map_cval_ctyp f cval, (id, List.map f unifiers))
  | V_ctor_unwrap (cval, (id, unifiers), ctyp) -> V_ctor_unwrap (map_cval_ctyp f cval, (id, List.map f unifiers), f ctyp)
  | V_tuple_member (cval, i, j) -> V_tuple_member (map_cval_ctyp f cval, i, j)
  | V_call (op, cvals) -> V_call (op, List.map (map_cval_ctyp f) cvals)
  | V_field (cval, id, ctyp) -> V_field (map_cval_ctyp f cval, id, f ctyp)
  | V_struct (fields, ctyp) -> V_struct (List.map (fun (id, cval) -> (id, map_cval_ctyp f cval)) fields, f ctyp)
  | V_tuple members -> V_tuple (List.map (map_cval_ctyp f) members)

let map_creturn_ctyp f = function
  | CR_one clexp -> CR_one (map_clexp_ctyp f clexp)
  | CR_multi clexps -> CR_multi (List.map (map_clexp_ctyp f) clexps)

let map_init_ctyp f init =
  match init with Init_cval cval -> Init_cval (map_cval_ctyp f cval) | Init_static _ | Init_json_key _ -> init

let map_extern_ctyp f = function Call -> Call | Extern ctyp -> Extern (f ctyp)

let rec map_instr_ctyp f (I_aux (instr, aux)) =
  let instr =
    match instr with
    | I_decl (ctyp, id) -> I_decl (f ctyp, id)
    | I_init (ctyp, id, init) -> I_init (f ctyp, id, map_init_ctyp f init)
    | I_if (cval, then_instrs, else_instrs) ->
        I_if (map_cval_ctyp f cval, List.map (map_instr_ctyp f) then_instrs, List.map (map_instr_ctyp f) else_instrs)
    | I_jump (cval, label) -> I_jump (map_cval_ctyp f cval, label)
    | I_funcall (creturn, extern, (id, ctyps), cvals) ->
        I_funcall
          ( map_creturn_ctyp f creturn,
            map_extern_ctyp f extern,
            (id, List.map f ctyps),
            List.map (map_cval_ctyp f) cvals
          )
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
    | (I_comment _ | I_raw _ | I_label _ | I_goto _ | I_exit _) as instr -> instr
  in
  I_aux (instr, aux)

let map_instr_cval f = visit_instr (new map_cval_visitor f)

class instr_visitor f : jib_visitor =
  object
    inherit empty_jib_visitor

    method! vcval _ = SkipChildren
    method! vctyp _ = SkipChildren
    method! vclexp _ = SkipChildren

    method! vinstr instr = ChangeDoChildrenPost (instr, f)
  end

let map_instr f = visit_instr (new instr_visitor f)

let rec concatmap_instr f (I_aux (instr, aux)) =
  let instr =
    match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _ | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _
    | I_return _ | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_exit _ | I_undefined _ | I_end _ ->
        instr
    | I_if (cval, instrs1, instrs2) ->
        I_if
          (cval, List.concat (List.map (concatmap_instr f) instrs1), List.concat (List.map (concatmap_instr f) instrs2))
    | I_block instrs -> I_block (List.concat (List.map (concatmap_instr f) instrs))
    | I_try_block instrs -> I_try_block (List.concat (List.map (concatmap_instr f) instrs))
  in
  f (I_aux (instr, aux))

let rec iter_instr f (I_aux (instr, aux)) =
  match instr with
  | I_decl _ | I_init _ | I_reset _ | I_reinit _ | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _
  | I_return _ | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_exit _ | I_undefined _ | I_end _ ->
      f (I_aux (instr, aux))
  | I_if (_, instrs1, instrs2) ->
      List.iter (iter_instr f) instrs1;
      List.iter (iter_instr f) instrs2
  | I_block instrs | I_try_block instrs -> List.iter (iter_instr f) instrs

let cdef_map_instr f = visit_cdef (new instr_visitor f)

let rec map_funcall f instrs =
  match instrs with
  | [] -> []
  | (I_aux (I_funcall _, _) as funcall_instr) :: tail -> begin
      match tail with
      | (I_aux (I_if (V_id (id, CT_bool), _, []), _) as exception_instr) :: tail'
        when Name.compare id have_exception == 0 ->
          f funcall_instr [exception_instr] @ map_funcall f tail'
      | _ -> f funcall_instr [] @ map_funcall f tail
    end
  | I_aux (instr, aux) :: tail ->
      let instr =
        match instr with
        | I_decl _ | I_init _ | I_reset _ | I_reinit _ | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _
        | I_return _ | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_exit _ | I_undefined _ | I_end _ ->
            instr
        | I_if (cval, instrs1, instrs2) -> I_if (cval, map_funcall f instrs1, map_funcall f instrs2)
        | I_block instrs -> I_block (map_funcall f instrs)
        | I_try_block instrs -> I_try_block (map_funcall f instrs)
      in
      I_aux (instr, aux) :: map_funcall f tail

let ctype_def_map_funcall f = function
  | CTD_abstract (id, ctyp, CTDI_instrs instrs) -> CTD_abstract (id, ctyp, CTDI_instrs (map_funcall f instrs))
  | ctd -> ctd

let cdef_aux_map_funcall f = function
  | CDEF_register (id, ctyp, instrs) -> CDEF_register (id, ctyp, map_funcall f instrs)
  | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, map_funcall f instrs)
  | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, map_funcall f instrs)
  | CDEF_startup (id, instrs) -> CDEF_startup (id, map_funcall f instrs)
  | CDEF_finish (id, instrs) -> CDEF_finish (id, map_funcall f instrs)
  | CDEF_val (id, tyvars, ctyps, ctyp, extern) -> CDEF_val (id, tyvars, ctyps, ctyp, extern)
  | CDEF_type tdef -> CDEF_type (ctype_def_map_funcall f tdef)
  | CDEF_pragma (name, str) -> CDEF_pragma (name, str)

let cdef_map_funcall f (CDEF_aux (aux, def_annot)) = CDEF_aux (cdef_aux_map_funcall f aux, def_annot)

let ctype_def_concatmap_instr f = function
  | CTD_abstract (id, ctyp, CTDI_instrs instrs) ->
      CTD_abstract (id, ctyp, CTDI_instrs (List.concat (List.map (concatmap_instr f) instrs)))
  | ctd -> ctd

let cdef_aux_concatmap_instr f = function
  | CDEF_register (id, ctyp, instrs) -> CDEF_register (id, ctyp, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_fundef (id, heap_return, args, instrs) ->
      CDEF_fundef (id, heap_return, args, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_startup (id, instrs) -> CDEF_startup (id, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_finish (id, instrs) -> CDEF_finish (id, List.concat (List.map (concatmap_instr f) instrs))
  | CDEF_val (id, tyvars, ctyps, ctyp, extern) -> CDEF_val (id, tyvars, ctyps, ctyp, extern)
  | CDEF_type tdef -> CDEF_type (ctype_def_concatmap_instr f tdef)
  | CDEF_pragma (name, str) -> CDEF_pragma (name, str)

let cdef_concatmap_instr f (CDEF_aux (aux, def_annot)) = CDEF_aux (cdef_aux_concatmap_instr f aux, def_annot)

let ctype_def_map_ctyp f = function
  | CTD_abstract (id, ctyp, inst) -> CTD_abstract (id, f ctyp, inst)
  | CTD_enum (id, ids) -> CTD_enum (id, ids)
  | CTD_abbrev (id, ctyp) -> CTD_abbrev (id, f ctyp)
  | CTD_struct (id, tyvars, ctors) -> CTD_struct (id, tyvars, List.map (fun (id, ctyp) -> (id, f ctyp)) ctors)
  | CTD_variant (id, tyvars, ctors) -> CTD_variant (id, tyvars, List.map (fun (id, ctyp) -> (id, f ctyp)) ctors)

(* Map over each ctyp in a cdef using map_instr_ctyp *)
let cdef_aux_map_ctyp f = function
  | CDEF_register (id, ctyp, instrs) -> CDEF_register (id, f ctyp, List.map (map_instr_ctyp f) instrs)
  | CDEF_let (n, bindings, instrs) ->
      CDEF_let (n, List.map (fun (id, ctyp) -> (id, f ctyp)) bindings, List.map (map_instr_ctyp f) instrs)
  | CDEF_fundef (id, heap_return, args, instrs) ->
      CDEF_fundef (id, heap_return, args, List.map (map_instr_ctyp f) instrs)
  | CDEF_startup (id, instrs) -> CDEF_startup (id, List.map (map_instr_ctyp f) instrs)
  | CDEF_finish (id, instrs) -> CDEF_finish (id, List.map (map_instr_ctyp f) instrs)
  | CDEF_val (id, tyvars, ctyps, ctyp, extern) -> CDEF_val (id, tyvars, List.map f ctyps, f ctyp, extern)
  | CDEF_type tdef -> CDEF_type (ctype_def_map_ctyp f tdef)
  | CDEF_pragma (name, str) -> CDEF_pragma (name, str)

let cdef_map_ctyp f (CDEF_aux (aux, def_annot)) = CDEF_aux (cdef_aux_map_ctyp f aux, def_annot)

let cdef_map_cval f = cdef_map_instr (map_instr_cval f)

(* Map over all sequences of instructions contained within an instruction *)
let rec map_instrs f (I_aux (instr, aux)) =
  let instr =
    match instr with
    | I_decl _ | I_init _ | I_reset _ | I_reinit _ -> instr
    | I_if (cval, instrs1, instrs2) ->
        I_if (cval, f (List.map (map_instrs f) instrs1), f (List.map (map_instrs f) instrs2))
    | I_funcall _ | I_copy _ | I_clear _ | I_jump _ | I_throw _ | I_return _ -> instr
    | I_block instrs -> I_block (f (List.map (map_instrs f) instrs))
    | I_try_block instrs -> I_try_block (f (List.map (map_instrs f) instrs))
    | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_exit _ | I_undefined _ | I_end _ -> instr
  in
  I_aux (instr, aux)

let map_instr_list f instrs = List.map (map_instr f) instrs

let instr_ids ~direct (I_aux (instr, _)) =
  let reads, writes = instr_deps ~direct instr in
  NameSet.union reads writes

let instr_reads ~direct (I_aux (instr, _)) = fst (instr_deps ~direct instr)

let instr_writes ~direct (I_aux (instr, _)) = snd (instr_deps ~direct instr)

let rec filter_instrs f instrs =
  let filter_instrs' instr =
    match instr with
    | I_aux (I_block instrs, aux) ->
        let instrs' = filter_instrs f instrs in
        if instrs == instrs' then instr else I_aux (I_block instrs', aux)
    | I_aux (I_try_block instrs, aux) ->
        let instrs' = filter_instrs f instrs in
        if instrs == instrs' then instr else I_aux (I_try_block instrs', aux)
    | I_aux (I_if (cval, instrs1, instrs2), aux) ->
        let instrs1' = filter_instrs f instrs1 in
        let instrs2' = filter_instrs f instrs2 in
        if instrs1 == instrs1' && instrs2 == instrs2' then instr else I_aux (I_if (cval, instrs1', instrs2'), aux)
    | _ -> instr
  in
  let instrs = map_no_copy filter_instrs' instrs in
  if List.exists (fun i -> not (f i)) instrs then List.filter f instrs else instrs

(* GLOBAL: label_counter is used to make sure all labels have unique
   names. Like gensym_counter it should be safe to reset between
   top-level definitions. **)
let label_counter = ref 0

let label str =
  let str = str ^ string_of_int !label_counter in
  incr label_counter;
  str

let rec infer_call op vs =
  match (op, vs) with
  | Bnot, _ -> CT_bool
  | Band, _ -> CT_bool
  | Bor, _ -> CT_bool
  | List_hd, [v] -> begin
      match cval_ctyp v with
      | CT_list ctyp -> ctyp
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid call to hd"
    end
  | List_tl, [v] -> begin
      match cval_ctyp v with
      | CT_list ctyp -> CT_list ctyp
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid call to tl"
    end
  | List_is_empty, [v] -> begin
      match cval_ctyp v with
      | CT_list ctyp -> CT_list ctyp
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid call to is_empty"
    end
  | (Eq | Neq), _ -> CT_bool
  | Bvnot, [v] -> cval_ctyp v
  | Bvaccess, _ -> CT_fbits 1
  | (Bvor | Bvand | Bvxor | Bvadd | Bvsub), [v; _] -> cval_ctyp v
  | (Ilt | Igt | Ilteq | Igteq), _ -> CT_bool
  | (Iadd | Isub), _ -> CT_fint 64
  | (Unsigned n | Signed n), _ -> CT_fint n
  | (Zero_extend n | Sign_extend n), [v] -> begin
      match cval_ctyp v with
      | CT_fbits _ | CT_sbits _ -> CT_fbits n
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for zero/sign_extend argument"
    end
  | Slice n, [vec; _] -> begin
      match cval_ctyp vec with
      | CT_fbits _ | CT_sbits _ -> CT_fbits n
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for extract argument"
    end
  | Sslice n, [vec; _; _] -> begin
      match cval_ctyp vec with
      | CT_fbits _ | CT_sbits _ -> CT_sbits n
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for extract argument"
    end
  | Set_slice, [vec; _; _] -> cval_ctyp vec
  | Replicate n, [vec] -> begin
      match cval_ctyp vec with
      | CT_fbits m -> CT_fbits (n * m)
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for replicate argument"
    end
  | Concat, [v1; v2] -> begin
      match (cval_ctyp v1, cval_ctyp v2) with
      | CT_fbits n, CT_fbits m -> CT_fbits (n + m)
      | CT_fbits n, CT_sbits m -> CT_sbits m
      | CT_sbits n, CT_fbits m -> CT_sbits n
      | CT_sbits n, CT_sbits m -> CT_sbits (max n m)
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for concat argument"
    end
  | Ite, [_; t; _] -> cval_ctyp t
  | String_eq, _ -> CT_bool
  | Index _, [v] -> (
      match cval_ctyp v with
      | CT_fvector (_, ctyp) -> ctyp
      | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid type for index argument"
    )
  | _, _ -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Invalid call to function " ^ string_of_op op)

and cval_ctyp = function
  | V_id (_, ctyp) -> ctyp
  | V_member (_, ctyp) -> ctyp
  | V_lit (_, ctyp) -> ctyp
  | V_ctor_kind _ -> CT_bool
  | V_ctor_unwrap (_, _, ctyp) -> ctyp
  | V_tuple_member (cval, _, n) -> begin
      match cval_ctyp cval with
      | CT_tup ctyps -> List.nth ctyps n
      | ctyp -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Invalid tuple type " ^ string_of_ctyp ctyp)
    end
  | V_field (cval, field, ctyp) -> ctyp
  | V_struct (_, ctyp) -> ctyp
  | V_tuple cvals -> CT_tup (List.map cval_ctyp cvals)
  | V_call (op, vs) -> infer_call op vs

let creturn_ctyp = function CR_one clexp -> clexp_ctyp clexp | CR_multi clexps -> CT_tup (List.map clexp_ctyp clexps)

let init_ctyps = function
  | Init_cval cval -> CTSet.singleton (cval_ctyp cval)
  | Init_static _ | Init_json_key _ -> CTSet.empty

let rec instr_ctyps (I_aux (instr, aux)) =
  match instr with
  | I_decl (ctyp, _) | I_reset (ctyp, _) | I_clear (ctyp, _) | I_undefined ctyp -> CTSet.singleton ctyp
  | I_init (ctyp, _, init) -> CTSet.add ctyp (init_ctyps init)
  | I_reinit (ctyp, _, cval) -> CTSet.add ctyp (CTSet.singleton (cval_ctyp cval))
  | I_if (cval, instrs1, instrs2) ->
      CTSet.union (instrs_ctyps instrs1) (instrs_ctyps instrs2) |> CTSet.add (cval_ctyp cval)
  | I_funcall (creturn, _, (_, ctyps), cvals) ->
      List.fold_left (fun m ctyp -> CTSet.add ctyp m) CTSet.empty (List.map cval_ctyp cvals)
      |> CTSet.union (CTSet.of_list ctyps)
      |> CTSet.add (creturn_ctyp creturn)
  | I_copy (clexp, cval) -> CTSet.add (clexp_ctyp clexp) (CTSet.singleton (cval_ctyp cval))
  | I_block instrs | I_try_block instrs -> instrs_ctyps instrs
  | I_throw cval | I_jump (cval, _) | I_return cval -> CTSet.singleton (cval_ctyp cval)
  | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_exit _ | I_end _ -> CTSet.empty

and instrs_ctyps instrs = List.fold_left CTSet.union CTSet.empty (List.map instr_ctyps instrs)

let ctype_def_ctyps = function
  | CTD_enum _ | CTD_abstract _ -> []
  | CTD_abbrev (_, ctyp) -> [ctyp]
  | CTD_struct (_, _, fields) -> List.map snd fields
  | CTD_variant (_, _, ctors) -> List.map snd ctors

let ctype_def_id = function
  | CTD_abstract (id, _, _) | CTD_enum (id, _) | CTD_abbrev (id, _) | CTD_struct (id, _, _) | CTD_variant (id, _, _) ->
      id

let ctype_def_to_ctyp = function
  | CTD_abstract (id, ctyp, _) -> ctyp
  | CTD_abbrev (_, ctyp) -> ctyp
  | CTD_enum (id, _) -> CT_enum id
  | CTD_struct (id, tyvars, fields) -> CT_struct (id, List.map (fun v -> CT_poly v) tyvars)
  | CTD_variant (id, tyvars, ctors) -> CT_variant (id, List.map (fun v -> CT_poly v) tyvars)

let cdef_ctyps (CDEF_aux (aux, _)) =
  match aux with
  | CDEF_register (_, ctyp, instrs) -> CTSet.add ctyp (instrs_ctyps instrs)
  | CDEF_val (_, _, ctyps, ctyp, _) -> CTSet.add ctyp (List.fold_left (fun m ctyp -> CTSet.add ctyp m) CTSet.empty ctyps)
  | CDEF_fundef (_, _, _, instrs) | CDEF_startup (_, instrs) | CDEF_finish (_, instrs) -> instrs_ctyps instrs
  | CDEF_type tdef -> List.fold_right CTSet.add (ctype_def_ctyps tdef) CTSet.empty
  | CDEF_let (_, bindings, instrs) ->
      List.fold_left (fun m ctyp -> CTSet.add ctyp m) CTSet.empty (List.map snd bindings)
      |> CTSet.union (instrs_ctyps instrs)
  | CDEF_pragma (_, _) -> CTSet.empty

let instr_split_at f =
  let rec instr_split_at' f before = function
    | [] -> (List.rev before, [])
    | instr :: instrs when f instr -> (List.rev before, instr :: instrs)
    | instr :: instrs -> instr_split_at' f (instr :: before) instrs
  in
  instr_split_at' f []

let rec cval_has_ctyp pred = function
  | V_id (_, ctyp) | V_member (_, ctyp) | V_lit (_, ctyp) -> pred ctyp
  | V_field (cval, _, ctyp) -> cval_has_ctyp pred cval || pred ctyp
  | V_tuple_member (cval, _, _) -> cval_has_ctyp pred cval
  | V_tuple cvals | V_call (_, cvals) -> List.exists (cval_has_ctyp pred) cvals
  | V_ctor_kind (cval, (_, ctyps)) -> cval_has_ctyp pred cval || List.exists pred ctyps
  | V_ctor_unwrap (cval, (_, ctyps), ctyp) -> cval_has_ctyp pred cval || List.exists pred ctyps || pred ctyp
  | V_struct (fields, ctyp) -> List.exists (fun (_, cval) -> cval_has_ctyp pred cval) fields || pred ctyp

let rec clexp_has_ctyp pred = function
  | CL_id (_, ctyp) | CL_rmw (_, _, ctyp) | CL_void ctyp -> pred ctyp
  | CL_field (clexp, _, ctyp) -> clexp_has_ctyp pred clexp || pred ctyp
  | CL_addr clexp | CL_tuple (clexp, _) -> clexp_has_ctyp pred clexp

let creturn_has_ctyp pred = function
  | CR_one clexp -> clexp_has_ctyp pred clexp
  | CR_multi clexps -> List.exists (clexp_has_ctyp pred) clexps

let init_has_ctyp pred = function Init_cval cval -> cval_has_ctyp pred cval | Init_static _ | Init_json_key _ -> false

let rec instr_has_ctyp pred (I_aux (aux, _)) =
  match aux with
  | I_decl (ctyp, _) | I_reset (ctyp, _) | I_clear (ctyp, _) | I_undefined ctyp -> pred ctyp
  | I_init (ctyp, _, init) -> pred ctyp || init_has_ctyp pred init
  | I_reinit (ctyp, _, cval) -> pred ctyp || cval_has_ctyp pred cval
  | I_jump (cval, _) | I_throw cval | I_return cval -> cval_has_ctyp pred cval
  | I_copy (clexp, cval) -> clexp_has_ctyp pred clexp || cval_has_ctyp pred cval
  | I_if (i, t, e) -> cval_has_ctyp pred i || List.exists (instr_has_ctyp pred) t || List.exists (instr_has_ctyp pred) e
  | I_block instrs | I_try_block instrs -> List.exists (instr_has_ctyp pred) instrs
  | I_funcall (creturn, _, (_, ctyps), cvals) ->
      creturn_has_ctyp pred creturn || List.exists pred ctyps || List.exists (cval_has_ctyp pred) cvals
  | I_goto _ | I_label _ | I_comment _ | I_raw _ | I_end _ | I_exit _ -> false

let ctype_def_has_ctyp pred = function
  | CTD_enum _ | CTD_abstract _ -> false
  | CTD_abbrev (_, ctyp) -> pred ctyp
  | CTD_struct (_, _, fields) -> List.exists (fun (_, ctyp) -> pred ctyp) fields
  | CTD_variant (_, _, ctors) -> List.exists (fun (_, ctyp) -> pred ctyp) ctors

let cdef_has_ctyp pred (CDEF_aux (aux, _)) =
  match aux with
  | CDEF_register (_, ctyp, instrs) -> pred ctyp || List.exists (instr_has_ctyp pred) instrs
  | CDEF_val (_, _, ctyps, ctyp, _) -> List.exists pred ctyps || pred ctyp
  | CDEF_fundef (_, _, _, instrs) | CDEF_startup (_, instrs) | CDEF_finish (_, instrs) ->
      List.exists (instr_has_ctyp pred) instrs
  | CDEF_type tdef -> ctype_def_has_ctyp pred tdef
  | CDEF_let (_, bindings, instrs) ->
      List.exists (fun (_, ctyp) -> pred ctyp) bindings || List.exists (instr_has_ctyp pred) instrs
  | CDEF_pragma _ -> false
