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

open Libsail

open Ast
open Ast_util
open Jib
open Jib_util
open Value2
open Printf

let zencode_id id = Util.zencode_string (string_of_id id)

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let string_of_name =
  let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n in
  function
  | Gen (v1, v2, n) -> Util.zencode_string (string_of_int v1 ^ "." ^ string_of_int v2) ^ ssa_num n
  | Name (id, n) -> zencode_id id ^ ssa_num n
  | Have_exception n -> "have_exception" ^ ssa_num n
  | Return n -> "return" ^ ssa_num n
  | Current_exception n -> "current_exception" ^ ssa_num n
  | Throw_location n -> "throw_location" ^ ssa_num n
  | Abstract _ | Channel _ | Memory_writes _ ->
      raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Unexpected identifier found during IR generation")

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
  | CL_id (id, ctyp) -> string_of_name id
  | CL_field (clexp, field, _) -> string_of_clexp clexp ^ "." ^ zencode_id field
  | CL_addr clexp -> string_of_clexp clexp ^ "*"
  | CL_tuple (clexp, n) -> string_of_clexp clexp ^ "." ^ string_of_int n
  | CL_void _ -> "void"
  | CL_rmw _ -> assert false

let string_of_creturn = function
  | CR_one clexp -> string_of_clexp clexp
  | CR_multi clexps -> "(" ^ Util.string_of_list ", " string_of_clexp clexps ^ ")"

let add_instr n buf indent str =
  Buffer.add_string buf (String.make indent ' ');
  Buffer.add_string buf str;
  Buffer.add_string buf ";\n"

module Ir_formatter = struct
  module type Config = sig
    type label
    val make_label_map : instr list -> label StringMap.t
    val output_label_instr : Buffer.t -> label StringMap.t -> string -> unit
    val string_of_label : label -> string
    val modify_instrs : instr list -> instr list
    val keyword : string -> string
    val typ : ctyp -> string
    val value : cval -> string
  end

  module Make (C : Config) = struct
    let file_map = ref []

    let file_number file_name =
      let rec scan n = function
        | f :: fs -> if f = file_name then n else scan (n + 1) fs
        | [] ->
            file_map := !file_map @ [file_name];
            n
      in
      scan 0 !file_map

    let unknown_loc_counter = ref 0

    let abstract_functions = ref StringSet.empty

    let output_loc l =
      match Reporting.simp_loc l with
      | None ->
          incr unknown_loc_counter;
          Printf.sprintf " `%d" !unknown_loc_counter
      | Some (p1, p2) ->
          Printf.sprintf " `%d %d:%d-%d:%d" (file_number p1.pos_fname) p1.pos_lnum (p1.pos_cnum - p1.pos_bol)
            p2.pos_lnum (p2.pos_cnum - p2.pos_bol)

    let output_files buf =
      Buffer.add_string buf (C.keyword "files");
      List.iter (fun file_name -> Buffer.add_string buf (" \"" ^ file_name ^ "\"")) !file_map

    let rec output_instr n buf indent label_map (I_aux (instr, (_, l))) =
      match instr with
      | I_decl (ctyp, id) | I_reset (ctyp, id) ->
          add_instr n buf indent (string_of_name id ^ " : " ^ C.typ ctyp ^ output_loc l)
      | I_init (ctyp, id, Init_cval cval) | I_reinit (ctyp, id, cval) ->
          add_instr n buf indent (string_of_name id ^ " : " ^ C.typ ctyp ^ " = " ^ C.value cval ^ output_loc l)
      | I_init (ctyp, id, (Init_static _ | Init_json_key _)) ->
          raise (Reporting.err_general l "Unsupported initializer in Isla IR")
      | I_clear (ctyp, id) -> add_instr n buf indent ("!" ^ string_of_name id)
      | I_label label -> C.output_label_instr buf label_map label
      | I_jump (cval, label) ->
          add_instr n buf indent
            (C.keyword "jump" ^ " " ^ C.value cval ^ " " ^ C.keyword "goto" ^ " "
            ^ C.string_of_label (StringMap.find label label_map)
            ^ output_loc l
            )
      | I_goto label ->
          add_instr n buf indent (C.keyword "goto" ^ " " ^ C.string_of_label (StringMap.find label label_map))
      | I_exit cause -> add_instr n buf indent (C.keyword "exit" ^ " " ^ cause ^ output_loc l)
      | I_undefined _ -> add_instr n buf indent (C.keyword "arbitrary")
      | I_end _ -> add_instr n buf indent (C.keyword "end")
      | I_copy (clexp, cval) -> add_instr n buf indent (string_of_clexp clexp ^ " = " ^ C.value cval ^ output_loc l)
      | I_funcall (creturn, Call, id, args) ->
          add_instr n buf indent
            (string_of_creturn creturn ^ " = " ^ string_of_uid id ^ "(" ^ Util.string_of_list ", " C.value args ^ ")"
           ^ output_loc l
            )
      | I_funcall (creturn, Extern _, id, args) ->
          add_instr n buf indent
            (string_of_creturn creturn ^ " = $" ^ string_of_uid id ^ "(" ^ Util.string_of_list ", " C.value args ^ ")"
           ^ output_loc l
            )
      | I_return cval -> add_instr n buf indent (C.keyword "return" ^ " " ^ C.value cval)
      | I_comment str -> Buffer.add_string buf (String.make indent ' ' ^ "/*" ^ str ^ "*/\n")
      | I_raw str -> Buffer.add_string buf str
      | I_throw cval -> add_instr n buf indent (C.keyword "throw" ^ " " ^ C.value cval)
      | I_if _ | I_block _ | I_try_block _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Can only format flat IR"

    and output_instrs n buf indent label_map = function
      | (I_aux (I_label _, _) as instr) :: instrs ->
          output_instr n buf indent label_map instr;
          output_instrs n buf indent label_map instrs
      | instr :: instrs ->
          output_instr n buf indent label_map instr;
          output_instrs (n + 1) buf indent label_map instrs
      | [] -> ()

    let id_ctyp (id, ctyp) = sprintf "%s: %s" (zencode_id id) (C.typ ctyp)

    let output_def_aux buf = function
      | CDEF_register (id, ctyp, []) ->
          Buffer.add_string buf (sprintf "%s %s : %s" (C.keyword "register") (string_of_name id) (C.typ ctyp))
      | CDEF_register (id, ctyp, instrs) ->
          let instrs = C.modify_instrs instrs in
          let label_map = C.make_label_map instrs in
          Buffer.add_string buf (sprintf "%s %s : %s {\n" (C.keyword "register") (string_of_name id) (C.typ ctyp));
          output_instrs 0 buf 2 label_map instrs;
          Buffer.add_string buf "}"
      | CDEF_val (id, _, ctyps, ctyp, None) ->
          Buffer.add_string buf
            (sprintf "%s %s : (%s) ->  %s" (C.keyword "val") (zencode_id id) (Util.string_of_list ", " C.typ ctyps)
               (C.typ ctyp)
            )
      | CDEF_val (id, _, ctyps, ctyp, Some extern) ->
          let keyword = C.keyword (if StringSet.mem extern !abstract_functions then "abstract" else "val") in
          Buffer.add_string buf
            (sprintf "%s %s = \"%s\" : (%s) ->  %s" keyword (zencode_id id) extern
               (Util.string_of_list ", " C.typ ctyps) (C.typ ctyp)
            )
      | CDEF_fundef (id, ret, args, instrs) ->
          let instrs = C.modify_instrs instrs in
          let label_map = C.make_label_map instrs in
          let ret = match ret with Return_plain -> "" | Return_via id -> " " ^ string_of_name id in
          Buffer.add_string buf
            (sprintf "%s %s%s(%s) {\n" (C.keyword "fn") (zencode_id id) ret
               (Util.string_of_list ", " string_of_name args)
            );
          output_instrs 0 buf 2 label_map instrs;
          Buffer.add_string buf "}"
      | CDEF_type (CTD_enum (id, ids)) ->
          Buffer.add_string buf
            (sprintf "%s %s {\n  %s\n}" (C.keyword "enum") (zencode_id id) (Util.string_of_list ",\n  " zencode_id ids))
      | CDEF_type (CTD_struct (id, _, ids)) ->
          Buffer.add_string buf
            (sprintf "%s %s {\n  %s\n}" (C.keyword "struct") (zencode_id id) (Util.string_of_list ",\n  " id_ctyp ids))
      | CDEF_type (CTD_variant (id, _, ids)) ->
          Buffer.add_string buf
            (sprintf "%s %s {\n  %s\n}" (C.keyword "union") (zencode_id id) (Util.string_of_list ",\n  " id_ctyp ids))
      | CDEF_type (CTD_abbrev _ | CTD_abstract _) -> ()
      | CDEF_let (_, bindings, instrs) ->
          let instrs = C.modify_instrs instrs in
          let label_map = C.make_label_map instrs in
          Buffer.add_string buf (sprintf "%s (%s) {\n" (C.keyword "let") (Util.string_of_list ", " id_ctyp bindings));
          output_instrs 0 buf 2 label_map instrs;
          Buffer.add_string buf "}"
      | CDEF_pragma ("abstract", str) -> abstract_functions := StringSet.add str !abstract_functions
      | CDEF_pragma (name, str) -> Buffer.add_string buf (sprintf "#%s %s" name str)
      | CDEF_startup _ | CDEF_finish _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Unexpected startup / finish"

    let output_def buf (CDEF_aux (aux, _)) = output_def_aux buf aux

    let rec output_defs' buf = function
      | def :: defs ->
          output_def buf def;
          Buffer.add_string buf "\n\n";
          output_defs' buf defs
      | [] -> ()

    let output_defs buf defs =
      unknown_loc_counter := 0;
      abstract_functions := StringSet.empty;
      output_defs' buf defs;
      output_files buf;
      Buffer.add_string buf "\n\n"
  end
end

let colored_ir = ref false

let with_colors f =
  let is_colored = !colored_ir in
  colored_ir := true;
  f ();
  colored_ir := is_colored

module Flat_ir_config : Ir_formatter.Config = struct
  type label = int

  let make_label_map instrs =
    let rec make_label_map' n = function
      | I_aux (I_label label, _) :: instrs -> StringMap.add label n (make_label_map' n instrs)
      | _ :: instrs -> make_label_map' (n + 1) instrs
      | [] -> StringMap.empty
    in
    make_label_map' 0 instrs

  let modify_instrs instrs =
    let open Jib_optimize in
    reset_flat_counter ();
    instrs |> flatten_instrs |> remove_clear |> remove_dead_code

  let string_of_label = string_of_int

  let output_label_instr buf _ label = ()

  let color f = if !colored_ir then f else fun str -> str

  let keyword str = str |> color Util.red |> color Util.clear

  let typ str = string_of_ctyp str |> color Util.yellow |> color Util.clear

  let value str = string_of_cval str |> color Util.cyan |> color Util.clear
end

module Flat_ir_formatter = Ir_formatter.Make (Flat_ir_config)
