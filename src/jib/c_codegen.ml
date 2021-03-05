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
open Ast_defs
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Type_check
open PPrint
open Printf
open Value2

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module Big_int = Nat_big_num
module Json = Yojson.Basic

let (gensym, _) = symbol_generator "c2"
let ngensym () = name (gensym ())

let zencode_id id = Util.zencode_string (string_of_id id)

let zencode_uid (id, ctyps) =
  match ctyps with
  | [] -> Util.zencode_string (string_of_id id)
  | _ -> Util.zencode_string (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

let ctor_bindings = List.fold_left (fun map (id, ctyp) -> UBindings.add id ctyp map) UBindings.empty

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(** This function is used to split types into those we allocate on the
   stack, versus those which need to live on the heap, or otherwise
   require some additional memory management *)
let rec is_stack_ctyp ctyp = match ctyp with
  | CT_fbits _ | CT_sbits _ | CT_bit | CT_unit | CT_bool | CT_enum _ -> true
  | CT_fint n -> n <= 64
  (* | CT_lint when !optimize_fixed_int -> true *)
  | CT_lint -> false
  (* | CT_lbits _ when !optimize_fixed_bits -> true *)
  | CT_lbits _ -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ | CT_fvector _ -> false
  | CT_struct (_, fields) -> List.for_all (fun (_, ctyp) -> is_stack_ctyp ctyp) fields
  | CT_variant (_, ctors) -> false (* List.for_all (fun (_, ctyp) -> is_stack_ctyp ctyp) ctors *) (* FIXME *)
  | CT_tup ctyps -> List.for_all is_stack_ctyp ctyps
  | CT_ref ctyp -> true
  | CT_poly -> true
  | CT_constant n -> Big_int.less_equal (min_int 64) n && Big_int.greater_equal n (max_int 64)

(** For now, the types that can be used in the state API are the types that fits on the stack.
    In the future, this can be expanded to support more complex types if needed. *)
let is_api_ctyp = is_stack_ctyp

let v_mask_lower i = V_lit (VL_bits (Util.list_init i (fun _ -> Sail2_values.B1), true), CT_fbits (i, true))

type codegen_options = {
    (** Rewrites a Sail identifier into a user-specified name in the generated C *)
    exports : string Bindings.t;
    (** Rewrites a generated symbol after name-mangling has ocurred *)
    exports_mangled : string StringMap.t;
    (** Extra headers to include in the generated .h file *)
    extra_headers : string list;
    (** Extra lines that are included in the sail_state struct. Used
       to add user-specified state to the structs, which can then be
       passed to primops in state_primops *)
    extra_state : string list;
    (** Primitives in this set will be passed a pointer to the
       sail_state struct *)
    state_primops : StringSet.t;
    (** Control which sail_state variables accessors will be implemented
       by the consumer of the library. This is a list of regular expressions,
       if one of those regular expression matches the name of a sail_state variable,
       only the declaration of the accessors will be generated. *)
    external_state_api : string list;
  }

let initial_options = {
    exports = Bindings.empty;
    exports_mangled = StringMap.empty;
    extra_headers = [];
    extra_state = [];
    state_primops = StringSet.empty;
    external_state_api = [];
  }

let add_export opts id = { opts with exports = Bindings.add id (string_of_id id) opts.exports }

let add_custom_export opts id into = { opts with exports = Bindings.add id into opts.exports }

let add_mangled_rename opts (from, into) =
  { opts with exports_mangled = StringMap.add from into opts.exports_mangled }

let add_external_state_api_regex opts regex =
  { opts with external_state_api = regex :: opts.external_state_api }

let add_export_uid opts (id, ctyps) =
  match ctyps with
  | [] -> { opts with exports = Bindings.add id (string_of_id id) opts.exports }
  | _ -> opts

let ctype_def_initial_options opts = function
  | CTD_enum (id, ids) ->
     List.fold_left add_export (add_export opts id) ids
  | CTD_struct (id, members) | CTD_variant (id, members) ->
     List.fold_left add_export_uid (add_export opts id) (List.map fst members)

let cdef_initial_options opts = function
  | CDEF_type ctype_def -> ctype_def_initial_options opts ctype_def
  | CDEF_reg_dec (id, _, _) -> add_export opts id
  | CDEF_let (_, bindings, _) -> List.fold_left (fun opts (id, _) -> add_export opts id) opts bindings
  | _ -> opts

let default_options cdefs =
  let opts = List.fold_left cdef_initial_options initial_options cdefs in
  let opts = add_export opts (mk_id "initialize_registers") in
  let opts = add_custom_export opts (mk_id "main") "sail_main" in
  List.fold_left add_mangled_rename opts (List.init 9 (fun n -> "ztup" ^ string_of_int n, "tuple_" ^ string_of_int n))

let options_from_json json cdefs =
  let open Json.Util in
  let bad_key k json =
    raise (Reporting.err_general Parse_ast.Unknown
             (sprintf "Invalid %s key in codegen json configuration: %s" k (Json.to_string json)))
  in
  let opts = match member "default_exports" json with
    | `Bool true -> default_options cdefs
    | `Bool false -> initial_options
    | `Null ->
       Reporting.simple_warn "No default_exports key in codegen json configuration";
       initial_options
    | json -> bad_key "default_exports" json
  in
  let process_exports opts = function
    | `List [`String from; `String into] -> add_custom_export opts (mk_id from) into
    | `String str -> add_export opts (mk_id str)
    | json -> bad_key "exports" json
  in
  let opts = match member "exports" json with
    | `List exports -> List.fold_left process_exports opts exports
    | `Null ->
       Reporting.simple_warn "No exports key in codegen json configuration";
       opts
    | json -> bad_key "exports" json
  in
  let process_exports_mangled opts = function
    | `List [`String from; `String into] -> add_mangled_rename opts (from, into)
    | json -> bad_key "exports_mangled" json
  in
  let opts = match member "exports_mangled" json with
    | `List exports -> List.fold_left process_exports_mangled opts exports
    | `Null ->
       Reporting.simple_warn "No exports_mangled key in codegen json configuration";
       opts
    | json -> bad_key "exports_mangled" json
  in
  let process_extra_header opts = function
    | `String header -> { opts with extra_headers = header :: opts.extra_headers }
    | json -> bad_key "extra_headers" json
  in
  let opts = match member "extra_headers" json with
    | `List headers -> List.fold_left process_extra_header opts headers
    | `Null ->
       Reporting.simple_warn "No extra_headers key in codegen json configuration";
       opts
    | json -> bad_key "extra_headers" json
  in
  let process_extra_state opts = function
    | `String member -> { opts with extra_state = member :: opts.extra_state }
    | json -> bad_key "extra_state" json
  in
  let opts = match member "extra_state" json with
    | `List members -> List.fold_left process_extra_state opts members
    | `Null ->
       Reporting.simple_warn "No extra_state key in codegen json configuration";
       opts
    | json -> bad_key "extra_state" json
  in
  let process_state_primops opts = function
    | `String member -> { opts with state_primops = StringSet.add member opts.state_primops }
    | json -> bad_key "state_primops" json
  in
  let opts = match member "state_primops" json with
    | `List members -> List.fold_left process_state_primops opts members
    | `Null ->
       Reporting.simple_warn "No state_primops key in codegen json configuration";
       opts
    | json -> bad_key "state_primops" json
  in
  let process_external_state_api opts = function
    | `String member -> add_external_state_api_regex opts member
    | json -> bad_key "external_state_api" json
  in
  let opts = match member "external_state_api" json with
    | `List members -> List.fold_left process_external_state_api opts members
    | `Null ->
       Reporting.simple_warn "No external_state_api key in codegen json configuration";
       opts
    | json -> bad_key "external_state_api" json
  in
  opts

module type Options = sig
  val opts : codegen_options
end

module Make(O: Options) = struct

let mangle str =
  let mangled = Util.zencode_string str in
  match StringMap.find_opt mangled O.opts.exports_mangled with
  | Some export -> export
  | None -> mangled

let sgen_id id =
  match Bindings.find_opt id O.opts.exports with
  | Some export -> export
  | None -> mangle (string_of_id id)

let sgen_name ctyp id =
  match id with
  | Name (id, _) ->
     sgen_id id
  | Global (id, _) ->
     if is_api_ctyp ctyp then
        sprintf "(state_get_%s(state))" (sgen_id id)
     else
        sprintf "(state->%s)" (sgen_id id)
  | Have_exception _ ->
     "(state->have_exception)"
  | Return _ ->
     assert false
  | Current_exception _ ->
     "(*(state->current_exception))"
  | Throw_location _ ->
     "(state->throw_location)"

let sgen_uid (id, ctyps) =
  match ctyps with
  | [] -> sgen_id id
  | _ ->
     mangle (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

let codegen_id id = string (sgen_id id)
let codegen_uid id = string (sgen_uid id)

let sgen_function_id id = sgen_id id
let sgen_function_uid uid = sgen_uid uid
let codegen_function_id id = string (sgen_function_id id)

let rec sgen_ctyp = function
  | CT_unit -> "unit"
  | CT_bit -> "fbits"
  | CT_bool -> "bool"
  | CT_fbits _ -> "uint64_t"
  | CT_sbits _ -> "sbits"
  | CT_fint _ -> "int64_t"
  | CT_constant _ -> "int64_t"
  | CT_lint -> "sail_int"
  | CT_lbits _ -> "lbits"
  | CT_tup _ as tup -> "struct " ^ mangle ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> "struct " ^ sgen_id id
  | CT_enum (id, _) -> "enum " ^ sgen_id id
  | CT_variant (id, _) -> "struct " ^ sgen_id id
  | CT_list _ as l -> mangle (string_of_ctyp l)
  | CT_vector _ as v -> mangle (string_of_ctyp v)
  | CT_fvector (_, ord, typ) -> sgen_ctyp (CT_vector (ord, typ))
  | CT_string -> "sail_string"
  | CT_real -> "real"
  | CT_ref ctyp -> sgen_ctyp ctyp ^ "*"
  | CT_poly -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

let rec sgen_ctyp_name = function
  | CT_unit -> "unit"
  | CT_bit -> "fbits"
  | CT_bool -> "bool"
  | CT_fbits _ -> "fbits"
  | CT_sbits _ -> "sbits"
  | CT_fint _ -> "mach_int"
  | CT_constant _ -> "mach_int"
  | CT_lint -> "sail_int"
  | CT_lbits _ -> "lbits"
  | CT_tup _ as tup -> mangle ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> sgen_id id
  | CT_enum (id, _) -> sgen_id id
  | CT_variant (id, _) -> sgen_id id
  | CT_list _ as l -> mangle (string_of_ctyp l)
  | CT_vector _ as v -> mangle (string_of_ctyp v)
  | CT_fvector (_, ord, typ) -> sgen_ctyp_name (CT_vector (ord, typ))
  | CT_string -> "sail_string"
  | CT_real -> "real"
  | CT_ref ctyp -> "ref_" ^ sgen_ctyp_name ctyp
  | CT_poly -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

let sgen_mask n =
  if n = 0 then
    "UINT64_C(0)"
  else if n <= 64 then
    let chars_F = String.make (n / 4) 'F' in
    let first = match (n mod 4) with
      | 0 -> ""
      | 1 -> "1"
      | 2 -> "3"
      | 3 -> "7"
      | _ -> assert false
    in
    "UINT64_C(0x" ^ first ^ chars_F ^ ")"
  else
    failwith "Tried to create a mask literal for a vector greater than 64 bits."

let rec sgen_value = function
  | VL_bits ([], _) -> "UINT64_C(0)"
  | VL_bits (bs, true) -> "UINT64_C(" ^ Sail2_values.show_bitlist bs ^ ")"
  | VL_bits (bs, false) -> "UINT64_C(" ^ Sail2_values.show_bitlist (List.rev bs) ^ ")"
  | VL_int i ->
     if Big_int.equal i (min_int 64) then
       "INT64_MIN"
     else
       "INT64_C(" ^ Big_int.to_string i ^ ")"
  | VL_bool true -> "true"
  | VL_bool false -> "false"
  | VL_unit -> "UNIT"
  | VL_bit Sail2_values.B0 -> "UINT64_C(0)"
  | VL_bit Sail2_values.B1 -> "UINT64_C(1)"
  | VL_bit Sail2_values.BU -> failwith "Undefined bit found in value"
  | VL_real str -> str
  | VL_string str -> "\"" ^ str ^ "\""
  | VL_empty_list -> "NULL"
  | VL_enum element -> mangle element
  | VL_ref r -> "&(state->" ^ sgen_id (mk_id r) ^ ")"
  | VL_undefined ->
     Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for an undefined literal"

let rec sgen_cval ctx = function
  | V_id (id, ctyp) ->
     sgen_name ctyp id
  | V_lit (vl, ctyp) -> sgen_value vl
  | V_call (op, cvals) -> sgen_call ctx op cvals
  | V_field (f, field) -> 
    begin match f with
    | V_id (Global (id, _), ctyp) when is_api_ctyp ctyp ->
       sprintf "state_get_%s_in_%s(state)" (sgen_uid field) (sgen_id id)
    | _ -> sprintf "%s.%s" (sgen_cval ctx f) (sgen_uid field)
    end
  | V_tuple_member (f, _, n) ->
     sprintf "%s.%s" (sgen_cval ctx f) (mangle ("tup" ^ string_of_int n))
  | V_ctor_kind (f, ctor, unifiers, _) ->
     sgen_cval ctx f ^ ".kind"
     ^ " != Kind_" ^ sgen_uid (ctor, unifiers)
  | V_struct (fields, _) ->
     sprintf "{%s}"
       (Util.string_of_list ", " (fun (field, cval) -> sgen_uid field ^ " = " ^ sgen_cval ctx cval) fields)
  | V_ctor_unwrap (ctor, f, unifiers, _) ->
     sprintf "%s.%s"
       (sgen_cval ctx f)
       (sgen_uid (ctor, unifiers))
  | V_poly (f, _) -> sgen_cval ctx f

and sgen_call ctx op cvals =
  match op, cvals with
  | Bnot, [v] -> "!(" ^ sgen_cval ctx v ^ ")"
  | List_hd, [v] ->
     sprintf "(%s).hd" ("*" ^ sgen_cval ctx v)
  | List_tl, [v] ->
     sprintf "(%s).tl" ("*" ^ sgen_cval ctx v)
  | Eq, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_sbits _ ->
        sprintf "eq_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ ->
        sprintf "(%s == %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     end
  | Neq, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_sbits _ ->
        sprintf "neq_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ ->
        sprintf "(%s != %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     end
  | Ilt, [v1; v2] ->
     sprintf "(%s < %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
  | Igt, [v1; v2] ->
     sprintf "(%s > %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
  | Ilteq, [v1; v2] ->
     sprintf "(%s <= %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
  | Igteq, [v1; v2] ->
     sprintf "(%s >= %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
  | Iadd, [v1; v2] ->
     sprintf "(%s + %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
  | Isub, [v1; v2] ->
     sprintf "(%s - %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
  | Unsigned 64, [vec] ->
     sprintf "((mach_int) %s)" (sgen_cval ctx vec)
  | Signed 64, [vec] ->
     begin match cval_ctyp vec with
     | CT_fbits (n, _) ->
        sprintf "fast_signed(%s, %d)" (sgen_cval ctx vec) n
     | _ -> assert false
     end
  | Bvand, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_fbits _ ->
        sprintf "(%s & %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | CT_sbits _ ->
        sprintf "and_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ -> assert false
     end
  | Bvnot, [v] ->
     begin match cval_ctyp v with
     | CT_fbits (n, _) ->
        sprintf "(~(%s) & %s)" (sgen_cval ctx v) (sgen_cval ctx (v_mask_lower n))
     | CT_sbits _ ->
        sprintf "not_sbits(%s)" (sgen_cval ctx v)
     | _ -> assert false
     end
  | Bvor, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_fbits _ ->
        sprintf "(%s | %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | CT_sbits _ ->
        sprintf "or_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ -> assert false
     end
  | Bvxor, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_fbits _ ->
        sprintf "(%s ^ %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | CT_sbits _ ->
        sprintf "xor_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ -> assert false
     end
  | Bvadd, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_fbits (n, _) ->
        sprintf "((%s + %s) & %s)" (sgen_cval ctx v1) (sgen_cval ctx v2) (sgen_cval ctx (v_mask_lower n))
     | CT_sbits _ ->
        sprintf "add_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ -> assert false
     end
  | Bvsub, [v1; v2] ->
     begin match cval_ctyp v1 with
     | CT_fbits (n, _) ->
        sprintf "((%s - %s) & %s)" (sgen_cval ctx v1) (sgen_cval ctx v2) (sgen_cval ctx (v_mask_lower n))
     | CT_sbits _ ->
        sprintf "sub_sbits(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ -> assert false
     end
  | Bvaccess, [vec; n] ->
     begin match cval_ctyp vec with
     | CT_fbits _ ->
        sprintf "(UINT64_C(1) & (%s >> %s))" (sgen_cval ctx vec) (sgen_cval ctx n)
     | CT_sbits _ ->
        sprintf "(UINT64_C(1) & (%s.bits >> %s))" (sgen_cval ctx vec) (sgen_cval ctx n)
     | _ -> assert false
     end
  | Slice len, [vec; start] ->
     begin match cval_ctyp vec with
     | CT_fbits _ ->
        sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & (%s >> %s))" len (sgen_cval ctx vec) (sgen_cval ctx start)
     | CT_sbits _ ->
        sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & (%s.bits >> %s))" len (sgen_cval ctx vec) (sgen_cval ctx start)
     | _ -> assert false
     end
  | Sslice 64, [vec; start; len] ->
     begin match cval_ctyp vec with
     | CT_fbits _ ->
        sprintf "sslice(%s, %s, %s)" (sgen_cval ctx vec) (sgen_cval ctx start) (sgen_cval ctx len)
     | CT_sbits _ ->
        sprintf "sslice(%s.bits, %s, %s)" (sgen_cval ctx vec) (sgen_cval ctx start) (sgen_cval ctx len)
     | _ -> assert false
     end
  | Set_slice, [vec; start; slice] ->
     begin match cval_ctyp vec, cval_ctyp slice with
     | CT_fbits (n, _), CT_fbits (m, _) ->
        sprintf "((%s & ~(%s << %s)) | (%s << %s))" (sgen_cval ctx vec) (sgen_mask m) (sgen_cval ctx start) (sgen_cval ctx slice) (sgen_cval ctx start)
     | _ -> assert false
     end
  | Zero_extend n, [v] ->
     begin match cval_ctyp v with
     | CT_fbits _ -> sgen_cval ctx v
     | CT_sbits _ ->
        sprintf "fast_zero_extend(%s, %d)" (sgen_cval ctx v) n
     | _ -> assert false
     end
  | Sign_extend n, [v] ->
     begin match cval_ctyp v with
     | CT_fbits (m, _) ->
        sprintf "fast_sign_extend(%s, %d, %d)" (sgen_cval ctx v) m n
     | CT_sbits _ ->
        sprintf "fast_sign_extend2(%s, %d)" (sgen_cval ctx v) n
     | _ -> assert false
     end
  | Replicate n, [v] ->
     begin match cval_ctyp v with
     | CT_fbits (m, _) ->
        sprintf "fast_replicate_bits(UINT64_C(%d), %s, %d)" m (sgen_cval ctx v) n
     | _ -> assert false
     end
  | Concat, [v1; v2] ->
     (* Optimized routines for all combinations of fixed and small bits
        appends, where the result is guaranteed to be smaller than 64. *)
     begin match cval_ctyp v1, cval_ctyp v2 with
     | CT_fbits (0, _), CT_fbits (n2, _) ->
        sgen_cval ctx v2
     | CT_fbits (n1, _), CT_fbits (n2, _) ->
        sprintf "(%s << %d) | %s" (sgen_cval ctx v1) n2 (sgen_cval ctx v2)
     | CT_sbits (64, ord1), CT_fbits (n2, _) ->
        sprintf "append_sf(%s, %s, %d)" (sgen_cval ctx v1) (sgen_cval ctx v2) n2
     | CT_fbits (n1, ord1), CT_sbits (64, ord2) ->
        sprintf "append_fs(%s, %d, %s)" (sgen_cval ctx v1) n1 (sgen_cval ctx v2)
     | CT_sbits (64, ord1), CT_sbits (64, ord2) ->
        sprintf "append_ss(%s, %s)" (sgen_cval ctx v1) (sgen_cval ctx v2)
     | _ -> assert false
     end
  | _, _ ->
     failwith "Could not generate cval primop"

let sgen_cval_param ctx cval =
  match cval_ctyp cval with
  | CT_lbits direction ->
     sgen_cval ctx cval ^ ", " ^ string_of_bool direction
  | CT_sbits (_, direction) ->
     sgen_cval ctx cval ^ ", " ^ string_of_bool direction
  | CT_fbits (len, direction) ->
     sgen_cval ctx cval ^ ", UINT64_C(" ^ string_of_int len ^ ") , " ^ string_of_bool direction
  | _ ->
     sgen_cval ctx cval

let rec sgen_clexp_state_api = function
  | CL_id (Global (id, _), _) -> sgen_id id
  | CL_field (clexp, field) -> sgen_uid field ^ "_in_" ^ sgen_clexp_state_api clexp 
  | _ -> assert false

let sgen_cval_state_api = function
  | V_id (Global (id, _), ctyp) -> sgen_id id
  | _ -> assert false

let rec is_state_api_cval = function
  | V_id (Global (id, _), ctyp) ->
    begin match ctyp with 
    | CT_vector (_, vctyp) -> is_api_ctyp vctyp
    | CT_fvector (_, _, vctyp) -> is_api_ctyp vctyp
    | _ when is_api_ctyp ctyp -> true
    | _ -> false
    end
  | V_field (clexp, field) -> is_state_api_cval clexp
  | _ -> false

let rec is_state_api_clexp = function
  | CL_id (Global (id, _), ctyp) ->
    begin match ctyp with 
    | CT_vector (_, vctyp) -> is_api_ctyp vctyp
    | CT_fvector (_, _, vctyp) -> is_api_ctyp vctyp
    | _ when is_api_ctyp ctyp -> true
    | _ -> false
    end
  | CL_field (clexp, field) -> is_state_api_clexp clexp
  | _ -> false

let rec sgen_clexp ctx clexp =
  match clexp with
  | CL_id (Have_exception _, _) -> "(state->have_exception)"
  | CL_id (Current_exception _, _) -> "(state->current_exception)"
  | CL_id (Throw_location _, _) -> "(state->throw_location)"
  | CL_id (Return _, _) -> assert false
  | CL_id (Global (id, _), _) -> 
    let ctyp = clexp_ctyp clexp in
    if is_api_ctyp ctyp then
      "(state_get_" ^ sgen_id id ^ "(state))"
    else
      "&(state->" ^ sgen_id id ^ ")"
  | CL_id (Name (id, _), _) -> "&" ^ sgen_id id
  | CL_field (clexp, field) ->
     begin match clexp with
     | CL_id (Global (id, _), ctyp) when is_api_ctyp ctyp -> "(state_get_ " ^ sgen_uid field ^ "_in_" ^ sgen_clexp_state_api clexp ^ "(state))"
     | _ -> "&((" ^ sgen_clexp ctx clexp ^ ")->" ^ sgen_uid field ^ ")"
     end
  | CL_tuple (clexp, n) -> "&((" ^ sgen_clexp ctx clexp ^ ")->" ^ mangle ("tup" ^ string_of_int n) ^ ")"
  | CL_addr clexp -> "(*(" ^ sgen_clexp ctx clexp ^ "))"
  | CL_void -> assert false
  | CL_rmw _ -> assert false

let rec sgen_clexp_pure ctx clexp =
  match clexp with
  | CL_id (Have_exception _, _) -> "(state->have_exception)"
  | CL_id (Current_exception _, _) -> "(state->current_exception)"
  | CL_id (Throw_location _, _) -> "(state->throw_location)"
  | CL_id (Return _, _) -> assert false
  | CL_id (Global (id, _), _) ->
    let ctyp = clexp_ctyp clexp in
    assert (not (is_api_ctyp ctyp));
      "state->" ^ sgen_id id
  | CL_id (Name (id, _), _) -> sgen_id id
  | CL_field (clexp, field) -> sgen_clexp_pure ctx clexp ^ "." ^ sgen_uid field
  | CL_tuple (clexp, n) -> sgen_clexp_pure ctx clexp ^ "." ^ mangle ("tup" ^ string_of_int n)
  | CL_addr clexp -> "(*(" ^ sgen_clexp_pure ctx clexp ^ "))"
  | CL_void -> assert false
  | CL_rmw _ -> assert false

(** Generate instructions to copy from a cval to a clexp. This will
   insert any needed type conversions from big integers to small
   integers (or vice versa), or from arbitrary-length bitvectors to
   and from uint64 bitvectors as needed. *)
let rec codegen_conversion l ctx clexp cval =
  let ctyp_to = clexp_ctyp clexp in
  let ctyp_from = cval_ctyp cval in
  match ctyp_to, ctyp_from with
  (* When both types are equal, we don't need any conversion. *)
  | _, _ when ctyp_equal ctyp_to ctyp_from ->
     if is_stack_ctyp ctyp_to then
       if is_state_api_clexp clexp then
         ksprintf string "  state_set_%s(state, %s);" (sgen_clexp_state_api clexp) (sgen_cval ctx cval)
       else
         ksprintf string "  %s = %s;" (sgen_clexp_pure ctx clexp) (sgen_cval ctx cval)
     else
       ksprintf string "  COPY(%s)(%s, %s);" (sgen_ctyp_name ctyp_to) (sgen_clexp ctx clexp) (sgen_cval ctx cval)

  | CT_ref ctyp_to, ctyp_from ->
     codegen_conversion l ctx (CL_addr clexp) cval

  (* If we have to convert between tuple types, convert the fields individually. *)
  | CT_tup ctyps_to, CT_tup ctyps_from when List.length ctyps_to = List.length ctyps_from ->
     let len = List.length ctyps_to in
     let conversions =
       List.mapi (fun i ctyp -> codegen_conversion l ctx (CL_tuple (clexp, i)) (V_tuple_member (cval, len, i))) ctyps_from
     in
     string "  /* conversions */"
     ^^ hardline
     ^^ separate hardline conversions
     ^^ hardline
     ^^ string "  /* end conversions */"

  (* For anything not special cased, just try to call a appropriate CONVERT_OF function. *)
  | _, _ when is_stack_ctyp (clexp_ctyp clexp) ->
    if is_state_api_clexp clexp then
     ksprintf string "  state_set_%s(state, CONVERT_OF(%s, %s)(%s));"
       (sgen_clexp_state_api clexp) (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) (sgen_cval_param ctx cval)
    else
     ksprintf string "  %s = CONVERT_OF(%s, %s)(%s);"
       (sgen_clexp_pure ctx clexp) (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) (sgen_cval_param ctx cval)
  | _, _ ->
     ksprintf string "  CONVERT_OF(%s, %s)(%s, %s);"
       (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) (sgen_clexp ctx clexp) (sgen_cval_param ctx cval)

let extra_params () = "sail_state *state, "

let extra_arguments is_extern =
  if is_extern then
    ""
  else
    "state, "

let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
  match instr with
  | I_decl (ctyp, id) when is_stack_ctyp ctyp ->
     ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name ctyp id)
  | I_decl (ctyp, id) ->
     ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name ctyp id) ^^ hardline
     ^^ ksprintf string "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name ctyp id)

  | I_copy (clexp, cval) -> codegen_conversion l ctx clexp cval

  | I_jump (cval, label) ->
     ksprintf string "  if (%s) goto %s;" (sgen_cval ctx cval) label

  | I_if (cval, [then_instr], [], ctyp) ->
     ksprintf string "  if (%s)" (sgen_cval ctx cval) ^^ hardline
     ^^ twice space ^^ codegen_instr fid ctx then_instr
  | I_if (cval, then_instrs, [], ctyp) ->
     string "  if" ^^ space ^^ parens (string (sgen_cval ctx cval)) ^^ space
     ^^ surround 0 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
  | I_if (cval, then_instrs, else_instrs, ctyp) ->
     string "  if" ^^ space ^^ parens (string (sgen_cval ctx cval)) ^^ space
     ^^ surround 0 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
     ^^ space ^^ string "else" ^^ space
     ^^ surround 0 0 lbrace (separate_map hardline (codegen_instr fid ctx) else_instrs) (twice space ^^ rbrace)

  | I_block instrs ->
     string "  {"
     ^^ jump 2 2 (separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline
     ^^ string "  }"

  | I_try_block instrs ->
     string "  { /* try */"
     ^^ jump 2 2 (separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline
     ^^ string "  }"

  | I_funcall (x, special_extern, f, args) ->
     let c_args = Util.string_of_list ", " (sgen_cval ctx) args in
     let ctyp = clexp_ctyp x in
     let fname, is_extern =
       if special_extern then
         (string_of_id (fst f), true)
       else if Env.is_extern (fst f) ctx.tc_env "c" then
         (Env.get_extern (fst f) ctx.tc_env "c", true)
       else
         (sgen_function_uid f, false)
     in
     let sail_state_arg : string ref = ref 
       (if is_extern && StringSet.mem fname O.opts.state_primops then
         "state, "
       else
         "")
     in
     let fname =
       match fname, ctyp with
       | "internal_pick", _ -> sprintf "pick_%s" (sgen_ctyp_name ctyp)
       | "cons", _ ->
          begin match snd f with
          | [ctyp] -> Util.zencode_string ("cons#" ^ string_of_ctyp ctyp)
          | _ -> Reporting.unreachable l __POS__ "cons without specified type"
          end
       | "eq_anything", _ ->
          begin match args with
          | cval :: _ -> sprintf "eq_%s" (sgen_ctyp_name (cval_ctyp cval))
          | _ -> Reporting.unreachable l __POS__ "eq_anything function with bad arity."
          end
       | "length", _ ->
          begin match args with
          | cval :: _ -> sprintf "length_%s" (sgen_ctyp_name (cval_ctyp cval))
          | _ -> Reporting.unreachable l __POS__ "length function with bad arity."
          end
       | "vector_access", CT_bit -> "bitvector_access"
       | "vector_access", _ ->
          begin match args with
          | cval :: _  when is_state_api_cval cval -> sail_state_arg := "state, "; sprintf "state_vector_access_%s" (sgen_cval_state_api cval) 
          | cval :: _ -> sprintf "vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
          | _ -> Reporting.unreachable l __POS__ "vector access function with bad arity."
          end
       | "vector_update_subrange", _ -> sprintf "vector_update_subrange_%s" (sgen_ctyp_name ctyp)
       | "vector_subrange", _ -> sprintf "vector_subrange_%s" (sgen_ctyp_name ctyp)
       | "vector_update", CT_fbits _ -> "update_fbits"
       | "vector_update", CT_lbits _ -> "update_lbits"
       | "vector_update", _ -> if is_state_api_clexp x then (
                                 sail_state_arg := "state, ";
                                 sprintf "state_vector_update_%s" (sgen_clexp_state_api x))
                               else
                                 sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
       | "string_of_bits", _ ->
          begin match cval_ctyp (List.nth args 0) with
          | CT_fbits _ -> "string_of_fbits"
          | CT_lbits _ -> "string_of_lbits"
          | _ -> assert false
          end
       | "decimal_string_of_bits", _ ->
          begin match cval_ctyp (List.nth args 0) with
          | CT_fbits _ -> "decimal_string_of_fbits"
          | CT_lbits _ -> "decimal_string_of_lbits"
          | _ -> assert false
          end
       | "internal_vector_update", _ -> sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
       | "internal_vector_init", _ -> sprintf "internal_vector_init_%s" (sgen_ctyp_name ctyp)
       | "undefined_bitvector", CT_fbits _ -> "UNDEFINED(fbits)"
       | "undefined_bitvector", CT_lbits _ -> "UNDEFINED(lbits)"
       | "undefined_bit", _ -> "UNDEFINED(fbits)"
       | "undefined_vector", _ -> sprintf "UNDEFINED(vector_%s)" (sgen_ctyp_name ctyp)
       | "undefined_list", _ -> sprintf "UNDEFINED(%s)" (sgen_ctyp_name ctyp)
       | fname, _ -> fname
     in
     if fname = "reg_deref" then
       if is_stack_ctyp ctyp then
         ksprintf string "  %s = *(%s);" (sgen_clexp_pure ctx x) c_args
       else
         ksprintf string "  COPY(%s)(&%s, *(%s));" (sgen_ctyp_name ctyp) (sgen_clexp_pure ctx x) c_args
     else
       if is_stack_ctyp ctyp then
          if is_state_api_clexp x then
            ksprintf string "  state_set_%s(state, %s(%s%s%s));" (sgen_clexp_state_api x) fname !sail_state_arg (extra_arguments is_extern) c_args
          else
            ksprintf string "  %s = %s(%s%s%s);" (sgen_clexp_pure ctx x) fname !sail_state_arg (extra_arguments is_extern) c_args
       else
         ksprintf string "  %s(%s%s%s, %s);" fname !sail_state_arg (extra_arguments is_extern) (sgen_clexp ctx x) c_args

  | I_clear (ctyp, id) when is_stack_ctyp ctyp ->
     empty
  | I_clear (ctyp, id) ->
     ksprintf string "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name ctyp id)

  | I_init (ctyp, id, cval) ->
     codegen_instr fid ctx (idecl l ctyp id) ^^ hardline
     ^^ codegen_conversion Parse_ast.Unknown ctx (CL_id (id, ctyp)) cval

  | I_reinit (ctyp, id, cval) ->
     codegen_instr fid ctx (ireset ctyp id) ^^ hardline
     ^^ codegen_conversion Parse_ast.Unknown ctx (CL_id (id, ctyp)) cval

  | I_reset (ctyp, id) when is_stack_ctyp ctyp ->
     ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name ctyp id)
  | I_reset (ctyp, id) ->
     ksprintf string "  RECREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name ctyp id)

  | I_return cval ->
     ksprintf string "  return %s;" (sgen_cval ctx cval)

  | I_throw cval ->
     Reporting.unreachable l __POS__ "I_throw reached code generator"

  | I_undefined ctyp ->
     let rec codegen_exn_return ctyp =
       match ctyp with
       | CT_unit -> "UNIT", []
       | CT_bit -> "UINT64_C(0)", []
       | CT_fint _ -> "INT64_C(0xdeadc0de)", []
       (* | CT_lint when !optimize_fixed_int -> "((sail_int) 0xdeadc0de)", [] *)
       | CT_fbits _ -> "UINT64_C(0xdeadc0de)", []
       | CT_sbits _ -> "undefined_sbits()", []
       (* | CT_lbits _ when !optimize_fixed_bits -> "undefined_lbits(false)", [] *)
       | CT_bool -> "false", []
       | CT_enum (_, ctor :: _) -> sgen_id ctor, []
       | CT_tup ctyps when is_stack_ctyp ctyp ->
          let gs = ngensym () in
          let fold (inits, prev) (n, ctyp) =
            let init, prev' = codegen_exn_return ctyp in
            sprintf ".%s = %s" (mangle ("tup" ^ string_of_int n)) init :: inits, prev @ prev'
          in
          let inits, prev = List.fold_left fold ([], []) (List.mapi (fun i x -> (i, x)) ctyps) in
          sgen_name ctyp gs,
          [sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name ctyp gs)
           ^ Util.string_of_list ", " (fun x -> x) inits ^ " };"] @ prev
       | CT_struct (id, ctors) when is_stack_ctyp ctyp ->
          let gs = ngensym () in
          let fold (inits, prev) (uid, ctyp) =
            let init, prev' = codegen_exn_return ctyp in
            sprintf ".%s = %s" (sgen_uid uid) init :: inits, prev @ prev'
          in
          let inits, prev = List.fold_left fold ([], []) ctors in
          sgen_name ctyp gs,
          [sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name ctyp gs)
           ^ Util.string_of_list ", " (fun x -> x) inits ^ " };"] @ prev
       | ctyp -> Reporting.unreachable l __POS__ ("Cannot create undefined value for type: " ^ string_of_ctyp ctyp)
     in
     let ret, prev = codegen_exn_return ctyp in
     separate_map hardline (fun str -> string ("  " ^ str)) (List.rev prev)
     ^^ hardline
     ^^ ksprintf string "  return %s;" ret

  | I_comment str ->
     string ("  /* " ^ str ^ " */")

  | I_label str ->
     string (str ^ ": ;")

  | I_goto str ->
     ksprintf string "  goto %s;" str

  | I_raw _ when ctx.no_raw -> empty
  | I_raw str ->
     string ("  " ^ str)

  | I_end _ -> assert false

  | I_match_failure ->
     string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")

(**************************************************************************)
(* Code generation for type definitions (enums, structs, and variants)    *)
(**************************************************************************)

let codegen_type_def_header = function
  | CTD_enum (id, ids) ->
     ksprintf string "// enum %s" (string_of_id id) ^^ hardline
     ^^ separate space [string "enum"; codegen_id id; lbrace; separate_map (comma ^^ space) codegen_id ids; rbrace ^^ semi]
     ^^ twice hardline

  | CTD_struct (id, ctors) ->
     let codegen_ctor (id, ctyp) =
       string (sgen_ctyp ctyp) ^^ space ^^ codegen_uid id
     in
     ksprintf string "// struct %s" (string_of_id id) ^^ hardline
     ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
     ^^ surround 2 0 lbrace
          (separate_map (semi ^^ hardline) codegen_ctor ctors ^^ semi)
          rbrace
     ^^ semi ^^ twice hardline

  | CTD_variant (id, tus) ->
     let codegen_tu (ctor_id, ctyp) =
       separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_uid ctor_id ^^ semi; rbrace]
     in
     ksprintf string "// union %s" (string_of_id id) ^^ hardline
     ^^ string "enum" ^^ space
     ^^ string ("kind_" ^ sgen_id id) ^^ space
     ^^ separate space [ lbrace;
                         separate_map (comma ^^ space) (fun id -> string ("Kind_" ^ sgen_uid id)) (List.map fst tus);
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

let codegen_type_def_body ctx = function
  | CTD_enum (id, ((first_id :: _) as ids)) ->
     let codegen_eq =
       let name = sgen_id id in
       string (Printf.sprintf "bool eq_%s(enum %s op1, enum %s op2) { return op1 == op2; }" name name name)
     in
     let codegen_undefined =
       let name = sgen_id id in
       string (Printf.sprintf "enum %s UNDEFINED(%s)(unit u) { return %s; }" name name (sgen_id first_id))
     in
     codegen_eq
     ^^ twice hardline
     ^^ codegen_undefined

  | CTD_enum (id, []) -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Cannot compile empty enum " ^ string_of_id id)

  | CTD_struct (id, ctors) ->
     let struct_ctyp = CT_struct (id, ctors) in
     (* Generate a set_T function for every struct T *)
     let codegen_set (id, ctyp) =
       if is_stack_ctyp ctyp then
         string (Printf.sprintf "rop->%s = op.%s;" (sgen_uid id) (sgen_uid id))
       else
         string (Printf.sprintf "COPY(%s)(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_uid id) (sgen_uid id))
     in
     let codegen_setter id ctors =
       string (let n = sgen_id id in Printf.sprintf "static void COPY(%s)(struct %s *rop, const struct %s op)" n n n) ^^ space
       ^^ surround 2 0 lbrace
                   (separate_map hardline codegen_set (UBindings.bindings ctors))
                   rbrace
     in
     (* Generate an init/clear_T function for every struct T *)
     let codegen_field_init f (id, ctyp) =
       if not (is_stack_ctyp ctyp) then
         [string (Printf.sprintf "%s(%s)(&op->%s);" f (sgen_ctyp_name ctyp) (sgen_uid id))]
       else []
     in
     let codegen_init f id ctors =
       string (let n = sgen_id id in Printf.sprintf "static void %s(%s)(struct %s *op)" f n n) ^^ space
       ^^ surround 2 0 lbrace
                   (separate hardline (UBindings.bindings ctors |> List.map (codegen_field_init f) |> List.concat))
                   rbrace
     in
     let codegen_eq =
       let codegen_eq_test (id, ctyp) =
         string (Printf.sprintf "EQUAL(%s)(op1.%s, op2.%s)" (sgen_ctyp_name ctyp) (sgen_uid id) (sgen_uid id))
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
       string (sgen_ctyp ctyp) ^^ space ^^ codegen_uid id
     in
     codegen_setter id (ctor_bindings ctors)
     ^^ (if not (is_stack_ctyp struct_ctyp) then
           twice hardline
           ^^ codegen_init "CREATE" id (ctor_bindings ctors)
           ^^ twice hardline
           ^^ codegen_init "RECREATE" id (ctor_bindings ctors)
           ^^ twice hardline
           ^^ codegen_init "KILL" id (ctor_bindings ctors)
         else empty)
     ^^ twice hardline
     ^^ codegen_eq

  | CTD_variant (id, tus) ->
     let codegen_tu (ctor_id, ctyp) =
       separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_uid ctor_id ^^ semi; rbrace]
     in
     (* Create an if, else if, ... block that does something for each constructor *)
     let rec each_ctor v f = function
       | [] -> string "{}"
       | [(ctor_id, ctyp)] ->
          string (Printf.sprintf "if (%skind == Kind_%s)" v (sgen_uid ctor_id)) ^^ lbrace ^^ hardline
          ^^ jump 0 2 (f ctor_id ctyp)
          ^^ hardline ^^ rbrace
       | (ctor_id, ctyp) :: ctors ->
          string (Printf.sprintf "if (%skind == Kind_%s) " v (sgen_uid ctor_id)) ^^ lbrace ^^ hardline
          ^^ jump 0 2 (f ctor_id ctyp)
          ^^ hardline ^^ rbrace ^^ string " else " ^^ each_ctor v f ctors
     in
     let codegen_init =
       let n = sgen_id id in
       let ctor_id, ctyp = List.hd tus in
       string (Printf.sprintf "static void CREATE(%s)(struct %s *op)" n n)
       ^^ hardline
       ^^ surround 2 0 lbrace
                   (string (Printf.sprintf "op->kind = Kind_%s;" (sgen_uid ctor_id)) ^^ hardline
                    ^^ if not (is_stack_ctyp ctyp) then
                         string (Printf.sprintf "CREATE(%s)(&op->%s);" (sgen_ctyp_name ctyp) (sgen_uid ctor_id))
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
         string (Printf.sprintf "KILL(%s)(&%s->%s);" (sgen_ctyp_name ctyp) v (sgen_uid ctor_id))
     in
     let codegen_clear =
       let n = sgen_id id in
       string (Printf.sprintf "static void KILL(%s)(struct %s *op)" n n) ^^ hardline
       ^^ surround 2 0 lbrace
                   (each_ctor "op->" (clear_field "op") tus ^^ semi)
                   rbrace
     in
     let codegen_ctor (ctor_id, ctyp) =
       let ctor_args = Printf.sprintf "%s op" (sgen_ctyp ctyp) in
       string (Printf.sprintf "static void %s(%sstruct %s *rop, %s)" (sgen_function_uid ctor_id) (extra_params ()) (sgen_id id) ctor_args) ^^ hardline
       ^^ surround 2 0 lbrace
                   (each_ctor "rop->" (clear_field "rop") tus ^^ hardline
                    ^^ string ("rop->kind = Kind_" ^ sgen_uid ctor_id) ^^ semi ^^ hardline
                    ^^ if is_stack_ctyp ctyp then
                         string (Printf.sprintf "rop->%s = op;" (sgen_uid ctor_id))
                       else
                         string (Printf.sprintf "CREATE(%s)(&rop->%s);" (sgen_ctyp_name ctyp) (sgen_uid ctor_id)) ^^ hardline
                         ^^ string (Printf.sprintf "COPY(%s)(&rop->%s, op);" (sgen_ctyp_name ctyp) (sgen_uid ctor_id)))
                   rbrace
     in
     let codegen_setter =
       let n = sgen_id id in
       let set_field ctor_id ctyp =
         if is_stack_ctyp ctyp then
           string (Printf.sprintf "rop->%s = op.%s;" (sgen_uid ctor_id) (sgen_uid ctor_id))
         else
           string (Printf.sprintf "CREATE(%s)(&rop->%s);" (sgen_ctyp_name ctyp) (sgen_uid ctor_id))
           ^^ string (Printf.sprintf " COPY(%s)(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_uid ctor_id) (sgen_uid ctor_id))
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
         string (Printf.sprintf "return EQUAL(%s)(op1.%s, op2.%s);" (sgen_ctyp_name ctyp) (sgen_uid ctor_id) (sgen_uid ctor_id))
       in
       let rec codegen_eq_tests = function
         | [] -> string "return false;"
         | (ctor_id, ctyp) :: ctors ->
            string (Printf.sprintf "if (op1.kind == Kind_%s && op2.kind == Kind_%s) " (sgen_uid ctor_id) (sgen_uid ctor_id)) ^^ lbrace ^^ hardline
            ^^ jump 0 2 (codegen_eq_test ctor_id ctyp)
            ^^ hardline ^^ rbrace ^^ string " else " ^^ codegen_eq_tests ctors
       in
       let n = sgen_id id in
       string (Printf.sprintf "static bool EQUAL(%s)(struct %s op1, struct %s op2) " n n n)
       ^^ surround 2 0 lbrace (codegen_eq_tests tus) rbrace
     in
     codegen_init
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

let codegen_type_def ctx ctype_def =
  codegen_type_def_header ctype_def, codegen_type_def_body ctx ctype_def

(**************************************************************************)
(* Code generation for generated types (lists, tuples, etc)               *)
(**************************************************************************)

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
    empty, empty
  else
    begin
      let _, fields = List.fold_left (fun (n, fields) ctyp -> n + 1, UBindings.add (mk_id ("tup" ^ string_of_int n), []) ctyp fields)
                                     (0, UBindings.empty)
                                     ctyps
      in
      generated := IdSet.add id !generated;
      codegen_type_def ctx (CTD_struct (id, UBindings.bindings fields))
    end

let codegen_list_header id =
  ksprintf string "// generated list type %s" (string_of_id id) ^^ hardline
  ^^ ksprintf string "struct node_%s;" (sgen_id id) ^^ hardline
  ^^ ksprintf string "typedef struct node_%s *%s;" (sgen_id id) (sgen_id id)
  ^^ twice hardline

let codegen_node id ctyp =
  ksprintf string "struct node_%s {\n  %s hd;\n  struct node_%s *tl;\n};\n" (sgen_id id) (sgen_ctyp ctyp) (sgen_id id)
  ^^ ksprintf string "typedef struct node_%s *%s;" (sgen_id id) (sgen_id id)

let codegen_list_init id =
  ksprintf string "static void CREATE(%s)(%s *rop) { *rop = NULL; }" (sgen_id id) (sgen_id id)

let codegen_list_clear id ctyp =
  ksprintf string "static void KILL(%s)(%s *rop) {\n" (sgen_id id) (sgen_id id)
  ^^ ksprintf string "  if (*rop == NULL) return;"
  ^^ (if is_stack_ctyp ctyp then empty
      else ksprintf string "  KILL(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp))
  ^^ ksprintf string "  KILL(%s)(&(*rop)->tl);\n" (sgen_id id)
  ^^ string "  sail_free(*rop);"
  ^^ string "}"

let codegen_list_recreate id =
  ksprintf string "static void RECREATE(%s)(%s *rop) { KILL(%s)(rop); *rop = NULL; }" (sgen_id id) (sgen_id id) (sgen_id id)

let codegen_list_set id ctyp =
  ksprintf string "static void internal_set_%s(%s *rop, const %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id)
  ^^ string "  if (op == NULL) { *rop = NULL; return; };\n"
  ^^ ksprintf string "  *rop = sail_malloc(sizeof(struct node_%s));\n" (sgen_id id)
  ^^ (if is_stack_ctyp ctyp then
        string "  (*rop)->hd = op->hd;\n"
      else
        ksprintf string "  CREATE(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp)
        ^^ ksprintf string "  COPY(%s)(&(*rop)->hd, op->hd);\n" (sgen_ctyp_name ctyp))
  ^^ ksprintf string "  internal_set_%s(&(*rop)->tl, op->tl);\n" (sgen_id id)
  ^^ string "}"
  ^^ twice hardline
  ^^ ksprintf string "static void COPY(%s)(%s *rop, const %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id)
  ^^ ksprintf string "  KILL(%s)(rop);\n" (sgen_id id)
  ^^ ksprintf string "  internal_set_%s(rop, op);\n" (sgen_id id)
  ^^ string "}"

let codegen_cons id ctyp =
  let cons_id = mk_id ("cons#" ^ string_of_ctyp ctyp) in
  ksprintf string "static void %s(%s *rop, const %s x, const %s xs) {\n" (sgen_function_id cons_id) (sgen_id id) (sgen_ctyp ctyp) (sgen_id id)
  ^^ ksprintf string "  *rop = sail_malloc(sizeof(struct node_%s));\n" (sgen_id id)
  ^^ (if is_stack_ctyp ctyp then
        string "  (*rop)->hd = x;\n"
      else
        ksprintf string "  CREATE(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp)
        ^^ ksprintf string "  COPY(%s)(&(*rop)->hd, x);\n" (sgen_ctyp_name ctyp))
  ^^ string "  (*rop)->tl = xs;\n"
  ^^ string "}"

let codegen_pick id ctyp =
  if is_stack_ctyp ctyp then
    ksprintf string "static %s pick_%s(const %s xs) { return xs->hd; }" (sgen_ctyp ctyp) (sgen_ctyp_name ctyp) (sgen_id id)
  else
    ksprintf string "static void pick_%s(%s *x, const %s xs) { COPY(%s)(x, xs->hd); }" (sgen_ctyp_name ctyp) (sgen_ctyp ctyp) (sgen_id id) (sgen_ctyp_name ctyp)

let codegen_list_equal id ctyp =
  ksprintf string "static bool EQUAL(%s)(const %s op1, const %s op2) {\n" (sgen_id id) (sgen_id id) (sgen_id id)
  ^^ ksprintf string "  if (op1 == NULL && op2 == NULL) { return true; };\n"
  ^^ ksprintf string "  if (op1 == NULL || op2 == NULL) { return false; };\n"
  ^^ ksprintf string "  return EQUAL(%s)(op1->hd, op2->hd) && EQUAL(%s)(op1->tl, op2->tl);\n" (sgen_ctyp_name ctyp) (sgen_id id)
  ^^ string "}"

let codegen_list_undefined id ctyp =
  ksprintf string "static void UNDEFINED(%s)(%s *rop, %s u) {\n" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
  ^^ ksprintf string "  *rop = NULL;\n"
  ^^ string "}"

let codegen_list ctx ctyp =
  let id = mk_id (string_of_ctyp (CT_list ctyp)) in
  if IdSet.mem id !generated then (
    (empty, empty)
  ) else (
    generated := IdSet.add id !generated;
    let header = codegen_list_header id in
    let body =
      codegen_node id ctyp ^^ twice hardline
      ^^ codegen_list_init id ^^ twice hardline
      ^^ codegen_list_clear id ctyp ^^ twice hardline
      ^^ codegen_list_recreate id ^^ twice hardline
      ^^ codegen_list_set id ctyp ^^ twice hardline
      ^^ codegen_cons id ctyp ^^ twice hardline
      ^^ codegen_pick id ctyp ^^ twice hardline
      ^^ codegen_list_equal id ctyp ^^ twice hardline
      ^^ codegen_list_undefined id ctyp
    in
    (header, body)
  )

(* Generate functions for working with non-bit vectors of some specific type. *)
let codegen_vector_header ctx id (direction, ctyp) =
  let vector_typedef =
    string (Printf.sprintf "struct %s {\n  size_t len;\n  %s *data;\n};\n" (sgen_id id) (sgen_ctyp ctyp))
    ^^ string (Printf.sprintf "typedef struct %s %s;" (sgen_id id) (sgen_id id))
  in
  vector_typedef ^^ hardline ^^
  string (Printf.sprintf "void vector_update_%s(%s *rop, %s op, sail_int n, %s elem);" (sgen_id id) (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)) ^^ hardline ^^
  if is_stack_ctyp ctyp then
    string (Printf.sprintf "%s vector_access_%s(%s op, sail_int n);" (sgen_ctyp ctyp) (sgen_id id) (sgen_id id))
  else
    string "" (* Not needed in the header file at the moment *)
  ^^ twice hardline

let codegen_vector_body ctx id (direction, ctyp) =
  let vector_init =
    string (Printf.sprintf "static void CREATE(%s)(%s *rop) {\n  rop->len = 0;\n  rop->data = NULL;\n}" (sgen_id id) (sgen_id id))
  in
  let vector_set =
    string (Printf.sprintf "static void COPY(%s)(%s *rop, %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id))
    ^^ string (Printf.sprintf "  KILL(%s)(rop);\n" (sgen_id id))
    ^^ string "  rop->len = op.len;\n"
    ^^ string (Printf.sprintf "  rop->data = sail_malloc((rop->len) * sizeof(%s));\n" (sgen_ctyp ctyp))
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
    ^^ string "  if (rop->data != NULL) sail_free(rop->data);\n"
    ^^ string "}"
  in
  let vector_update =
    string (Printf.sprintf "void vector_update_%s(%s *rop, %s op, sail_int n, %s elem) {\n" (sgen_id id) (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
    ^^ string "  int m = sail_int_get_ui(n);\n"
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
      string (Printf.sprintf "%s vector_access_%s(%s op, sail_int n) {\n" (sgen_ctyp ctyp) (sgen_id id) (sgen_id id))
      ^^ string "  int m = sail_int_get_ui(n);\n"
      ^^ string "  return op.data[m];\n"
      ^^ string "}"
    else
      string (Printf.sprintf "static void vector_access_%s(%s *rop, %s op, sail_int n) {\n" (sgen_id id) (sgen_ctyp ctyp) (sgen_id id))
      ^^ string "  int m = sail_int_get_ui(n);\n"
      ^^ string (Printf.sprintf "  COPY(%s)(rop, op.data[m]);\n" (sgen_ctyp_name ctyp))
      ^^ string "}"
  in
  let internal_vector_init =
    string (Printf.sprintf "static void internal_vector_init_%s(%s *rop, const int64_t len) {\n" (sgen_id id) (sgen_id id))
    ^^ string "  rop->len = len;\n"
    ^^ string (Printf.sprintf "  rop->data = sail_malloc(len * sizeof(%s));\n" (sgen_ctyp ctyp))
    ^^ (if not (is_stack_ctyp ctyp) then
          string "  for (int i = 0; i < len; i++) {\n"
          ^^ string (Printf.sprintf "    CREATE(%s)((rop->data) + i);\n" (sgen_ctyp_name ctyp))
          ^^ string "  }\n"
        else empty)
    ^^ string "}"
  in
  let vector_undefined =
    string (Printf.sprintf "static void undefined_vector_%s(%s *rop, sail_int len, %s elem) {\n" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
    ^^ string (Printf.sprintf "  rop->len = sail_int_get_ui(len);\n")
    ^^ string (Printf.sprintf "  rop->data = sail_malloc((rop->len) * sizeof(%s));\n" (sgen_ctyp ctyp))
    ^^ string "  for (int i = 0; i < (rop->len); i++) {\n"
    ^^ string (if is_stack_ctyp ctyp then
                 "    (rop->data)[i] = elem;\n"
               else
                 Printf.sprintf "    CREATE(%s)((rop->data) + i);\n    COPY(%s)((rop->data) + i, elem);\n" (sgen_ctyp_name ctyp) (sgen_ctyp_name ctyp))
    ^^ string "  }\n"
    ^^ string "}"
  in
  vector_init ^^ twice hardline
  ^^ vector_clear ^^ twice hardline
  ^^ vector_undefined ^^ twice hardline
  ^^ vector_access ^^ twice hardline
  ^^ vector_set ^^ twice hardline
  ^^ vector_update ^^ twice hardline
  ^^ internal_vector_update ^^ twice hardline
  ^^ internal_vector_init ^^ twice hardline

let codegen_vector ctx (direction, ctyp) =
  let id = mk_id (string_of_ctyp (CT_vector (direction, ctyp))) in
  if IdSet.mem id !generated then (
    empty, empty
  ) else (
    generated := IdSet.add id !generated;
    codegen_vector_header ctx id (direction, ctyp),
    codegen_vector_body ctx id (direction, ctyp)
  )

(**************************************************************************)
(* Code generation for definitions                                        *)
(**************************************************************************)

(** To keep things neat we use GCC's local labels extension to limit
   the scope of labels. We do this by iterating over all the blocks
   and adding a __label__ declaration with all the labels local to
   that block.

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

let is_decl = function
  | I_aux (I_decl _, _) -> true
  | _ -> false

let codegen_decl = function
  | I_aux (I_decl (ctyp, id), _) ->
     string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_name ctyp id))
  | _ -> assert false

let codegen_alloc = function
  | I_aux (I_decl (ctyp, id), _) when is_stack_ctyp ctyp -> empty
  | I_aux (I_decl (ctyp, id), _) ->
     string (Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name ctyp id))
  | _ -> assert false

let add_local_labels instrs =
  match map_instrs add_local_labels' (iblock instrs) with
  | I_aux (I_block instrs, _) -> instrs
  | _ -> assert false

let codegen_def_header ctx = function
  | CDEF_spec (id, _, arg_ctyps, ret_ctyp) ->
     if Env.is_extern id ctx.tc_env "c" then
       empty
     else if is_stack_ctyp ret_ctyp then
       ksprintf string "%s %s(%s%s);"
         (sgen_ctyp ret_ctyp) (sgen_function_id id) (extra_params ()) (Util.string_of_list ", " sgen_ctyp arg_ctyps)
       ^^ twice hardline
     else
       ksprintf string "void %s(%s%s *rop, %s);"
         (sgen_function_id id) (extra_params ()) (sgen_ctyp ret_ctyp) (Util.string_of_list ", " sgen_ctyp arg_ctyps)
       ^^ twice hardline

  | CDEF_type ctype_def ->
     codegen_type_def_header ctype_def

  | _ -> empty

let codegen_def_body ctx = function
  | CDEF_reg_dec _ -> empty

  | CDEF_spec _ -> empty

  | CDEF_fundef (id, ret_arg, args, instrs) as def ->
     let arg_ctyps, ret_ctyp = match Bindings.find_opt id ctx.valspecs with
       | Some vs -> vs
       | None ->
          Reporting.unreachable (id_loc id) __POS__ ("No valspec found for " ^ string_of_id id)
     in

     (* Check that the function has the correct arity at this point. *)
     if List.length arg_ctyps <> List.length args then
       Reporting.unreachable (id_loc id) __POS__
         ("function arguments "
          ^ Util.string_of_list ", " string_of_id args
          ^ " matched against type "
          ^ Util.string_of_list ", " string_of_ctyp arg_ctyps)
     else ();

     let instrs = add_local_labels instrs in
     let args = Util.string_of_list ", " (fun x -> x) (List.map2 (fun ctyp arg -> sgen_ctyp ctyp ^ " " ^ sgen_id arg) arg_ctyps args) in
     let function_header =
       match ret_arg with
       | None ->
          assert (is_stack_ctyp ret_ctyp);
          string (sgen_ctyp ret_ctyp) ^^ space ^^ codegen_function_id id ^^ parens (string (extra_params ()) ^^ string args) ^^ hardline
       | Some gs ->
          assert (not (is_stack_ctyp ret_ctyp));
          string "void" ^^ space ^^ codegen_function_id id
          ^^ parens (string (extra_params ()) ^^ string (sgen_ctyp ret_ctyp ^ " *" ^ sgen_id gs ^ ", ") ^^ string args)
          ^^ hardline
     in
     function_header
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs) ^^ hardline
     ^^ string "}"
     ^^ twice hardline

  | CDEF_type ctype_def ->
     codegen_type_def_body ctx ctype_def

  | CDEF_startup (id, instrs) ->
     let startup_header = string (Printf.sprintf "void startup_%s(void)" (sgen_function_id id)) in
     separate_map hardline codegen_decl instrs
     ^^ twice hardline
     ^^ startup_header ^^ hardline
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline codegen_alloc instrs) ^^ hardline
     ^^ string "}"

  | CDEF_finish (id, instrs) ->
     let finish_header = string (Printf.sprintf "void finish_%s(void)" (sgen_function_id id)) in
     separate_map hardline codegen_decl (List.filter is_decl instrs)
     ^^ twice hardline
     ^^ finish_header ^^ hardline
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs) ^^ hardline
     ^^ string "}"

  | CDEF_let (number, bindings, instrs) ->
     let instrs = add_local_labels instrs in
     let setup =
       List.concat (List.map (fun (id, ctyp) -> [idecl (id_loc id) ctyp (global id)]) bindings)
     in
     let cleanup =
       List.concat (List.map (fun (id, ctyp) -> [iclear ~loc:(id_loc id) ctyp (global id)]) bindings)
     in
     hardline ^^ string (Printf.sprintf "void sail_create_letbind_%d(sail_state *state) " number)
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline codegen_alloc setup) ^^ hardline
     ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") { ctx with no_raw = true }) instrs) ^^ hardline
     ^^ string "}"
     ^^ hardline ^^ string (Printf.sprintf "void sail_kill_letbind_%d(sail_state *state) " number)
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") ctx) cleanup) ^^ hardline
     ^^ string "}"
     ^^ twice hardline

(** As we generate C we need to generate specialized version of tuple,
   list, and vector type. These must be generated in the correct
   order. The ctyp_dependencies function generates a list of
   c_gen_typs in the order they must be generated. Types may be
   repeated in ctyp_dependencies so it's up to the code-generator not
   to repeat definitions pointlessly (using the !generated variable)
   *)
type c_gen_typ =
  | CTG_tup of ctyp list
  | CTG_list of ctyp
  | CTG_vector of bool * ctyp

let rec ctyp_dependencies = function
  | CT_tup ctyps -> List.concat (List.map ctyp_dependencies ctyps) @ [CTG_tup ctyps]
  | CT_list ctyp -> ctyp_dependencies ctyp @ [CTG_list ctyp]
  | CT_vector (direction, ctyp) | CT_fvector (_, direction, ctyp) -> ctyp_dependencies ctyp @ [CTG_vector (direction, ctyp)]
  | CT_ref ctyp -> ctyp_dependencies ctyp
  | CT_struct (_, ctors) -> List.concat (List.map (fun (_, ctyp) -> ctyp_dependencies ctyp) ctors)
  | CT_variant (_, ctors) -> List.concat (List.map (fun (_, ctyp) -> ctyp_dependencies ctyp) ctors)
  | CT_lint | CT_fint _ | CT_lbits _ | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_bit | CT_string | CT_enum _ | CT_poly | CT_constant _ -> []

let codegen_ctg ctx = function
  | CTG_vector (direction, ctyp) -> codegen_vector ctx (direction, ctyp)
  | CTG_tup ctyps -> codegen_tup ctx ctyps
  | CTG_list ctyp -> codegen_list ctx ctyp

let codegen_progress n total = function
  | CDEF_reg_dec (id, _, _) ->
     Util.progress "Codegen " ("R " ^ string_of_id id) n total
  | CDEF_fundef (id, _, _, _) ->
     Util.progress "Codegen " (string_of_id id) n total
  | _ ->
     Util.progress "Codegen " "" n total

(** When we generate code for a definition, we need to first generate
   any auxillary type definitions that are required. *)
let codegen_def n total ctx def =
  codegen_progress n total def;
  let ctyps = cdef_ctyps def |> CTSet.elements in
  (* We should have erased any polymorphism introduced by variants at this point! *)
  if List.exists is_polymorphic ctyps then
    let polymorphic_ctyps = List.filter is_polymorphic ctyps in
    Reporting.unreachable Parse_ast.Unknown __POS__
      (sprintf "Found polymorphic types:\n%s\nwhile generating definition."
         (Util.string_of_list "\n" string_of_ctyp polymorphic_ctyps))
  else
    let deps = List.concat (List.map ctyp_dependencies ctyps) in
    let deps_header, deps_body = List.map (codegen_ctg ctx) deps |> List.split in
    concat deps_header ^^ codegen_def_header ctx def,
    concat deps_body ^^ codegen_def_body ctx def

let codegen_state_struct_def ctx = function
  | CDEF_reg_dec (id, ctyp, _) ->
     ksprintf string "    %s %s;" (sgen_ctyp ctyp) (sgen_id id) ^^ hardline

  | CDEF_let (_, [], _) -> empty
  | CDEF_let (_, bindings, _) ->
     separate_map hardline (fun (id, ctyp) -> string (Printf.sprintf "    %s %s;" (sgen_ctyp ctyp) (sgen_id id))) bindings
     ^^ hardline

  | _ -> empty

let codegen_state_function_body_on_match id body =
  let is_external = List.exists (fun regex -> Str.string_match (Str.regexp regex) id 0) O.opts.external_state_api in
  if is_external then
    ("" ,";")
  else
    ("static inline ", Printf.sprintf " { %s }" body) 

let codegen_state_api_struct id ctyp =
  match ctyp with
  | CT_struct (_, fields) ->
     let codegen_state_api_field ((fid, _), ctyp) =
       if is_api_ctyp ctyp then
         let set_attrs, set_body = codegen_state_function_body_on_match (sgen_id fid) (Printf.sprintf "st->%s.%s = u;" (sgen_id id) (sgen_id fid)) in 
         let get_attrs, get_body = codegen_state_function_body_on_match (sgen_id fid) (Printf.sprintf "return st->%s.%s;" (sgen_id id) (sgen_id fid)) in
         ksprintf string "%svoid state_set_%s_in_%s(sail_state* st, %s u)%s"
           set_attrs (sgen_id fid) (sgen_id id) (sgen_ctyp ctyp) set_body
         ^^ hardline
         ^^ ksprintf string "%s%s state_get_%s_in_%s(sail_state* st)%s"
              get_attrs (sgen_ctyp ctyp) (sgen_id fid) (sgen_id id) get_body
       else
         empty
     in
     separate_map hardline codegen_state_api_field fields ^^ hardline
  | _ -> empty

let codegen_state_api_vector id ctyp vctyp =
  let attrs, body = codegen_state_function_body_on_match (sgen_id id) (Printf.sprintf "vector_update_%s(rop, op, n, elem);" (sgen_ctyp ctyp)) in
  string (Printf.sprintf "%svoid state_vector_update_%s(sail_state* st, %s *rop, %s op, sail_int n, %s elem)%s"
          attrs (sgen_id id) (sgen_ctyp ctyp) (sgen_ctyp ctyp) (sgen_ctyp vctyp) body)
    ^^ hardline ^^
  let attrs, body = codegen_state_function_body_on_match (sgen_id id) (Printf.sprintf "return vector_access_%s(op, n);" (sgen_ctyp ctyp)) in
  string (Printf.sprintf "%s%s state_vector_access_%s(sail_state* st, %s op, sail_int n)%s"
    attrs (sgen_ctyp vctyp) (sgen_id id) (sgen_ctyp ctyp) body)
    ^^ hardline

let codegen_state_api_reg_dec id ctyp =
  begin match ctyp with
  | _ when is_api_ctyp ctyp ->
    let attrs, body = codegen_state_function_body_on_match (sgen_id id) (Printf.sprintf "return st->%s;" (sgen_id id)) in
    ksprintf string "%s%s state_get_%s(sail_state* st)%s" attrs (sgen_ctyp ctyp) (sgen_id id) body ^^ hardline ^^ 
    let attrs, body = codegen_state_function_body_on_match (sgen_id id) (Printf.sprintf "st->%s = n;" (sgen_id id)) in
    ksprintf string "%svoid state_set_%s(sail_state* st, %s n)%s" attrs (sgen_id id) (sgen_ctyp ctyp) body ^^ hardline ^^
    codegen_state_api_struct id ctyp
  | CT_vector (_, vctyp) when is_api_ctyp vctyp -> codegen_state_api_vector id ctyp vctyp 
  | CT_fvector (_, _, vctyp) when is_api_ctyp vctyp -> codegen_state_api_vector id ctyp vctyp 
  | _ -> empty
  end

let codegen_state_api ctx = function
| CDEF_reg_dec (id, ctyp, _) -> codegen_state_api_reg_dec id ctyp
| CDEF_let (_, [], _) -> empty
| CDEF_let (_, bindings, _) ->
    separate_map hardline (fun (id, ctyp) -> codegen_state_api_reg_dec id ctyp) bindings 
    ^^ hardline
| _ -> empty

let codegen_state_struct ctx cdefs =
  string "struct sail_state {" ^^ hardline
  ^^ concat_map (codegen_state_struct_def ctx) cdefs
  ^^ (if not (Bindings.mem (mk_id "exception") ctx.variants) then (
        empty
      ) else (
        string "    // exception handling support" ^^ hardline
        ^^ ksprintf string "    struct %s *current_exception;" (sgen_id (mk_id "exception")) ^^ hardline
        ^^ string "    bool have_exception;" ^^ hardline
        ^^ string "    sail_string *throw_location;" ^^ hardline
     ))
  ^^ concat_map (fun str -> string ("    " ^ str ^ ";") ^^ hardline) O.opts.extra_state
  ^^ string "};" ^^ hardline ^^ hardline
  ^^ concat_map (codegen_state_api ctx) cdefs

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

let rec get_recursive_functions defs =
  match defs with
  | DEF_internal_mutrec fundefs :: defs ->
     IdSet.union (List.map id_of_fundef fundefs |> IdSet.of_list) (get_recursive_functions defs)

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
       IdSet.add (id_of_fundef fdef) (get_recursive_functions defs)
     else
       get_recursive_functions defs

  | _ :: defs -> get_recursive_functions defs
  | [] -> IdSet.empty

let codegen_output file_name docs =
  let chan = open_out file_name in
  output_string chan (Pretty_print_sail.to_string docs);
  flush chan;
  close_out chan

let add_extra_header str =
  if String.length str > 0 then (
    if str.[0] == '<' && str.[String.length str - 1] == '>' then
      string ("#include " ^ str) ^^ hardline
    else
      string ("#include \"" ^ str ^ "\"") ^^ hardline
  ) else (
    empty
  )

let codegen ctx output_name cdefs =
  let total = List.length cdefs in
  let docs_header, docs_body = List.mapi (fun n def -> codegen_def (n + 1) total ctx def) cdefs |> List.split in

  let state = codegen_state_struct ctx cdefs in

  let stdlib_headers =
    string "#include <stdint.h>" ^^ hardline
    ^^ string "#include <stdbool.h>"
  in
  let sail_headers =
    string "#include \"sail_state.h\"" ^^ hardline
    ^^ string "#include \"sail.h\"" ^^ hardline
    ^^ string "#include \"sail_failure.h\""
  in

  let register_init_clear (id, ctyp, instrs) =
    if is_stack_ctyp ctyp then
      List.map (sgen_instr (mk_id "reg") ctx) instrs, []
    else
      [ Printf.sprintf "  CREATE(%s)(&(state->%s));" (sgen_ctyp_name ctyp) (sgen_id id) ]
      @ List.map (sgen_instr (mk_id "reg") ctx) instrs,
      [ Printf.sprintf "  KILL(%s)(&(state->%s));" (sgen_ctyp_name ctyp) (sgen_id id) ]
  in

  let header_symbol = String.uppercase_ascii (Filename.basename output_name) in
  let header =
    ksprintf string "#ifndef SAILC_%s_H" header_symbol ^^ hardline 
    ^^ ksprintf string "#define SAILC_%s_H" header_symbol ^^ hardline
    ^^ stdlib_headers ^^ hardline
    ^^ sail_headers ^^ hardline
    ^^ concat_map add_extra_header O.opts.extra_headers ^^ hardline
    ^^ concat docs_header
    ^^ state
    ^^ twice hardline
    ^^ string "void sail_initialize_state(sail_state *state);"
    ^^ hardline
    ^^ string "void sail_finalize_state(sail_state *state);"
    ^^ twice hardline
    ^^ string "#endif"
    ^^ hardline
  in

  let regs = c_ast_registers cdefs in

  let letbind_initializers =
    List.map (fun n -> sprintf "  sail_create_letbind_%d(state);" n) (List.rev ctx.letbinds)
  in
  let letbind_finalizers =
    List.map (fun n -> sprintf "  sail_kill_letbind_%d(state);" n) ctx.letbinds
  in

  let body =
    ksprintf string "#include \"%s.h\"" (Filename.basename output_name)
    ^^ twice hardline
    ^^ concat docs_body
    ^^ string "void sail_initialize_letbindings(sail_state *state) {" ^^ hardline
    ^^ separate_map hardline string letbind_initializers ^^ hardline
    ^^ string "}"
    ^^ twice hardline
    ^^ string "void sail_finalize_letbindings(sail_state *state) {" ^^ hardline
    ^^ separate_map hardline string letbind_finalizers ^^ hardline
    ^^ string "}"
    ^^ twice hardline
    ^^ string "void sail_initialize_state(sail_state *state) {" ^^ hardline
    ^^ separate_map hardline string (List.map (fun r -> fst (register_init_clear r)) regs |> List.concat)
    ^^ (if not (Bindings.mem (mk_id "exception") ctx.variants) then (
          empty
        ) else (
          string "  state->have_exception = false;"
          ^^ ksprintf string "  state->current_exception = sail_malloc(sizeof(struct %s));"
            (sgen_id (mk_id "exception")) ^^ hardline
          ^^ ksprintf string "  CREATE(%s)(state->current_exception);" (sgen_id (mk_id "exception")) ^^ hardline
          ^^ string "  state->throw_location = sail_malloc(sizeof(sail_string));" ^^ hardline
          ^^ string "  CREATE(sail_string)(state->throw_location);"
       ))
    ^^ hardline
    ^^ string "  sail_initialize_letbindings(state);"  ^^ hardline
    ^^ string "}"
    ^^ twice hardline
    ^^ string "void sail_finalize_state(sail_state *state) {" ^^ hardline
    ^^ separate_map hardline string (List.map (fun r -> snd (register_init_clear r)) regs |> List.concat)
    ^^ (if not (Bindings.mem (mk_id "exception") ctx.variants) then (
          empty
        ) else (
          ksprintf string "  KILL(%s)(state->current_exception);" (sgen_id (mk_id "exception")) ^^ hardline
          ^^ string "  sail_free(state->current_exception);" ^^ hardline
          ^^ string "  KILL(sail_string)(state->throw_location);" ^^ hardline
          ^^ string "  sail_free(state->throw_location);"
       ))
    ^^ hardline
    ^^ string "  sail_finalize_letbindings(state);"  ^^ hardline
    ^^ string "}"
    ^^ hardline
  in

  codegen_output (output_name ^ ".h") header;
  codegen_output (output_name ^ ".c") body

let emulator ctx output_name cdefs =
  codegen ctx output_name cdefs;

  let headers = separate hardline
    ([ string "#include \"sail.h\"";
       string "#include \"sail_failure.h\"";
       string "#include \"rts.h\"";
       string "#include \"elf.h\"";
       ksprintf string "#include \"%s.h\"" (Filename.basename output_name) ]
     @ (List.map (fun h -> string (Printf.sprintf "#include \"%s\"" h)) [] (*c_includes*)))
  in

  let startup cdefs =
    List.map sgen_startup (List.filter is_cdef_startup cdefs)
  in
  let finish cdefs =
    List.map sgen_finish (List.filter is_cdef_finish cdefs)
  in

  let regs = c_ast_registers cdefs in

  let model_init = separate hardline (List.map string
     ( [ "void model_initialize(sail_state *state)";
         "{";
         "  sail_initialize_state(state);";
         "  setup_rts();" ]
     @ startup cdefs
     @ (if regs = [] then [] else [ Printf.sprintf "  %s(state, UNIT);" (sgen_function_id (mk_id "initialize_registers")) ])
     @ [ "}" ] ))
  in

  let model_fini = separate hardline (List.map string
     ( [ "void model_finalize(sail_state *state)";
         "{" ]
     @ finish cdefs
     @ [ "  cleanup_rts();";
         "  sail_finalize_state(state);";
         "}" ]))
  in

  let model_default_main = separate hardline (List.map string
       ([ "int model_main(int argc, char *argv[])";
          "{";
          "  sail_state state;";
          "  model_initialize(&state);";
          "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
          sprintf "  %s(&state, UNIT);" (sgen_function_id (mk_id "main")) ]
        @ (if not (Bindings.mem (mk_id "exception") ctx.variants) then [] else
             [ "  if (state.have_exception) {fprintf(stderr, \"Exiting due to uncaught exception: %s\\n\", *state.throw_location);}" ])
        @ [ "  model_finalize(&state);" ]
        @ (if not (Bindings.mem (mk_id "exception") ctx.variants) then [] else
             [ "  if (state.have_exception) {return(EXIT_FAILURE);}" ])
        @ [ "  return EXIT_SUCCESS;";
            "}" ]))
  in

  let model_main = separate hardline (List.map string
       [ "int main(int argc, char *argv[])";
         "{";
         "  return model_main(argc, argv);";
         "}" ])
  in

  let emu =
    headers ^^ twice hardline
    ^^ model_init ^^ twice hardline
    ^^ model_fini ^^ twice hardline
    ^^ model_default_main ^^ twice hardline
    ^^ model_main ^^ hardline
  in
  codegen_output (output_name ^ "_emu.c") emu

end
