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
(*  Copyright (c) 2013-2026                                                 *)
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
open Ast_compare
open Ast_util
open Bit
open Type_check

module J = Yojson.Safe

let typ_is_record env = function
  | Typ_aux (Typ_id id, _) -> Env.is_record id env
  | Typ_aux (Typ_app (id, _), _) -> Env.is_record id env
  | _ -> false

let typ_is_variant env = function
  | Typ_aux (Typ_id id, _) -> Env.is_variant id env
  | Typ_aux (Typ_app (id, _), _) -> Env.is_variant id env
  | _ -> false

let typ_is_enum env = function Typ_aux (Typ_id id, _) -> Env.is_enum id env | _ -> false

let destruct_typ_args = function
  | Typ_aux (Typ_id id, _) -> Some (id, [])
  | Typ_aux (Typ_app (id, args), _) -> Some (id, args)
  | _ -> None

let find_json ~at:l full_parts json =
  let rec go parts json =
    match (parts, json) with
    | [], json -> Some json
    | part :: parts, `Assoc obj -> (
        match List.assoc_opt part obj with Some json -> go parts json | None -> None
      )
    | parts, json ->
        let full_parts = String.concat "." full_parts in
        let parts = String.concat "." parts in
        Printf.sprintf "Attempting to access configuration %s of %s, but JSON is %s" parts full_parts (J.to_string json)
        |> Reporting.err_general l |> raise
  in
  go full_parts json

let json_bit ~at:l = function
  | `Bool true -> Bin_1
  | `Bool false -> Bin_0
  | json -> raise (Reporting.err_general l (Printf.sprintf "Failed to interpret %s as a bit" (J.to_string json)))

let json_to_string = function `String s -> Some s | _ -> None

let valid_bin_char c = match c with '_' -> None | '0' -> Some (Some Bin_0) | '1' -> Some (Some Bin_1) | _ -> Some None

let valid_dec_char c =
  match c with
  | '_' -> None
  | ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9') as c -> Some (Some c)
  | _ -> Some None

let valid_hex_char c =
  if c = '_' then None
  else (match Initial_check.hex_digit_of_char c with Some (digit, _) -> Some (Some digit) | None -> Some None)

let bin_digit_to_bit = function Bin_0 -> B0 | Bin_1 -> B1

let fix_length ~at:l ~len bitlist =
  let open Extraction.ValueType in
  match Primops.zero_extend (V_bitvector bitlist) (V_int (Big_int.of_int len)) with
  | Some (V_bitvector bitlist) -> bitlist
  | _ ->
      Reporting.warn ~force_show:true Version.v0_20_2 "Configuration" l
        "Forced to truncate configuration bitvector literal";
      let d = len - List.length bitlist in
      Util.drop (abs d) bitlist

let bitlist_to_literal bitlist = non_empty_singleton (List.map (function B0 -> Bin_0 | B1 -> Bin_1) bitlist)

let parse_json_string_to_bits ~at:l ~len str =
  let open Util.Option_monad in
  let str_len = String.length str in
  let chars = str |> String.to_seq |> List.of_seq in
  let* bitlist =
    if str_len > 2 && String.sub str 0 2 = "0b" then
      let* bin_digits = Util.drop 2 chars |> List.filter_map valid_bin_char |> Util.option_all in
      Some (List.map bin_digit_to_bit bin_digits |> fix_length ~at:l ~len)
    else if str_len > 2 && String.sub str 0 2 = "0x" then
      let* hex_digits = Util.drop 2 chars |> List.filter_map valid_hex_char |> Util.option_all in
      Some (List.concat_map BitList.of_hex_digit hex_digits |> fix_length ~at:l ~len)
    else
      let* dec_chars = List.filter_map valid_dec_char chars |> Util.option_all in
      let n = List.to_seq dec_chars |> String.of_seq |> Big_int.of_string in
      Some (Sail_lib.get_slice_int (Big_int.of_int len, n, Big_int.zero))
  in
  Some (mk_lit_exp ~loc:l (L_bin (bitlist_to_literal bitlist)))

let parse_json_string_to_abstract_bits ~at:l ~len str =
  let open Util.Option_monad in
  let str_len = String.length str in
  let chars = str |> String.to_seq |> List.of_seq in
  let mask bitlist =
    mk_exp (E_app (mk_id "sail_mask", [mk_exp (E_sizeof (nid len)); mk_lit_exp (L_bin (bitlist_to_literal bitlist))]))
    |> locate (fun _ -> l)
  in
  let slice_int n =
    mk_exp
      (E_app
         (mk_id "get_slice_int", [mk_exp (E_sizeof (nid len)); mk_lit_exp (L_num n); mk_lit_exp (L_num Big_int.zero)])
      )
    |> locate (fun _ -> l)
  in
  if str_len > 2 && String.sub str 0 2 = "0b" then
    let* bin_digits = Util.drop 2 chars |> List.filter_map valid_bin_char |> Util.option_all in
    Some (List.map bin_digit_to_bit bin_digits |> mask)
  else if str_len > 2 && String.sub str 0 2 = "0x" then
    let* hex_digits = Util.drop 2 chars |> List.filter_map valid_hex_char |> Util.option_all in
    Some (List.concat_map BitList.of_hex_digit hex_digits |> mask)
  else
    let* dec_chars = List.filter_map valid_dec_char chars |> Util.option_all in
    let n = List.to_seq dec_chars |> String.of_seq |> Big_int.of_string in
    Some (slice_int n)

module type CONFIG_VALUE = sig
  type t

  val num : Parse_ast.l -> Big_int.num -> t

  val enum_member : Parse_ast.l -> string -> t

  val string : Parse_ast.l -> string -> t

  val bool : Parse_ast.l -> bool -> t

  val unit : Parse_ast.l -> t

  val hex : Parse_ast.l -> hex_digit non_empty list -> t

  val bin : Parse_ast.l -> bin_digit non_empty list -> t

  val vector : Parse_ast.l -> t list -> t

  val list : Parse_ast.l -> t list -> t

  val structure : Parse_ast.l -> id -> (id * t) list -> t

  val ctor : Parse_ast.l -> id -> t -> t

  val abstract_bits : Parse_ast.l -> id -> string -> t option
end

module ConfigExp : CONFIG_VALUE with type t = uannot exp = struct
  type t = uannot exp

  let num l n = mk_lit_exp ~loc:l (L_num n)

  let enum_member l s = mk_exp ~loc:l (E_id (mk_id ~loc:l s))

  let string l s = mk_lit_exp ~loc:l (L_string s)

  let bool l b = mk_lit_exp ~loc:l (if b then L_true else L_false)

  let unit l = mk_lit_exp ~loc:l L_unit

  let hex l digits = mk_lit_exp ~loc:l (L_hex digits)

  let bin l digits = mk_lit_exp ~loc:l (L_bin digits)

  let vector l items = mk_exp ~loc:l (E_vector items)

  let list l items = mk_exp ~loc:l (E_list items)

  let structure l id fields = mk_exp ~loc:l (E_struct (SN_id id, List.map (fun (f, v) -> mk_fexp ~loc:l f v) fields))

  let ctor l id v = mk_exp ~loc:l (E_app (id, [v]))

  let abstract_bits l len s = parse_json_string_to_abstract_bits ~at:l ~len s
end

module ConfigValue : CONFIG_VALUE with type t = value = struct
  type t = value

  let num _ n = V_int n

  let enum_member l s = V_member (mk_id ~loc:l s)

  let string _ s = V_string s

  let bool _ b = V_bool b

  let unit _ = V_unit

  let hex _ digits = V_bitvector (Extraction.BitList.of_hex_lit digits)

  let bin _ digits = V_bitvector (Extraction.BitList.of_bin_lit digits)

  let vector _ items = V_vector items

  let list _ items = V_list items

  let structure _ _ fields = V_record fields

  let ctor _ id v = V_ctor (id, [v])

  let abstract_bits _ _ _ = None
end

module Parse (V : CONFIG_VALUE) = struct
  let parse_json_string_to_bits ~at:l ~len str =
    let open Util.Option_monad in
    let str_len = String.length str in
    let chars = str |> String.to_seq |> List.of_seq in
    let* bitlist =
      if str_len > 2 && String.sub str 0 2 = "0b" then
        let* bin_digits = Util.drop 2 chars |> List.filter_map valid_bin_char |> Util.option_all in
        Some (List.map bin_digit_to_bit bin_digits |> fix_length ~at:l ~len)
      else if str_len > 2 && String.sub str 0 2 = "0x" then
        let* hex_digits = Util.drop 2 chars |> List.filter_map valid_hex_char |> Util.option_all in
        Some (List.concat_map BitList.of_hex_digit hex_digits |> fix_length ~at:l ~len)
      else
        let* dec_chars = List.filter_map valid_dec_char chars |> Util.option_all in
        let n = List.to_seq dec_chars |> String.of_seq |> Big_int.of_string in
        Some (Sail_lib.get_slice_int (Big_int.of_int len, n, Big_int.zero))
    in
    Some (V.bin l (bitlist_to_literal bitlist))

  let rec from_json ~at:l abstracts env typ =
    let open Util.Option_monad in
    function
    | `Int n -> V.num l (Big_int.of_int n)
    | `Intlit n -> V.num l (Big_int.of_string n)
    | `String s ->
        if Option.is_some (Type_check.destruct_numeric typ) then V.num l (Big_int.of_string s)
        else if typ_is_enum env typ then V.enum_member l s
        else V.string l s
    | `Bool b -> V.bool l b
    | `Null -> V.unit l
    | `List jsons -> (
        let base_typ = match destruct_exist typ with None -> typ | Some (_, _, typ) -> typ in
        match base_typ with
        | Typ_aux (Typ_app (id, args), _) -> (
            match (string_of_id id, args) with
            | "bitvector", _ -> V.bin l (non_empty_singleton (List.map (json_bit ~at:l) jsons))
            | "vector", [_; A_aux (A_typ item_typ, _)] ->
                let items = List.map (from_json ~at:l abstracts env item_typ) jsons in
                V.vector l items
            | "list", [A_aux (A_typ item_typ, _)] ->
                let items = List.map (from_json ~at:l abstracts env item_typ) jsons in
                V.list l items
            | _ -> raise (Reporting.err_general l ("Failed to interpret JSON list as Sail type " ^ string_of_typ typ))
          )
        | _ -> raise (Reporting.err_general l ("Failed to interpret JSON list as Sail type " ^ string_of_typ typ))
      )
    | `Assoc obj -> (
        let base_typ = match destruct_exist typ with None -> typ | Some (_, _, typ) -> typ in
        let exp_opt =
          if typ_is_record env base_typ then
            let* id, _ = destruct_typ_args base_typ in
            let _, field_info = Env.get_record id env in
            let* fields =
              List.map
                (fun (field_typ, field_id) ->
                  let* field_json = List.assoc_opt (string_of_id field_id) obj in
                  let exp = from_json ~at:l abstracts env field_typ field_json in
                  Some (field_id, exp)
                )
                field_info
              |> Util.option_all
            in
            Some (V.structure l id fields)
          else if typ_is_variant env base_typ then
            let* id, args = destruct_typ_args base_typ in
            match obj with
            | [(ctor, value)] -> (
                let ctor = mk_id ~loc:l ctor in
                match List.find_opt (fun (id, _) -> Id.compare id ctor = 0) @@ instantiate_variant env id args with
                | None ->
                    raise
                      (Reporting.err_general l
                         (Printf.sprintf "Constructor %s in JSON configuration is not a valid constructor for union %s"
                            (string_of_id ctor) (string_of_id id)
                         )
                      )
                | Some (_, typ) ->
                    let exp = from_json ~at:l abstracts env typ value in
                    Some (V.ctor l ctor exp)
              )
            | _ ->
                raise
                  (Reporting.err_general l
                     (Printf.sprintf "JSON does not appear to contain a valid Sail union member for %s" (string_of_id id)
                     )
                  )
          else (
            match base_typ with
            | Typ_aux (Typ_app (id, args), _) -> (
                match (string_of_id id, args) with
                | "bitvector", _ -> (
                    let* len = List.assoc_opt "len" obj in
                    let* value = Option.bind (List.assoc_opt "value" obj) json_to_string in
                    match len with
                    | `Int len -> parse_json_string_to_bits ~at:l ~len value
                    | `String len -> (
                        match abstracts (mk_id len) with
                        | Some len -> parse_json_string_to_bits ~at:l ~len value
                        | None -> V.abstract_bits l (mk_id len) value
                      )
                    | _ -> None
                  )
                | _ -> None
              )
            | _ -> None
          )
        in
        match exp_opt with
        | Some exp -> exp
        | None ->
            raise
              (Reporting.err_general l
                 (Printf.sprintf "Failed to interpret JSON object %s as Sail type %s"
                    (J.to_string (`Assoc obj))
                    (string_of_typ typ)
                 )
              )
      )
    | json ->
        raise
          (Reporting.err_general l
             (Printf.sprintf "Failed to interpret JSON %s as Sail type %s" (J.to_string json) (string_of_typ typ))
          )
end

module ParseExp = Parse (ConfigExp)

let exp_from_json ~at:l env typ json = ParseExp.from_json ~at:l (fun _ -> None) env typ json

module ParseValue = Parse (ConfigValue)

let get_abstract_len ~at:l id env json =
  match Option.bind (Env.get_abstract_typ_key id env) (fun key -> find_json ~at:l key json) with
  | None ->
      raise
        (Reporting.err_general l
           (Printf.sprintf "Abstract type %s has no definition in JSON configuration" (string_of_id id))
        )
  | Some obj -> (
      match obj with
      | `Int n -> n
      | `Intlit s -> int_of_string s
      | _ ->
          raise
            (Reporting.err_general l
               (Printf.sprintf "Expected JSON width for abstract type %s to be an integer" (string_of_id id))
            )
    )

let value_from_json ~at:l env typ json =
  ParseValue.from_json ~at:l (fun id -> Some (get_abstract_len ~at:l id env json)) env typ json
