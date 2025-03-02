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
(*  Copyright (c) 2013-2025                                                 *)
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
open Ast_defs
open Ast_util
open Rewriter
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

module ConfigTypes : sig
  type config_type = { loc : Ast.l; env : env; typ : typ }

  type t

  val to_schema : ?root:bool -> t -> J.t

  val create : unit -> t

  val insert : string list -> config_type -> t -> unit

  val insert_abstract : string list -> id -> kind_aux -> t -> unit

  val insert_abstract_constraint : string list -> n_constraint -> t -> unit
end = struct
  open Util.Option_monad
  open Error_format

  type config_type = { loc : Ast.l; env : env; typ : typ }

  type schema_logic =
    | All_of of schema_logic list
    | Any_of of schema_logic list
    | Not of schema_logic
    | Schema of (string * J.t) list

  let rec logic_type schema_type = function
    | All_of schemas -> All_of (List.map (logic_type schema_type) schemas)
    | Any_of schemas -> Any_of (List.map (logic_type schema_type) schemas)
    | Not schema -> All_of [Schema (schema_type []); Not (logic_type schema_type schema)]
    | Schema clauses -> Schema (schema_type clauses)

  let rec logic_to_schema = function
    | All_of [schema] -> logic_to_schema schema
    | All_of schemas -> `Assoc [("allOf", `List (List.map logic_to_schema schemas))]
    | Any_of schemas -> `Assoc [("anyOf", `List (List.map logic_to_schema schemas))]
    | Not schema -> `Assoc [("not", logic_to_schema schema)]
    | Schema clauses -> `Assoc clauses

  let any_of c1 c2 =
    match (c1, c2) with
    | Any_of schemas1, Any_of schemas2 -> Any_of (schemas1 @ schemas2)
    | Any_of schemas1, _ -> Any_of (schemas1 @ [c2])
    | _, Any_of schemas2 -> Any_of (c1 :: schemas2)
    | _ -> Any_of [c1; c2]

  let all_of c1 c2 =
    match (c1, c2) with
    | Schema clauses1, Schema clauses2 -> Schema (clauses1 @ clauses2)
    | All_of schemas1, All_of schemas2 -> All_of (schemas1 @ schemas2)
    | All_of schemas1, _ -> All_of (schemas1 @ [c2])
    | _, All_of schemas2 -> All_of (c1 :: schemas2)
    | _ -> All_of [c1; c2]

  module type CONSTRAINT = sig
    type var
    val is_var : var -> nexp -> bool

    val const : Big_int.num -> (string * J.t) list
    val maximum : Big_int.num -> (string * J.t) list
    val minimum : Big_int.num -> (string * J.t) list
    val exclusive_maximum : Big_int.num -> (string * J.t) list
    val exclusive_minimum : Big_int.num -> (string * J.t) list
  end

  module SchemaTypeConstraint (Gen : CONSTRAINT) = struct
    open Util.Option_monad
    let rec constraint_schema v (NC_aux (aux, _)) =
      match aux with
      | NC_equal (A_aux (A_nexp nexp, _), A_aux (A_nexp (Nexp_aux (Nexp_constant c, _)), _)) when Gen.is_var v nexp ->
          Some (Schema (Gen.const c))
      | NC_equal (A_aux (A_nexp (Nexp_aux (Nexp_constant c, _)), _), A_aux (A_nexp nexp, _)) when Gen.is_var v nexp ->
          Some (Schema (Gen.const c))
      | NC_and (nc1, nc2) ->
          let* c1 = constraint_schema v nc1 in
          let* c2 = constraint_schema v nc2 in
          Some (all_of c1 c2)
      | NC_or (nc1, nc2) ->
          let* c1 = constraint_schema v nc1 in
          let* c2 = constraint_schema v nc2 in
          Some (any_of c1 c2)
      | (NC_lt (nexp, Nexp_aux (Nexp_constant c, _)) | NC_gt (Nexp_aux (Nexp_constant c, _), nexp))
        when Gen.is_var v nexp ->
          Some (Schema (Gen.exclusive_maximum c))
      | (NC_le (nexp, Nexp_aux (Nexp_constant c, _)) | NC_ge (Nexp_aux (Nexp_constant c, _), nexp))
        when Gen.is_var v nexp ->
          Some (Schema (Gen.maximum c))
      | (NC_gt (nexp, Nexp_aux (Nexp_constant c, _)) | NC_lt (Nexp_aux (Nexp_constant c, _), nexp))
        when Gen.is_var v nexp ->
          Some (Schema (Gen.exclusive_minimum c))
      | (NC_ge (nexp, Nexp_aux (Nexp_constant c, _)) | NC_le (Nexp_aux (Nexp_constant c, _), nexp))
        when Gen.is_var v nexp ->
          Some (Schema (Gen.minimum c))
      | NC_true -> Some (Schema [])
      | NC_false -> Some (Not (Schema []))
      | NC_app (id, [A_aux (A_bool nc, _)]) when string_of_id id = "not" ->
          let* c = constraint_schema v nc in
          Some (Not c)
      | NC_set (nexp, set) when Gen.is_var v nexp -> Some (Any_of (List.map (fun n -> Schema (Gen.const n)) set))
      | _ -> None
  end

  let schema_integer clauses = ("type", `String "integer") :: clauses

  module IntegerConstraint = SchemaTypeConstraint (struct
    type var = kid
    let is_var v = function Nexp_aux (Nexp_var v', _) -> Kid.compare v v' = 0 | _ -> false

    let const n = [("const", `Intlit (Big_int.to_string n))]
    let maximum n = [("maximum", `Intlit (Big_int.to_string n))]
    let minimum n = [("minimum", `Intlit (Big_int.to_string n))]
    let exclusive_maximum n = [("exclusiveMaximum", `Intlit (Big_int.to_string n))]
    let exclusive_minimum n = [("exclusiveMinimum", `Intlit (Big_int.to_string n))]
  end)

  module IntegerIdConstraint = SchemaTypeConstraint (struct
    type var = id
    let is_var v = function Nexp_aux (Nexp_id v', _) -> Id.compare v v' = 0 | _ -> false

    let const n = [("const", `Intlit (Big_int.to_string n))]
    let maximum n = [("maximum", `Intlit (Big_int.to_string n))]
    let minimum n = [("minimum", `Intlit (Big_int.to_string n))]
    let exclusive_maximum n = [("exclusiveMaximum", `Intlit (Big_int.to_string n))]
    let exclusive_minimum n = [("exclusiveMinimum", `Intlit (Big_int.to_string n))]
  end)

  let array_constraint ?min_length ?max_length () =
    Util.option_these
      [
        Option.map (fun len -> ("minItems", `Intlit (Big_int.to_string len))) min_length;
        Option.map (fun len -> ("maxItems", `Intlit (Big_int.to_string len))) max_length;
      ]

  module ArrayConstraint = SchemaTypeConstraint (struct
    type var = kid
    let is_var v = function Nexp_aux (Nexp_var v', _) -> Kid.compare v v' = 0 | _ -> false

    let const n = array_constraint ~min_length:n ~max_length:n ()
    let maximum n = array_constraint ~max_length:n ()
    let minimum n = array_constraint ~min_length:n ()
    let exclusive_maximum n = array_constraint ~max_length:(Big_int.pred n) ()
    let exclusive_minimum n = array_constraint ~min_length:(Big_int.succ n) ()
  end)

  let bitvector_string_literal =
    `Assoc
      [
        ( "oneOf",
          `List
            [
              `Assoc [("type", `String "string"); ("pattern", `String "^0x[0-9a-fA-F_]+$")];
              `Assoc [("type", `String "string"); ("pattern", `String "^0b[0-1_]+$")];
              `Assoc [("type", `String "string"); ("pattern", `String "^[0-9_]+$")];
            ]
        );
      ]

  let type_schema { loc; env; typ } =
    let rec generate typ =
      let kopts, nc, typ =
        match destruct_exist typ with None -> ([], nc_true, typ) | Some destructure -> destructure
      in
      match (kopts, nc, typ) with
      | _, _, Typ_aux (Typ_app (id, [A_aux (A_nexp arg, _)]), _) when string_of_id id = "atom" -> (
          match (kopts, nc, arg) with
          | [], NC_aux (NC_true, _), nexp ->
              let* c = solve_unique env nexp in
              Some (`Assoc (schema_integer [("const", `Intlit (Big_int.to_string c))]))
          | [KOpt_aux (KOpt_kind (_, v), _)], nc, Nexp_aux (Nexp_var v', _) when Kid.compare v v' = 0 ->
              let* nc_logic =
                nc |> constraint_simp |> IntegerConstraint.constraint_schema v |> Option.map (logic_type schema_integer)
              in
              Some (logic_to_schema nc_logic)
          | _ -> None
        )
      | _, NC_aux (NC_true, _), Typ_aux (Typ_app (id, [A_aux (A_bool arg, _)]), _) when string_of_id id = "atom_bool"
        -> (
          match (kopts, arg) with
          | [KOpt_aux (KOpt_kind (_, v), _)], NC_aux (NC_var v', _) when Kid.compare v v' = 0 ->
              Some (`Assoc [("type", `String "boolean")])
          | _ -> None
        )
      | _, _, Typ_aux (Typ_app (id, [A_aux (A_nexp arg, _)]), _) when string_of_id id = "bitvector" -> (
          let schema_bool_array clauses =
            [("type", `String "array"); ("items", `Assoc [("type", `String "boolean")])] @ clauses
          in
          let schema_hex_object len_type clauses =
            [
              ("type", `String "object");
              ( "properties",
                `Assoc [("len", `Assoc (("type", `String len_type) :: clauses)); ("value", bitvector_string_literal)]
              );
              ("required", `List [`String "len"; `String "value"]);
              ("additionalProperties", `Bool false);
            ]
          in
          match (kopts, nc, arg) with
          | [], NC_aux (NC_true, _), Nexp_aux (Nexp_id id, _) when Env.is_abstract_typ id env ->
              Some (`Assoc (schema_hex_object "string" [("const", `String (string_of_id id))]))
          | [], NC_aux (NC_true, _), nexp ->
              let* c = solve_unique env nexp in
              Some
                (`Assoc
                  [
                    ( "oneOf",
                      `List
                        [
                          `Assoc (schema_bool_array (array_constraint ~min_length:c ~max_length:c ()));
                          `Assoc (schema_hex_object "integer" [("const", `Intlit (Big_int.to_string c))]);
                        ]
                    );
                  ]
                  )
          | [KOpt_aux (KOpt_kind (_, v), _)], nc, Nexp_aux (Nexp_var v', _) when Kid.compare v v' = 0 ->
              let* bool_array_nc_logic =
                nc |> constraint_simp |> ArrayConstraint.constraint_schema v |> Option.map (logic_type schema_bool_array)
              in
              let* hex_object_nc_logic =
                nc |> constraint_simp |> IntegerConstraint.constraint_schema v
                |> Option.map (logic_type (schema_hex_object "integer"))
              in
              Some (`Assoc [("oneOf", `List [logic_to_schema bool_array_nc_logic; logic_to_schema hex_object_nc_logic])])
          | _ -> None
        )
      | _, _, Typ_aux (Typ_app (id, [A_aux (A_nexp arg, _); A_aux (A_typ item_typ, _)]), _)
        when string_of_id id = "vector" -> (
          let* schema_items = generate item_typ in
          let schema_array clauses = [("type", `String "array"); ("items", schema_items)] @ clauses in
          match (kopts, nc, arg) with
          | [], NC_aux (NC_true, _), nexp ->
              let* c = solve_unique env nexp in
              Some (`Assoc (schema_array (array_constraint ~min_length:c ~max_length:c ())))
          | [KOpt_aux (KOpt_kind (_, v), _)], nc, Nexp_aux (Nexp_var v', _) when Kid.compare v v' = 0 ->
              let* nc_logic =
                nc |> constraint_simp |> ArrayConstraint.constraint_schema v |> Option.map (logic_type schema_array)
              in
              Some (logic_to_schema nc_logic)
          | _ -> None
        )
      | [], NC_aux (NC_true, _), Typ_aux (Typ_app (id, [A_aux (A_typ item_typ, _)]), _) when string_of_id id = "list" ->
          let* schema_items = generate item_typ in
          let schema_array clauses = [("type", `String "array"); ("items", schema_items)] @ clauses in
          Some (`Assoc (schema_array (array_constraint ())))
      (* Records here can't be existentially quantified because the
         existential quantifier might link multiple fields, and we
         can't capture that in the schema. *)
      | [], NC_aux (NC_true, _), _ when typ_is_record env typ ->
          let* id, args = destruct_typ_args typ in
          let fields = instantiate_record env id args in
          let* properties =
            List.map
              (fun (field_typ, field_id) ->
                let* schema = generate field_typ in
                Some (string_of_id field_id, schema)
              )
              fields
            |> Util.option_all
          in
          let record_schema =
            [
              ("type", `String "object");
              ("properties", `Assoc properties);
              ("required", `List (List.map (fun (_, field_id) -> `String (string_of_id field_id)) fields));
              ("additionalProperties", `Bool false);
            ]
          in
          Some (`Assoc record_schema)
      | [], NC_aux (NC_true, _), _ when typ_is_variant env typ ->
          let* id, args = destruct_typ_args typ in
          let constructors = instantiate_variant env id args in
          let* properties =
            List.map
              (fun (constructor, typ) ->
                let* schema = generate typ in
                Some (string_of_id constructor, schema)
              )
              constructors
            |> Util.option_all
          in
          let variant_schema =
            [
              ("type", `String "object");
              ("properties", `Assoc properties);
              ("minProperties", `Int 1);
              ("maxProperties", `Int 1);
            ]
          in
          Some (`Assoc variant_schema)
      | [], NC_aux (NC_true, _), Typ_aux (Typ_id id, _) when Env.is_enum id env ->
          let members = Env.get_enum id env in
          Some
            (`Assoc [("type", `String "string"); ("enum", `List (List.map (fun m -> `String (string_of_id m)) members))])
      | [], NC_aux (NC_true, _), Typ_aux (Typ_id id, _) -> (
          match string_of_id id with
          | "string" -> Some (`Assoc [("type", `String "string")])
          | "unit" -> Some (`Assoc [("type", `String "null")])
          | "bit" -> Some (`Assoc [("type", `String "boolean")])
          | _ -> None
        )
      | _ -> None
    in
    let* json = generate typ in
    (* The non-Assoc case here should perhaps be an error (or None), as this
       function should always generate a schema object. *)
    match json with
    | `Assoc obj -> Some (`Assoc (("description", `String (Reporting.short_loc_to_string loc)) :: obj))
    | json -> Some json

  let type_schema_or_error config_type =
    match type_schema config_type with
    | Some schema -> schema
    | None ->
        raise
          (Reporting.err_typ config_type.loc
             ("Failed to generate JSON Schema for configuration type " ^ string_of_typ config_type.typ)
          )

  let abstract_integer_schema id (NC_aux (_, l) as nc) =
    IntegerIdConstraint.constraint_schema id nc |> Option.map (logic_type schema_integer) |> Option.map logic_to_schema

  type t =
    | Abstract_type of id * kind_aux * n_constraint list
    | Sail_value of config_type * config_type list
    | Object of (string, t) Hashtbl.t

  let rec to_schema ?(root = true) = function
    | Object tbl ->
        let properties =
          Hashtbl.fold
            (fun key value props ->
              let schema = to_schema ~root:false value in
              (key, schema) :: props
            )
            tbl []
        in
        let properties = List.sort (fun (p1, _) (p2, _) -> String.compare p1 p2) properties in
        let required = ("required", `List (List.map (fun (p, _) -> `String p) properties)) in
        let schema_version =
          if root then [("$schema", `String "https://json-schema.org/draft/2020-12/schema")] else []
        in
        `Assoc (schema_version @ [("type", `String "object"); ("properties", `Assoc properties); required])
    | Sail_value (config_type, []) -> type_schema_or_error config_type
    | Sail_value (config_type, config_types) ->
        let schemas = config_type :: config_types |> List.map type_schema_or_error in
        `Assoc [("allOf", `List schemas)]
    | Abstract_type (id, K_bool, _) -> `Assoc [("type", `String "boolean")]
    | Abstract_type (id, K_int, constrs) -> (
        let schemas = List.map (abstract_integer_schema id) constrs |> Util.option_these in
        match schemas with
        | [] -> `Assoc [("type", `String "integer")]
        | [schema] -> schema
        | schemas -> `Assoc [("allOf", `List schemas)]
      )
    | Abstract_type (id, K_type, _) ->
        raise
          (Reporting.err_unreachable (id_loc id) __POS__
             ("Type-kinded configuration found for abstract type " ^ string_of_id id)
          )

  (* Random is false here for deterministic error messages *)
  let create () = Object (Hashtbl.create ~random:false 16)

  let rec get_example = function
    | Sail_value ({ loc; typ; _ }, _) -> Some (loc, typ)
    | Object tbl -> Hashtbl.fold (fun _ value acc -> if Option.is_none acc then get_example value else acc) tbl None
    | Abstract_type _ -> None

  let subkey_error l full_parts obj =
    let full_parts = String.concat "." full_parts in
    let extra_info msg =
      match get_example obj with
      | Some (l, typ) -> Seq [msg; Line ""; Line "For example:"; Location ("", Some "used here", l, Seq [])]
      | None -> msg
    in
    let msg =
      Line (Printf.sprintf "Attempting to access key %s, but various subkeys have already been used" full_parts)
    in
    let b = Buffer.create 1024 in
    format_message (extra_info msg) (buffer_formatter b);
    raise (Reporting.err_general l (Buffer.contents b))

  let insert_with full_parts l map f =
    let rec go parts map =
      match (parts, map) with
      | [part], Object tbl -> f part tbl (Hashtbl.find_opt tbl part)
      | part :: parts, Object tbl -> (
          match Hashtbl.find_opt tbl part with
          | Some map -> go parts map
          | None ->
              Hashtbl.add tbl part (create ());
              go (part :: parts) map
        )
      | _ -> Reporting.unreachable l __POS__ "Failed to insert into config type map"
    in
    go full_parts map

  let insert full_parts config_type map =
    insert_with full_parts config_type.loc map (fun part tbl -> function
      | None -> Hashtbl.add tbl part (Sail_value (config_type, []))
      | Some (Sail_value (h_types, t_types)) -> Hashtbl.replace tbl part (Sail_value (config_type, h_types :: t_types))
      | Some obj -> subkey_error config_type.loc full_parts obj
    )

  let insert_abstract full_parts id kind_aux map =
    insert_with full_parts (id_loc id) map (fun part tbl -> function
      | None -> Hashtbl.add tbl part (Abstract_type (id, kind_aux, []))
      | Some obj -> subkey_error (id_loc id) full_parts obj
    )

  let insert_abstract_constraint full_parts (NC_aux (_, l) as nc) map =
    insert_with full_parts l map (fun part tbl -> function
      | None -> ()
      | Some (Abstract_type (id, kind_aux, ncs)) -> Hashtbl.replace tbl part (Abstract_type (id, kind_aux, nc :: ncs))
      | Some obj -> subkey_error l full_parts obj
    )
end

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
  | `Bool true -> '1'
  | `Bool false -> '0'
  | json -> raise (Reporting.err_general l (Printf.sprintf "Failed to interpret %s as a bit" (J.to_string json)))

let json_to_string = function `String s -> Some s | _ -> None

let valid_bin_char c = match c with '_' -> None | ('0' | '1') as c -> Some (Some c) | _ -> Some None

let valid_dec_char c =
  match c with
  | '_' -> None
  | ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9') as c -> Some (Some c)
  | _ -> Some None

let valid_hex_char c =
  match Char.uppercase_ascii c with
  | '_' -> None
  | ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | 'A' | 'B' | 'C' | 'D' | 'E' | 'F') as c -> Some (Some c)
  | _ -> Some None

let hex_char_to_bits c =
  match Sail2_values.nibble_of_char c with Some (b1, b2, b3, b4) -> [b1; b2; b3; b4] | None -> []

let bin_char_to_bit c = match c with '0' -> Sail2_values.B0 | '1' -> Sail2_values.B1 | _ -> Sail2_values.BU

let fix_length ~at:l ~len bitlist =
  let d = len - List.length bitlist in
  if d = 0 then bitlist
  else if d > 0 then Sail2_operators_bitlists.zero_extend bitlist (Big_int.of_int len)
  else (
    Reporting.warn ~force_show:true "Configuration" l "Forced to truncate configuration bitvector literal";
    Util.drop (abs d) bitlist
  )

let bitlist_to_string bitlist = List.map Sail2_values.bitU_char bitlist |> List.to_seq |> String.of_seq

let parse_json_string_to_bits ~at:l ~len str =
  let open Util.Option_monad in
  let open Sail2_operators_bitlists in
  let str_len = String.length str in
  let chars = str |> String.to_seq |> List.of_seq in
  let* bitlist =
    if str_len > 2 && String.sub str 0 2 = "0b" then
      let* bin_chars = Util.drop 2 chars |> List.filter_map valid_bin_char |> Util.option_all in
      Some (List.map bin_char_to_bit bin_chars |> fix_length ~at:l ~len)
    else if str_len > 2 && String.sub str 0 2 = "0x" then
      let* hex_chars = Util.drop 2 chars |> List.filter_map valid_hex_char |> Util.option_all in
      Some (List.map hex_char_to_bits hex_chars |> List.concat |> fix_length ~at:l ~len)
    else
      let* dec_chars = List.filter_map valid_dec_char chars |> Util.option_all in
      let n = List.to_seq dec_chars |> String.of_seq |> Big_int.of_string in
      Some (get_slice_int (Big_int.of_int len) n Big_int.zero)
  in
  Some (mk_lit_exp ~loc:l (L_bin (bitlist_to_string bitlist)))

let parse_json_string_to_abstract_bits ~at:l ~len str =
  let open Util.Option_monad in
  let open Sail2_operators_bitlists in
  let str_len = String.length str in
  let chars = str |> String.to_seq |> List.of_seq in
  let mask bitlist =
    mk_exp (E_app (mk_id "sail_mask", [mk_exp (E_sizeof (nid len)); mk_lit_exp (L_bin (bitlist_to_string bitlist))]))
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
    let* bin_chars = Util.drop 2 chars |> List.filter_map valid_bin_char |> Util.option_all in
    Some (List.map bin_char_to_bit bin_chars |> mask)
  else if str_len > 2 && String.sub str 0 2 = "0x" then
    let* hex_chars = Util.drop 2 chars |> List.filter_map valid_hex_char |> Util.option_all in
    Some (List.map hex_char_to_bits hex_chars |> List.concat |> mask)
  else
    let* dec_chars = List.filter_map valid_dec_char chars |> Util.option_all in
    let n = List.to_seq dec_chars |> String.of_seq |> Big_int.of_string in
    Some (slice_int n)

let rec sail_exp_from_json ~at:l env typ =
  let open Util.Option_monad in
  function
  | `Int n -> mk_lit_exp ~loc:l (L_num (Big_int.of_int n))
  | `Intlit n -> mk_lit_exp ~loc:l (L_num (Big_int.of_string n))
  | `String s ->
      if Option.is_some (Type_check.destruct_numeric typ) then mk_lit_exp ~loc:l (L_num (Big_int.of_string s))
      else if typ_is_enum env typ then mk_exp ~loc:l (E_id (mk_id ~loc:l s))
      else mk_lit_exp ~loc:l (L_string s)
  | `Bool true -> (
      match typ with
      | Typ_aux (Typ_id id, _) when string_of_id id = "bit" -> mk_lit_exp ~loc:l L_one
      | _ -> mk_lit_exp ~loc:l L_true
    )
  | `Bool false -> (
      match typ with
      | Typ_aux (Typ_id id, _) when string_of_id id = "bit" -> mk_lit_exp ~loc:l L_zero
      | _ -> mk_lit_exp ~loc:l L_false
    )
  | `Null -> mk_lit_exp ~loc:l L_unit
  | `List jsons -> (
      let base_typ = match destruct_exist typ with None -> typ | Some (_, _, typ) -> typ in
      match base_typ with
      | Typ_aux (Typ_app (id, args), _) -> (
          match (string_of_id id, args) with
          | "bitvector", _ ->
              L_bin (List.map (json_bit ~at:l) jsons |> List.to_seq |> String.of_seq) |> mk_lit_exp ~loc:l
          | "vector", [_; A_aux (A_typ item_typ, _)] ->
              let items = List.map (sail_exp_from_json ~at:l env item_typ) jsons in
              mk_exp ~loc:l (E_vector items)
          | "list", [A_aux (A_typ item_typ, _)] ->
              let items = List.map (sail_exp_from_json ~at:l env item_typ) jsons in
              mk_exp ~loc:l (E_list items)
          | _ -> raise (Reporting.err_general l ("Failed to interpret JSON list as Sail type " ^ string_of_typ typ))
        )
      | _ -> raise (Reporting.err_general l ("Failed to interpret JSON list as Sail type " ^ string_of_typ typ))
    )
  | `Assoc obj -> (
      let base_typ = match destruct_exist typ with None -> typ | Some (_, _, typ) -> typ in
      let exp_opt =
        if typ_is_record env base_typ then
          let* id, _ = destruct_typ_args base_typ in
          let _, fields = Env.get_record id env in
          let* fexps =
            List.map
              (fun (field_typ, field_id) ->
                let* field_json = List.assoc_opt (string_of_id field_id) obj in
                let exp = sail_exp_from_json ~at:l env field_typ field_json in
                Some (mk_fexp ~loc:l field_id exp)
              )
              fields
            |> Util.option_all
          in
          Some (mk_exp ~loc:l (E_struct fexps))
        else if typ_is_variant env base_typ then
          let* id, _ = destruct_typ_args base_typ in
          match obj with
          | [(constructor, value)] -> (
              let constructor = mk_id ~loc:l constructor in
              match Env.union_constructor_info constructor env with
              | None ->
                  raise
                    (Reporting.err_general l
                       (Printf.sprintf "Constructor %s in JSON configuration is not a valid constructor for union %s"
                          (string_of_id constructor) (string_of_id id)
                       )
                    )
              | Some (_, _, _, Tu_aux (Tu_ty_id (typ, _), _)) ->
                  let exp = sail_exp_from_json ~at:l env typ value in
                  Some (mk_exp ~loc:l (E_app (constructor, [exp])))
            )
          | _ ->
              raise
                (Reporting.err_general l
                   (Printf.sprintf "JSON does not appear to contain a valid Sail union member for %s" (string_of_id id))
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
                  | `String len -> parse_json_string_to_abstract_bits ~at:l ~len:(mk_id len) value
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
  | _ -> assert false

let rewrite_exp global_env env_update types json (aux, annot) =
  match aux with
  | E_config parts -> (
      let env = env_of_annot annot in
      let typ = typ_of_annot annot in
      ConfigTypes.insert parts { loc = fst annot; env; typ } types;
      match find_json ~at:(fst annot) parts json with
      | None -> E_aux (aux, annot)
      | Some json -> (
          try
            let exp = sail_exp_from_json ~at:(fst annot) global_env typ json in
            Type_check.check_exp (env_update (env_of_annot annot)) exp typ
          with Type_error.Type_error (l, err) -> raise (Type_error.to_reporting_exn l err)
        )
    )
  | _ -> E_aux (aux, annot)

let rec abstract_schema config_ids types = function
  | DEF_aux (DEF_constraint nc, def_annot) :: defs ->
      let nc_ids = ids_of_constraint nc in
      Bindings.iter
        (fun id (_, json_key) -> if IdSet.mem id nc_ids then ConfigTypes.insert_abstract_constraint json_key nc types)
        config_ids;
      abstract_schema config_ids types defs
  | def :: defs -> abstract_schema config_ids types defs
  | [] -> ()

let rewrite_ast global_env instantiation json ast =
  let open Frontend in
  let types = ConfigTypes.create () in
  Bindings.iter
    (fun id (kind_aux, json_key) -> ConfigTypes.insert_abstract json_key id kind_aux types)
    instantiation.config_ids;
  abstract_schema instantiation.config_ids types ast.defs;
  let alg = { id_exp_alg with e_aux = rewrite_exp global_env instantiation.env_update types json } in
  let ast = rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) } ast in
  let schema = ConfigTypes.to_schema types in
  (schema, ast)
