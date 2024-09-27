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
open Ast_util
open Rewriter
open Type_check

module J = Yojson.Safe
module StringMap = Util.StringMap

module ConfigTypes : sig
  type t

  val create : unit -> t

  val find_opt : at:Ast.l -> string list -> t -> (Ast.l * typ) option

  val update_type : string list -> Ast.l -> typ -> t -> bool

  val insert : string list -> Ast.l -> typ -> t -> unit
end = struct
  open Util.Option_monad
  open Error_format

  type t = Sail_value of { mutable loc : Ast.l; mutable typ : typ } | Object of (string, t) Hashtbl.t

  (* Random is false here for deterministic error messages *)
  let create () = Object (Hashtbl.create ~random:false 16)

  let rec get_example = function
    | Sail_value { loc; typ } -> Some (loc, typ)
    | Object tbl -> Hashtbl.fold (fun _ value acc -> if Option.is_none acc then get_example value else acc) tbl None

  let find_opt ~at:l full_parts map =
    let rec go parts map =
      match (parts, map) with
      | part :: parts, Object tbl ->
          let* map = Hashtbl.find_opt tbl part in
          go parts map
      | part :: _, Sail_value { loc; typ } ->
          let msg =
            Seq
              [
                Line
                  (Printf.sprintf
                     "Attempting to access key %s from configuration that has already been interpreted as type %s" part
                     (string_of_typ typ)
                  );
                Location ("", Some "interpreted here", loc, Seq []);
              ]
          in
          let b = Buffer.create 1024 in
          format_message msg (buffer_formatter b);
          raise (Reporting.err_typ l (Buffer.contents b))
      | [], Sail_value { loc; typ } -> Some (loc, typ)
      | [], obj ->
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
    in
    go full_parts map

  let rec insert parts l typ map =
    match (parts, map) with
    | [part], Object tbl -> Hashtbl.replace tbl part (Sail_value { loc = l; typ })
    | part :: parts, Object tbl -> (
        match Hashtbl.find_opt tbl part with
        | Some map -> insert parts l typ map
        | None ->
            Hashtbl.add tbl part (create ());
            insert (part :: parts) l typ map
      )
    | _ -> Reporting.unreachable l __POS__ "Failed to insert into config type map"

  let rec update_type parts l typ map =
    match (parts, map) with
    | part :: parts, Object tbl -> (
        match Hashtbl.find_opt tbl part with Some map -> update_type parts l typ map | None -> false
      )
    | [], Sail_value v ->
        v.loc <- l;
        v.typ <- typ;
        true
    | _ -> false
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

let sail_exp_from_json ~at:l env typ = function
  | `Int n -> mk_lit_exp ~loc:l (L_num (Big_int.of_int n))
  | `Intlit n -> mk_lit_exp ~loc:l (L_num (Big_int.of_string n))
  | `String s ->
      if Option.is_some (Type_check.destruct_numeric typ) then mk_lit_exp ~loc:l (L_num (Big_int.of_string s))
      else mk_lit_exp ~loc:l (L_string s)
  | `List jsons when Option.is_some (Type_check.destruct_bitvector env typ) ->
      L_bin (List.map (json_bit ~at:l) jsons |> List.to_seq |> String.of_seq) |> mk_lit_exp ~loc:l
  | _ -> assert false

let rewrite_exp global_env types json (aux, annot) =
  match aux with
  | E_config parts -> (
      let typ = typ_of_annot annot in
      let typ =
        match ConfigTypes.find_opt ~at:(fst annot) parts types with
        | Some (prev_l, prev_typ) ->
            if subtype_check global_env prev_typ typ then prev_typ
            else if subtype_check global_env typ prev_typ then (
              let (_ : bool) = ConfigTypes.update_type parts (fst annot) typ types in
              typ
            )
            else
              let open Error_format in
              let msg =
                Seq
                  [
                    Line "Incompatible types for configuration option found:";
                    List
                      [
                        ("Type " ^ string_of_typ typ ^ " found here", Seq []);
                        ("Type " ^ string_of_typ prev_typ ^ " found as previous type", Seq []);
                      ];
                    Line "";
                    Location ("", Some "previous type found here", prev_l, Seq []);
                  ]
              in
              let b = Buffer.create 1024 in
              format_message msg (buffer_formatter b);
              raise (Reporting.err_typ (fst annot) (Buffer.contents b))
        | None ->
            ConfigTypes.insert parts (fst annot) typ types;
            typ
      in
      match find_json ~at:(fst annot) parts json with
      | None -> E_aux (aux, annot)
      | Some json -> (
          try
            let exp = sail_exp_from_json ~at:(fst annot) global_env typ json in
            Type_check.check_exp (env_of_annot annot) exp typ
          with Type_error.Type_error (l, err) -> raise (Type_error.to_reporting_exn l err)
        )
    )
  | _ -> E_aux (aux, annot)

let rewrite_ast global_env json ast =
  let types = ConfigTypes.create () in
  let alg = { id_exp_alg with e_aux = rewrite_exp global_env types json } in
  rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) } ast
