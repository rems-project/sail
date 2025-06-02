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
(*    Louis-Emile Ploix                                                     *)
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

open Ast_util
open Parse_ast.Attribute_data

module StringSet = Util.StringSet

let sv_type_of_string = Initial_check.parse_from_string (Sv_type_parser.sv_type Sv_type_lexer.token)

let parse_sv_type = function
  | AD_aux (AD_string s, l) ->
      let open Lexing in
      let p =
        match Reporting.simp_loc l with Some (p, _) -> Some { p with pos_cnum = p.pos_cnum + 1 } | None -> None
      in
      let num_opt, ctyp = sv_type_of_string ?inline:p s in
      (l, num_opt, ctyp)
  | AD_aux (_, l) -> raise (Reporting.err_general l "Cannot parse systemverilog type from attribute")

module type ATTRIBUTE_INFO = sig
  val loc : Ast.l
  val attribute_name : string
end

module NullAttributeInfo : ATTRIBUTE_INFO = struct
  let loc = Parse_ast.Unknown
  let attribute_name = "unknown"
end

let get_sv_attribute_from ~getter name annot =
  match getter name annot with
  | Some (l, attr_data_opt) -> (
      let module Info = struct
        let loc = l
        let attribute_name = name
      end in
      match attr_data_opt with
      | None -> (Some [], (module Info : ATTRIBUTE_INFO))
      | Some attr_data -> (
          match attribute_data_object attr_data with
          | Some obj -> (Some obj, (module Info : ATTRIBUTE_INFO))
          | None -> raise (Reporting.err_general l ("Expected key-value pairs on " ^ name ^ " attribute"))
        )
    )
  | None -> (None, (module NullAttributeInfo))

let get_sv_attribute name uannot = get_sv_attribute_from ~getter:get_attribute name uannot
let get_sv_def_attribute name def_annot = get_sv_attribute_from ~getter:get_def_attribute name def_annot

module AttributeParser (Info : ATTRIBUTE_INFO) = struct
  open Util.Option_monad

  let key_type_error ~expected key l =
    Reporting.err_general
      (Hint ("key here", l, Info.loc))
      (Printf.sprintf "Expected %s type for %s in %s attribute" expected key Info.attribute_name)

  let get_bool ~default key obj_opt =
    match obj_opt with
    | None -> default
    | Some obj -> (
        match List.assoc_opt key obj with
        | None -> default
        | Some (AD_aux (AD_bool b, _)) -> b
        | Some (AD_aux (_, l)) -> raise (key_type_error ~expected:"boolean" key l)
      )

  let get_string ~default key obj_opt =
    match obj_opt with
    | None -> default
    | Some obj -> (
        match List.assoc_opt key obj with
        | None -> default
        | Some (AD_aux (AD_string s, _)) -> s
        | Some (AD_aux (_, l)) -> raise (key_type_error ~expected:"string" key l)
      )

  let get_types ~arity obj_opt =
    let* types = Option.bind obj_opt (List.assoc_opt "types") in
    let ctyps =
      match types with
      | AD_aux (AD_string _, _) as s -> [parse_sv_type s]
      | AD_aux (AD_list types, _) -> List.map parse_sv_type types
      | _ -> raise (Reporting.err_general Info.loc "types field must be either a string, or an array of strings")
    in
    if List.for_all (fun (_, num_opt, _) -> Option.is_some num_opt) ctyps then
      Some
        (List.init arity (fun n ->
             let* _, _, ctyp = List.find_opt (fun (_, num_opt, _) -> Option.get num_opt = n) ctyps in
             Some ctyp
         )
        )
    else if List.for_all (fun (_, num_opt, _) -> Option.is_none num_opt) ctyps then
      if List.length ctyps <> arity then
        raise
          (Reporting.err_general Info.loc
             "Number of items of types key must match number of function arguments, unless argument positions are \
              explicit"
          )
      else Some (List.map (fun (_, _, ctyp) -> Some ctyp) ctyps)
    else (
      let l1, _, _ = List.find (fun (_, num_opt, _) -> Option.is_some num_opt) ctyps in
      let l2, _, _ = List.find (fun (_, num_opt, _) -> Option.is_none num_opt) ctyps in
      raise
        (Reporting.err_general
           (Hint ("Non-positional type specified here", l2, l1))
           "Mixed use of types with specified positions and non-specified positions"
        )
    )

  let get_return_type obj_opt =
    let* return_type = Option.bind obj_opt (List.assoc_opt "return_type") in
    let l, num_opt, ctyp =
      match return_type with
      | AD_aux (AD_string _, _) as s -> parse_sv_type s
      | AD_aux (_, l) -> raise (Reporting.err_general l "return_type field must be a string")
    in
    match num_opt with
    | None -> Some ctyp
    | Some _ -> raise (Reporting.err_general l "return_type field should not have positional argument")

  let get_string_set ~default key obj_opt =
    let add_to_set set = function
      | AD_aux (AD_string s, _) -> StringSet.add s set
      | AD_aux (_, l) -> raise (key_type_error ~expected:"string" key l)
    in
    match obj_opt with
    | None -> default
    | Some obj -> (
        match List.assoc_opt key obj with
        | None -> default
        | Some (AD_aux (AD_list xs, _)) -> List.fold_left add_to_set StringSet.empty xs
        | Some (AD_aux (_, l)) -> raise (key_type_error ~expected:"boolean" key l)
      )

  let get_dpi sets obj_opt =
    let* dpi = Option.bind obj_opt (List.assoc_opt "dpi") in
    match dpi with
    | AD_aux (AD_bool b, _) -> Some b
    | AD_aux (AD_string s, _) -> Some (StringSet.mem s sets)
    | AD_aux (_, l) -> raise (Reporting.err_general l "dpi field must be a boolean or string")
end

let get_bool_attribute name attr_object =
  let open Parse_ast.Attribute_data in
  match List.assoc_opt name attr_object with
  | Some (AD_aux (AD_bool true, _)) -> true
  | Some (AD_aux (AD_bool false, _)) | None -> false
  | Some (AD_aux (_, l)) ->
      raise (Reporting.err_general l (Printf.sprintf "Expected boolean for %s key on sv_module attribute" name))

let check_attribute name attr_object f =
  let open Parse_ast.Attribute_data in
  match List.assoc_opt name attr_object with
  | Some (AD_aux (AD_bool true, _)) -> f ()
  | Some (AD_aux (AD_bool false, _)) | None -> ()
  | Some (AD_aux (_, l)) ->
      raise (Reporting.err_general l (Printf.sprintf "Expected boolean for %s key on sv_module attribute" name))
