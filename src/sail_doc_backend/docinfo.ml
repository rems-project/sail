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

(** This module defines types representing the documentation info (docinfo) associated with Sail ASTs. Additionally we
    define functions for converting these types into a language-neutral json representation. *)

open Libsail

open Ast
open Ast_defs
open Ast_util
open Parse_ast.Attribute_data

open Coq_def_annot

module Reformatter = Pretty_print_sail.Printer (struct
  let insert_braces = true
  let resugar = true
  let hide_attributes = true
end)

module Document = Pretty_print_sail.Document

(** In the case of latex, we generate files containing a sequence of commands that can simply be included. For other
    documentation targets with tooling that may consume the json output however, we define a version number that allows
    checking the generated version info with what the external tooling supports. *)
let docinfo_version = 1

let same_file f1 f2 = Filename.basename f1 = Filename.basename f2 && Filename.dirname f1 = Filename.dirname f2

let process_file f filename = f (Util.read_whole_file filename)

let hash_file filename = process_file Digest.string filename |> Digest.to_hex

type embedding = Plain | Base64

let embedding_string = function Plain -> "plain" | Base64 -> "base64"

let get_module_path env =
  let project_opt = Type_check.Env.get_modules env in
  let mod_id = Type_check.Env.get_current_module env in
  match project_opt with
  | Some project when Project.valid_module_id project mod_id ->
      let parents = Project.get_parents mod_id project in
      Some (List.map (fun id -> fst (Project.module_name project id)) (parents @ [mod_id]))
  | _ -> None

let json_of_bindings b f =
  Bindings.bindings b |> List.map (fun (key, elem) -> (string_of_id key, f elem)) |> fun elements -> `Assoc elements

type location_or_raw =
  | Raw of string
  | RawWithLocation of string * string * int * int * int * int * int * int
  | Location of string * int * int * int * int * int * int

let json_of_location_or_raw = function
  | Raw s -> `String s
  | RawWithLocation (s, fname, line1, bol1, char1, line2, bol2, char2) ->
      `Assoc
        [
          ("contents", `String s);
          ("file", `String fname);
          ("loc", `List [`Int line1; `Int bol1; `Int char1; `Int line2; `Int bol2; `Int char2]);
        ]
  | Location (fname, line1, bol1, char1, line2, bol2, char2) ->
      `Assoc
        [("file", `String fname); ("loc", `List [`Int line1; `Int bol1; `Int char1; `Int line2; `Int bol2; `Int char2])]

type hyper_location = string * int * int

let included_loc files l =
  match Reporting.loc_file l with
  | Some file -> Util.list_empty files || List.exists (same_file file) files
  | None -> Util.list_empty files

let hyper_loc l =
  match Reporting.simp_loc l with
  | Some (p1, p2) when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname ->
      Some (p1.pos_fname, p1.pos_cnum, p2.pos_cnum)
  | _ -> None

type hyperlink = Function of id * hyper_location | Register of id * hyper_location

let hyperlink_target = function Function (id, _) -> Callgraph.Function id | Register (id, _) -> Callgraph.Register id

let hyperlink_span = function Function (_, l) -> l | Register (_, l) -> l

let json_of_hyperlink = function
  | Function (id, (file, c1, c2)) ->
      `Assoc
        [
          ("type", `String "function");
          ("id", `String (string_of_id id));
          ("file", `String file);
          ("loc", `List [`Int c1; `Int c2]);
        ]
  | Register (id, (file, c1, c2)) ->
      `Assoc
        [
          ("type", `String "register");
          ("id", `String (string_of_id id));
          ("file", `String file);
          ("loc", `List [`Int c1; `Int c2]);
        ]

let json_of_comment (comment : Parse_ast.doc_comment option) =
  match comment with Some { contents; _ } -> [("comment", `String contents)] | None -> []

let hyperlinks_from_def files def =
  let open Rewriter in
  let links = ref [] in

  let link f l =
    if included_loc files l then (match hyper_loc l with Some hloc -> links := f hloc :: !links | None -> ())
  in

  let scan_lexp lexp_aux annot =
    let env = Type_check.env_of_annot annot in
    begin
      match lexp_aux with
      | LE_typ (_, id) | LE_id id -> begin
          match Type_check.Env.lookup_id id env with
          | Register _ -> link (fun hloc -> Register (id, hloc)) (id_loc id)
          | _ -> ()
        end
      | _ -> ()
    end;
    LE_aux (lexp_aux, annot)
  in

  let scan_exp e_aux annot =
    let env = Type_check.env_of_annot annot in
    begin
      match e_aux with
      | E_id id -> begin
          match Type_check.Env.lookup_id id env with
          | Register _ -> link (fun hloc -> Register (id, hloc)) (id_loc id)
          | _ -> ()
        end
      | E_app (f, _) -> link (fun hloc -> Function (f, hloc)) (id_loc f)
      | _ -> ()
    end;
    E_aux (e_aux, annot)
  in

  let rw_exp _ exp =
    fold_exp
      {
        id_exp_alg with
        e_aux = (fun (e_aux, annot) -> scan_exp e_aux annot);
        le_aux = (fun (l_aux, annot) -> scan_lexp l_aux annot);
      }
      exp
  in
  ignore (rewrite_ast_defs { rewriters_base with rewrite_exp = rw_exp } [def]);

  !links

let json_of_attributes = function
  | [] -> []
  | attrs -> [("attributes", `List (List.map (fun (attr, data) -> json_of_attribute attr data) attrs))]

let rec json_of_pat (P_aux (aux, _)) =
  let pat_type t = ("type", `String t) in
  let seq_pat_json t pats = `Assoc [pat_type t; ("patterns", `List (List.map json_of_pat pats))] in
  match aux with
  | P_lit lit -> `Assoc [pat_type "literal"; ("value", `String (string_of_lit lit))]
  | P_wild -> `Assoc [pat_type "wildcard"]
  | P_as (pat, id) -> `Assoc [pat_type "as"; ("pattern", json_of_pat pat); ("id", `String (string_of_id id))]
  | P_typ (_, pat) -> json_of_pat pat
  | P_id id -> `Assoc [pat_type "id"; ("id", `String (string_of_id id))]
  | P_var (pat, _) -> `Assoc [pat_type "var"; ("pattern", json_of_pat pat)]
  | P_app (id, pats) ->
      `Assoc [pat_type "app"; ("id", `String (string_of_id id)); ("patterns", `List (List.map json_of_pat pats))]
  | P_vector pats -> seq_pat_json "vector" pats
  | P_vector_concat pats -> seq_pat_json "vector_concat" pats
  | P_vector_subrange (id, n, m) ->
      `Assoc
        [
          pat_type "vector_subrange";
          ("id", `String (string_of_id id));
          ("from", `Int (Big_int.to_int n));
          ("to", `Int (Big_int.to_int m));
        ]
  | P_tuple pats -> seq_pat_json "tuple" pats
  | P_list pats -> seq_pat_json "list" pats
  | P_cons (pat_hd, pat_tl) -> `Assoc [pat_type "cons"; ("hd", json_of_pat pat_hd); ("tl", json_of_pat pat_tl)]
  | P_string_append pats -> seq_pat_json "string_append" pats
  | P_struct (_, fpats, fwild) ->
      `Assoc
        [
          pat_type "struct";
          ("fields", `Assoc (List.map (fun (field, pat) -> (string_of_id field, json_of_pat pat)) fpats));
          ("wildcard", `Bool (match fwild with FP_wild _ -> true | FP_no_wild -> false));
        ]
  | P_or _ | P_not _ -> `Null

type 'a function_clause_doc = {
  number : int;
  source : location_or_raw;
  pat : 'a pat;
  wavedrom : string option;
  guard_source : location_or_raw option;
  body_source : location_or_raw;
  module_path : string list option;
  comment : Parse_ast.doc_comment option;
  splits : location_or_raw Bindings.t option;
  attributes : (string * attribute_data option) list;
}

let json_of_function_clause_doc docinfo =
  `Assoc
    ([
       ("number", `Int docinfo.number);
       ("source", json_of_location_or_raw docinfo.source);
       ("pattern", json_of_pat docinfo.pat);
     ]
    @ (match docinfo.wavedrom with Some w -> [("wavedrom", `String w)] | None -> [])
    @ (match docinfo.guard_source with Some s -> [("guard", json_of_location_or_raw s)] | None -> [])
    @ [("body", json_of_location_or_raw docinfo.body_source)]
    @ (match docinfo.module_path with Some mods -> [("path", `List (List.map (fun m -> `String m) mods))] | None -> [])
    @ (match docinfo.splits with Some s -> [("splits", json_of_bindings s json_of_location_or_raw)] | None -> [])
    @ json_of_comment docinfo.comment @ json_of_attributes docinfo.attributes
    )

type 'a function_doc = Multiple_clauses of 'a function_clause_doc list | Single_clause of 'a function_clause_doc

let json_of_function_doc = function
  | Multiple_clauses docinfos -> `List (List.map json_of_function_clause_doc docinfos)
  | Single_clause docinfo -> json_of_function_clause_doc docinfo

type 'a mapping_clause_doc = {
  number : int;
  source : location_or_raw;
  left : 'a pat option;
  left_wavedrom : string option;
  right : 'a pat option;
  right_wavedrom : string option;
  body : location_or_raw option;
  comment : Parse_ast.doc_comment option;
  attributes : (string * attribute_data option) list;
}

let json_of_mapping_clause_doc docinfo =
  `Assoc
    ([("number", `Int docinfo.number); ("source", json_of_location_or_raw docinfo.source)]
    @ (match docinfo.left with Some p -> [("left", json_of_pat p)] | None -> [])
    @ (match docinfo.left_wavedrom with Some w -> [("left_wavedrom", `String w)] | None -> [])
    @ (match docinfo.right with Some p -> [("right", json_of_pat p)] | None -> [])
    @ (match docinfo.right_wavedrom with Some w -> [("right_wavedrom", `String w)] | None -> [])
    @ (match docinfo.body with Some s -> [("body", json_of_location_or_raw s)] | None -> [])
    @ json_of_comment docinfo.comment @ json_of_attributes docinfo.attributes
    )

type 'a mapping_doc = 'a mapping_clause_doc list

let json_of_mapping_doc docinfos = `List (List.map json_of_mapping_clause_doc docinfos)

type valspec_doc = {
  source : location_or_raw;
  type_source : location_or_raw;
  comment : Parse_ast.doc_comment option;
  attributes : (string * attribute_data option) list;
}

let json_of_valspec_doc docinfo =
  `Assoc
    ([("source", json_of_location_or_raw docinfo.source); ("type", json_of_location_or_raw docinfo.type_source)]
    @ json_of_comment docinfo.comment @ json_of_attributes docinfo.attributes
    )

type type_def_doc = location_or_raw

let json_of_type_def_doc = json_of_location_or_raw

type register_doc = {
  source : location_or_raw;
  type_source : location_or_raw;
  exp_source : location_or_raw option;
  comment : Parse_ast.doc_comment option;
  attributes : (string * attribute_data option) list;
}

let json_of_register_doc docinfo =
  `Assoc
    ([("source", json_of_location_or_raw docinfo.source); ("type", json_of_location_or_raw docinfo.type_source)]
    @ (match docinfo.exp_source with None -> [] | Some source -> [("exp", json_of_location_or_raw source)])
    @ json_of_comment docinfo.comment @ json_of_attributes docinfo.attributes
    )

type let_doc = {
  source : location_or_raw;
  exp_source : location_or_raw;
  comment : Parse_ast.doc_comment option;
  attributes : (string * attribute_data option) list;
}

let json_of_let_doc docinfo =
  `Assoc
    ([("source", json_of_location_or_raw docinfo.source); ("exp", json_of_location_or_raw docinfo.exp_source)]
    @ json_of_comment docinfo.comment @ json_of_attributes docinfo.attributes
    )

type anchor_doc = { source : location_or_raw; comment : Parse_ast.doc_comment option }

let json_of_anchor_doc docinfo =
  `Assoc ([("source", json_of_location_or_raw docinfo.source)] @ json_of_comment docinfo.comment)

type 'a linkable = { doc : 'a; links : hyperlink list; module_path : string list option }

let json_of_linkable x_label f linkable =
  match f linkable.doc with
  | `Null -> `Null
  | x ->
      let links =
        match linkable.links with [] -> [] | _ -> [("links", `List (List.map json_of_hyperlink linkable.links))]
      in
      let path =
        match linkable.module_path with
        | None -> []
        | Some mods -> [("path", `List (List.map (fun m -> `String m) mods))]
      in
      `Assoc ((x_label, x) :: (links @ path))

type 'a docinfo = {
  embedding : embedding;
  git : (string * bool) option;
  hashes : (string * string) list;
  functions : 'a function_doc linkable Bindings.t;
  mappings : 'a mapping_doc linkable Bindings.t;
  valspecs : valspec_doc linkable Bindings.t;
  type_defs : type_def_doc linkable Bindings.t;
  registers : register_doc linkable Bindings.t;
  lets : let_doc linkable Bindings.t;
  anchors : anchor_doc linkable Bindings.t;
  spans : location_or_raw Bindings.t;
}

let json_of_span loc = `Assoc [("span", json_of_location_or_raw loc)]

let json_of_docinfo docinfo =
  let assoc =
    [("version", `Int docinfo_version)]
    @ ( match docinfo.git with
      | Some (commit, dirty) -> [("git", `Assoc [("commit", `String commit); ("dirty", `Bool dirty)])]
      | None -> []
      )
    @ [
        ("embedding", `String (embedding_string docinfo.embedding));
        ("hashes", `Assoc (List.map (fun (key, hash) -> (key, `Assoc [("md5", `String hash)])) docinfo.hashes));
        ("functions", json_of_bindings docinfo.functions (json_of_linkable "function" json_of_function_doc));
        ("mappings", json_of_bindings docinfo.mappings (json_of_linkable "mapping" json_of_mapping_doc));
        ("vals", json_of_bindings docinfo.valspecs (json_of_linkable "val" json_of_valspec_doc));
        ("types", json_of_bindings docinfo.type_defs (json_of_linkable "type" json_of_type_def_doc));
        ("registers", json_of_bindings docinfo.registers (json_of_linkable "register" json_of_register_doc));
        ("lets", json_of_bindings docinfo.lets (json_of_linkable "let" json_of_let_doc));
        ("anchors", json_of_bindings docinfo.anchors (json_of_linkable "anchor" json_of_anchor_doc));
        ("spans", json_of_bindings docinfo.spans json_of_span);
      ]
  in
  `Assoc assoc

let git_command args =
  try
    let git_out, git_in, git_err = Unix.open_process_full ("git " ^ args) (Unix.environment ()) in
    let res = input_line git_out in
    match Unix.close_process_full (git_out, git_in, git_err) with Unix.WEXITED 0 -> Some res | _ -> None
  with _ -> None

module type CONFIG = sig
  val embedding_mode : embedding option
  val embed_with_location : bool
end

module Generator (Converter : Markdown.CONVERTER) (Config : CONFIG) = struct
  let encode str = match Config.embedding_mode with Some Plain | None -> str | Some Base64 -> Base64.encode_string str

  let embedding_format () = match Config.embedding_mode with Some Plain | None -> Plain | Some Base64 -> Base64

  let doc_lexing_pos (p1 : Lexing.position) (p2 : Lexing.position) =
    match Config.embedding_mode with
    | Some _ when Config.embed_with_location ->
        RawWithLocation
          ( Reporting.loc_range_to_src p1 p2 |> encode,
            p1.pos_fname,
            p1.pos_lnum,
            p1.pos_bol,
            p1.pos_cnum,
            p2.pos_lnum,
            p2.pos_bol,
            p2.pos_cnum
          )
    | Some _ -> Raw (Reporting.loc_range_to_src p1 p2 |> encode)
    | None -> Location (p1.pos_fname, p1.pos_lnum, p1.pos_bol, p1.pos_cnum, p2.pos_lnum, p2.pos_bol, p2.pos_cnum)

  let doc_loc l g f x =
    match Reporting.simp_loc l with
    | Some (p1, p2)
      when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname && Sys.file_exists p1.pos_fname ->
        doc_lexing_pos p1 p2
    | _ -> Raw (g x |> f |> Document.to_string |> encode)

  let get_doc_comment def_annot =
    Option.map
      (fun ({ contents; comment_type } : Parse_ast.doc_comment) ->
        let conf = Converter.default_config ~loc:def_annot.loc in
        ({ contents = encode (Converter.convert conf contents); comment_type } : Parse_ast.doc_comment)
      )
      def_annot.doc_comment

  let docinfo_for_valspec def_annot (VS_aux (VS_val_spec ((TypSchm_aux (_, ts_l) as ts), _, _), vs_annot) as vs) =
    {
      source = doc_loc (fst vs_annot) Type_check.strip_val_spec Reformatter.doc_spec vs;
      type_source = doc_loc ts_l (fun ts -> ts) Reformatter.doc_typschm ts;
      comment = get_doc_comment def_annot;
      attributes = List.map (fun (_, attr_info) -> attr_info) def_annot.attrs;
    }

  let docinfo_for_type_def (TD_aux (_, annot) as td) =
    doc_loc (fst annot) Type_check.strip_typedef Reformatter.doc_type_def td

  let docinfo_for_register def_annot (DEC_aux (DEC_reg ((Typ_aux (_, typ_l) as typ), _, exp), rd_annot) as rd) =
    {
      source = doc_loc (fst rd_annot) Type_check.strip_register Reformatter.doc_register rd;
      type_source = doc_loc typ_l (fun typ -> typ) Reformatter.doc_typ typ;
      exp_source =
        Option.map (fun (E_aux (_, (l, _)) as exp) -> doc_loc l Type_check.strip_exp Reformatter.doc_exp exp) exp;
      comment = get_doc_comment def_annot;
      attributes = List.map (fun (_, attr_info) -> attr_info) def_annot.attrs;
    }

  let docinfo_for_let def_annot (LB_aux (LB_val (_, exp), annot) as lbind) =
    {
      source = doc_loc (fst annot) Type_check.strip_letbind Reformatter.doc_letbind lbind;
      exp_source = doc_loc (exp_loc exp) Type_check.strip_exp Reformatter.doc_exp exp;
      comment = get_doc_comment def_annot;
      attributes = List.map (fun (_, attr_info) -> attr_info) def_annot.attrs;
    }

  let funcl_splits ~ast ~error_loc:l attrs exp =
    (* The constant propagation tends to strip away block formatting, so put it back to make the pretty_printed output a bit nicer. *)
    let pretty_printer =
      match exp with
      | E_aux (E_block _, _) -> fun exp -> Reformatter.doc_block [exp]
      | _ -> fun exp -> Reformatter.doc_exp exp
    in
    match find_attribute_opt "split" attrs with
    | None -> None
    | Some (_, Some (AD_aux (AD_string split_id, _))) -> (
        let split_id = mk_id split_id in
        let env = Type_check.env_of exp in
        match Type_check.Env.lookup_id split_id env with
        | Local (_, (Typ_aux (Typ_id enum_id, _) as enum_typ)) ->
            let members = Type_check.Env.get_enum enum_id env in
            let splits =
              List.fold_left
                (fun splits member ->
                  let checked_member = Type_check.check_exp env (mk_exp (E_id member)) enum_typ in
                  let substs = (Bindings.singleton split_id checked_member, KBindings.empty) in
                  let propagated, _ =
                    Constant_propagation.const_prop "doc" env ast IdSet.empty substs Bindings.empty exp
                  in
                  let propagated_doc =
                    Raw (pretty_printer (Type_check.strip_exp propagated) |> Document.to_string |> encode)
                  in
                  Bindings.add member propagated_doc splits
                )
                Bindings.empty members
            in
            Some splits
        | _ -> raise (Reporting.err_general l ("Could not split on variable " ^ string_of_id split_id))
      )
    | Some _ -> raise (Reporting.err_general l "Invalid argument for split attribute")

  let docinfo_for_funcl ~ast ?outer_annot n (FCL_aux (FCL_funcl (_, pexp), annot) as clause) =
    (* If we have just a single clause, we use the annotation for the
       outer FD_aux wrapper, except we prefer documentation comments
       attached to the inner function clause type where available. *)
    let comment = get_doc_comment (fst annot) in
    let annot = match outer_annot with None -> annot | Some annot -> annot in
    let comment = match comment with None -> get_doc_comment (fst annot) | comment -> comment in

    (* Try to use the inner attributes if we have no outer attributes. *)
    let attrs = get_def_attributes @@ fst @@ match outer_annot with None -> annot | Some outer -> outer in

    let source = doc_loc (fst annot).loc Type_check.strip_funcl Reformatter.doc_funcl clause in
    let pat, guard, exp =
      match pexp with
      | Pat_aux (Pat_exp (pat, exp), _) -> (pat, None, exp)
      | Pat_aux (Pat_when (pat, guard, exp), _) -> (pat, Some guard, exp)
    in
    let guard_source =
      Option.map (fun exp -> doc_loc (exp_loc exp) Type_check.strip_exp Reformatter.doc_exp exp) guard
    in
    let body_source =
      match exp with
      | E_aux (E_block (exp :: exps), (block_loc, _)) -> (
          let first_loc = exp_loc exp in
          let last_loc = exp_loc (Util.last (exp :: exps)) in
          match (Reporting.simp_loc first_loc, Reporting.simp_loc last_loc, Reporting.simp_loc block_loc) with
          | Some (p1, _), Some (_, p2), Some (block_p1, block_p2)
            when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname ->
              if block_p1.pos_lnum < p1.pos_lnum then
                (* Make sure the first line is indented correctly, when it's on a different line to the start of the block. *)
                doc_lexing_pos { p1 with pos_cnum = p1.pos_bol } p2
              else doc_lexing_pos block_p1 block_p2
          | _, _, _ ->
              let block = Type_check.strip_exp exp :: List.map Type_check.strip_exp exps in
              Raw (Reformatter.doc_block block |> Document.to_string |> encode)
        )
      | _ -> doc_loc (exp_loc exp) Type_check.strip_exp Reformatter.doc_exp exp
    in
    let module_path = get_module_path (Type_check.env_of exp) in

    let splits = funcl_splits ~ast ~error_loc:(pat_loc pat) attrs exp in

    {
      number = n;
      source;
      pat;
      wavedrom = Wavedrom.of_pattern ~labels:None pat |> Option.map encode;
      guard_source;
      body_source;
      module_path;
      comment;
      splits;
      attributes = List.map (fun (_, attr, data) -> (attr, data)) attrs;
    }

  let included_clause files (FCL_aux (_, (clause_annot, _))) = included_loc files clause_annot.loc

  let docinfo_for_fundef ~ast def_annot files (FD_aux (FD_function (_, _, clauses), annot)) =
    let clauses = List.filter (included_clause files) clauses in
    match clauses with
    | [] -> None
    | [clause] ->
        Some
          (Single_clause (docinfo_for_funcl ~ast ~outer_annot:(Type_check.strip_def_annot def_annot, snd annot) 0 clause)
          )
    | _ -> Some (Multiple_clauses (List.mapi (docinfo_for_funcl ~ast) clauses))

  let docinfo_for_mpexp (MPat_aux (aux, _)) =
    match aux with MPat_pat mpat -> pat_of_mpat mpat | MPat_when (mpat, _) -> pat_of_mpat mpat

  let docinfo_for_pexp (Pat_aux (aux, _)) =
    match aux with Pat_exp (pat, body) -> (pat, body) | Pat_when (pat, _, body) -> (pat, body)

  let docinfo_for_mapcl n (MCL_aux (aux, (def_annot, _)) as clause) =
    let source = doc_loc def_annot.loc Type_check.strip_mapcl Reformatter.doc_mapcl clause in
    let parse_wavedrom_attr = function _, Some (AD_aux (AD_string s, _)) -> Some s | _, Some _ | _, None -> None in
    let wavedrom_attr =
      Option.bind (find_attribute_opt "wavedrom" @@ get_def_attributes def_annot) parse_wavedrom_attr
    in

    let left, left_wavedrom, right, right_wavedrom, body =
      match aux with
      | MCL_bidir (left, right) ->
          let left = docinfo_for_mpexp left in
          let left_wavedrom = Wavedrom.of_pattern ~labels:wavedrom_attr left in
          let right = docinfo_for_mpexp right in
          let right_wavedrom = Wavedrom.of_pattern ~labels:wavedrom_attr right in
          (Some left, left_wavedrom, Some right, right_wavedrom, None)
      | MCL_forwards pexp ->
          let left, body = docinfo_for_pexp pexp in
          let left_wavedrom = Wavedrom.of_pattern ~labels:wavedrom_attr left in
          let body = doc_loc (exp_loc body) Type_check.strip_exp Reformatter.doc_exp body in
          (Some left, left_wavedrom, None, None, Some body)
      | MCL_backwards pexp ->
          let right, body = docinfo_for_pexp pexp in
          let right_wavedrom = Wavedrom.of_pattern ~labels:wavedrom_attr right in
          let body = doc_loc (exp_loc body) Type_check.strip_exp Reformatter.doc_exp body in
          (None, None, Some right, right_wavedrom, Some body)
    in

    {
      number = n;
      source;
      left;
      left_wavedrom = Option.map encode left_wavedrom;
      right;
      right_wavedrom = Option.map encode right_wavedrom;
      body;
      comment = get_doc_comment def_annot;
      attributes = List.map (fun (_, attr_info) -> attr_info) def_annot.attrs;
    }

  let included_mapping_clause files (MCL_aux (_, (def_annot, _))) = included_loc files def_annot.loc

  let docinfo_for_mapdef files (MD_aux (MD_mapping (_, _, clauses), _)) =
    let clauses = List.filter (included_mapping_clause files) clauses in
    match clauses with [] -> None | _ -> Some (List.mapi docinfo_for_mapcl clauses)

  let docinfo_for_ast ~files ~hyperlinks ast =
    let gitinfo =
      git_command "rev-parse HEAD"
      |> Option.map (fun checksum -> (checksum, Option.is_none (git_command "diff --quiet")))
    in

    let empty_docinfo =
      {
        embedding = embedding_format ();
        git = gitinfo;
        hashes = [];
        functions = Bindings.empty;
        mappings = Bindings.empty;
        valspecs = Bindings.empty;
        type_defs = Bindings.empty;
        registers = Bindings.empty;
        lets = Bindings.empty;
        anchors = Bindings.empty;
        spans = Bindings.empty;
      }
    in
    let initial_skip = match files with [] -> false | _ -> true in
    let skip_file file = if List.exists (same_file file) files then false else initial_skip in
    let skipping = function true :: _ -> true | _ -> false in
    let docinfo_for_def (docinfo, skips) (DEF_aux (aux, def_annot) as def) =
      let module_path = get_module_path def_annot.env in
      let links = hyperlinks files def in
      match aux with
      (* Maintain a stack of booleans, for each file if it was not
         specified via --doc-file, we push true to skip it. If no
         --doc-file flags are passed, include everything. *)
      | DEF_pragma (("file_start" | "include_start"), Pragma_line (path, _)) -> (docinfo, skip_file path :: skips)
      | DEF_pragma (("file_end" | "include_end"), _) -> (docinfo, match skips with _ :: skips -> skips | [] -> [])
      (* Function definiton may be scattered, so we can't skip it *)
      | DEF_fundef fdef ->
          let id = id_of_fundef fdef in
          ( begin
              match docinfo_for_fundef ~ast def_annot files fdef with
              | None -> docinfo
              | Some doc -> { docinfo with functions = Bindings.add id { doc; links; module_path } docinfo.functions }
            end,
            skips
          )
      | DEF_mapdef mdef ->
          let id = id_of_mapdef mdef in
          ( begin
              match docinfo_for_mapdef files mdef with
              | None -> docinfo
              | Some doc -> { docinfo with mappings = Bindings.add id { doc; links; module_path } docinfo.mappings }
            end,
            skips
          )
      | _ when skipping skips -> (docinfo, skips)
      | DEF_val vs ->
          let id = id_of_val_spec vs in
          ( {
              docinfo with
              valspecs = Bindings.add id { doc = docinfo_for_valspec def_annot vs; links; module_path } docinfo.valspecs;
            },
            skips
          )
      | DEF_type td ->
          let id = id_of_type_def td in
          ( {
              docinfo with
              type_defs = Bindings.add id { doc = docinfo_for_type_def td; links; module_path } docinfo.type_defs;
            },
            skips
          )
      | DEF_register rd ->
          let id = id_of_dec_spec rd in
          ( {
              docinfo with
              registers =
                Bindings.add id { doc = docinfo_for_register def_annot rd; links; module_path } docinfo.registers;
            },
            skips
          )
      | DEF_let (LB_aux (LB_val (pat, _), _) as letbind) ->
          let ids = pat_ids pat in
          ( IdSet.fold
              (fun id docinfo ->
                {
                  docinfo with
                  lets = Bindings.add id { doc = docinfo_for_let def_annot letbind; links; module_path } docinfo.lets;
                }
              )
              ids docinfo,
            skips
          )
      | _ -> (docinfo, skips)
    in
    let docinfo = List.fold_left docinfo_for_def (empty_docinfo, [initial_skip]) ast.defs |> fst in

    let process_anchors docinfo =
      let anchored = ref Bindings.empty in
      List.iter
        (fun (DEF_aux (aux, def_annot) as def) ->
          let l = def_loc def in
          match aux with
          | DEF_pragma ("anchor", Pragma_line (arg, _)) ->
              let links = hyperlinks files def in
              let module_path = get_module_path def_annot.env in
              let anchor_info =
                { source = doc_loc l Type_check.strip_def Reformatter.doc_def def; comment = def_annot.doc_comment }
              in
              anchored := Bindings.add (mk_id arg) { doc = anchor_info; links; module_path } !anchored
          | _ -> ()
        )
        ast.defs;
      { docinfo with anchors = !anchored }
    in
    let docinfo = process_anchors docinfo in

    let process_spans docinfo =
      let open Rewriter in
      let spans = ref Bindings.empty in
      let current_span = ref None in
      let scan_exp e_aux annot =
        match get_attribute "span" (Type_check.untyped_annot (snd annot)) with
        | None -> E_aux (e_aux, annot)
        | Some (_, Some (AD_aux (AD_string name, _))) ->
            spans :=
              Bindings.add (mk_id name)
                (doc_loc (fst annot) Type_check.strip_exp Reformatter.doc_exp (E_aux (e_aux, annot)))
                !spans;
            E_aux (e_aux, annot)
        | _ -> raise (Reporting.err_general (fst annot) "Invalid span attribute (expected string argument)")
      in
      let exp_alg = { id_exp_alg with e_aux = (fun (e_aux, annot) -> scan_exp e_aux annot) } in
      List.iter
        (fun (DEF_aux (aux, def_annot)) ->
          match aux with
          | DEF_pragma ("span", Pragma_line (arg, _)) when Option.is_none !current_span -> begin
              match String.split_on_char ' ' arg with
              | ["start"; name] -> current_span := Some (name, def_annot.loc)
              | _ -> raise (Reporting.err_general def_annot.loc "Invalid span directive")
            end
          | DEF_pragma ("span", Pragma_line (arg, _)) when arg = "end" -> begin
              match !current_span with
              | Some (name, start_l) ->
                  current_span := None;
                  let end_l = def_annot.loc in
                  begin
                    match (Reporting.simp_loc start_l, Reporting.simp_loc end_l) with
                    | Some (_, p1), Some (p2, _) when p1.pos_fname = p2.pos_fname ->
                        (* Adjust the span for p2 to end at the very start of the directive *)
                        let p2 = { p2 with pos_cnum = p2.pos_bol } in
                        spans := Bindings.add (mk_id name) (doc_lexing_pos p1 p2) !spans
                    | _, _ -> raise (Reporting.err_general def_annot.loc "Invalid locations found when ending span")
                  end
              | None -> raise (Reporting.err_general def_annot.loc "No start span for this end span")
            end
          | DEF_pragma ("span", _) ->
              raise (Reporting.err_general def_annot.loc "Previous span must be ended before this one can begin")
          | _ -> ()
        )
        ast.defs;
      let _ = rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ exp -> fold_exp exp_alg exp) } ast in
      { docinfo with spans = !spans }
    in
    let docinfo = process_spans docinfo in

    let module StringMap = Map.Make (String) in
    let process_file_hashes hashes (DEF_aux (_, doc_annot)) =
      if included_loc files doc_annot.loc then (
        match Reporting.simp_loc doc_annot.loc with
        | None -> hashes
        | Some (p1, _) ->
            if StringMap.mem p1.pos_fname hashes then hashes
            else StringMap.add p1.pos_fname (hash_file p1.pos_fname) hashes
      )
      else hashes
    in
    let hashes = List.fold_left process_file_hashes StringMap.empty ast.defs in
    { docinfo with hashes = StringMap.bindings hashes }
end
