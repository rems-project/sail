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

(** This module defines types representing the documentation info
   (docinfo) associated with Sail ASTs. Additionally we define
   functions for converting these types into a language-neutral json
   representation. *)

open Libsail

open Ast
open Ast_defs
open Ast_util

(** In the case of latex, we generate files containing a sequence of
   commands that can simply be included. For other documentation
   targets with tooling that may consume the json output however, we
   define a version number that allows checking the generated version
   info with what the external tooling supports. *)
let docinfo_version = 1

let same_file f1 f2 =
  Filename.basename f1 = Filename.basename f2 && Filename.dirname f1 = Filename.dirname f2
 
type location_or_raw =
  | Raw of string
  | Location of string * int * int * int * int * int * int

let location_or_raw_to_json = function
  | Raw s -> `String s
  | Location (fname, line1, bol1, char1, line2, bol2, char2) ->
     `Assoc [("file", `String fname); ("loc", `List [`Int line1; `Int bol1; `Int char1; `Int line2; `Int bol2; `Int char2])]

let doc_loc l f x =
  match Reporting.simp_loc l with
  | Some (p1, p2) when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname ->
     Location (p1.pos_fname, p1.pos_lnum, p1.pos_bol, p1.pos_cnum, p2.pos_lnum, p2.pos_bol, p2.pos_cnum)
  | _ -> Raw (f x |> Pretty_print_sail.to_string)

type hyper_location = string * int * int

let included_loc files l =
  match Reporting.loc_file l with
  | Some file ->
     Util.list_empty files || List.exists (same_file file) files
  | None ->
     Util.list_empty files
                    
let hyper_loc l =
  match Reporting.simp_loc l with
  | Some (p1, p2) when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname ->
     Some (p1.pos_fname, p1.pos_cnum, p2.pos_cnum)
  | _ -> None
                    
type hyperlink =
  | Function of id * hyper_location
  | Register of id * hyper_location

let hyperlink_to_json = function
  | Function (id, (file, c1, c2)) ->
     `Assoc [("type", `String "function"); ("id", `String (string_of_id id)); ("file", `String file); ("loc", `List [`Int c1; `Int c2])]
  | Register (id, (file, c1, c2)) ->
     `Assoc [("type", `String "register"); ("id", `String (string_of_id id)); ("file", `String file); ("loc", `List [`Int c1; `Int c2])]

let hyperlinks_to_json = function
  | [] -> `Null
  | links -> `List (List.map hyperlink_to_json links)

let hyperlinks_from_def files def =
  let open Rewriter in
  let links = ref [] in

  let link f l =
    if included_loc files l then (
      match hyper_loc l with
      | Some hloc -> links := f hloc :: !links
      | None -> ()
    ) in

  let scan_lexp lexp_aux annot =
    let env = Type_check.env_of_annot annot in
    begin match lexp_aux with
    | LEXP_cast (_, id) | LEXP_id id ->
       begin match Type_check.Env.lookup_id id env with
       | Register _ ->
          link (fun hloc -> Register (id, hloc)) (id_loc id)
       | _ -> ()
       end
    | _ -> ()
    end;
    LEXP_aux (lexp_aux, annot)
  in
  
  let scan_exp e_aux annot =
    let env = Type_check.env_of_annot annot in
    begin match e_aux with
    | E_id id ->
       begin match Type_check.Env.lookup_id id env with
       | Register _ ->
          link (fun hloc -> Register (id, hloc)) (id_loc id)
       | _ -> ()
       end
    | E_app (f, _) ->
       link (fun hloc -> Function (f, hloc)) (id_loc f)
    | _ -> ()
    end;
    E_aux (e_aux, annot)
  in

  let rw_exp _ exp =
    fold_exp {
        id_exp_alg with e_aux = (fun (e_aux, annot) -> scan_exp e_aux annot);
                        lEXP_aux = (fun (l_aux, annot) -> scan_lexp l_aux annot)
      } exp in
  ignore (rewrite_ast_defs { rewriters_base with rewrite_exp = rw_exp } [def]);

  !links
              
let doc_loc l f x =
  match Reporting.simp_loc l with
  | Some (p1, p2) when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname ->
     Location (p1.pos_fname, p1.pos_lnum, p1.pos_bol, p1.pos_cnum, p2.pos_lnum, p2.pos_bol, p2.pos_cnum)
  | _ -> Raw (f x |> Pretty_print_sail.to_string)

let rec pat_to_json (P_aux (aux, _)) =
  let pat_type t = ("type", `String t) in
  let seq_pat_json t pats = `Assoc [pat_type t; ("patterns", `List (List.map pat_to_json pats))] in
  match aux with
  | P_lit lit -> `Assoc [pat_type "literal"; ("value", `String (string_of_lit lit))]
  | P_wild -> `Assoc [pat_type "wildcard"]
  | P_as (pat, id) -> `Assoc [pat_type "as"; ("pattern", pat_to_json pat); ("id", `String (string_of_id id))]
  | P_typ (_, pat) -> pat_to_json pat
  | P_id id -> `Assoc [pat_type "id"; ("id", `String (string_of_id id))]
  | P_var (pat, _) -> `Assoc [pat_type "var"; ("pattern", pat_to_json pat)]
  | P_app (id, pats) -> `Assoc [pat_type "app"; ("id", `String (string_of_id id)); ("patterns", `List (List.map pat_to_json pats))]
  | P_vector pats -> seq_pat_json "vector" pats
  | P_vector_concat pats -> seq_pat_json "vector_concat" pats
  | P_tup pats -> seq_pat_json "tuple" pats
  | P_list pats -> seq_pat_json "list" pats
  | P_cons (pat_hd, pat_tl) -> `Assoc [pat_type "cons"; ("hd", pat_to_json pat_hd); ("tl", pat_to_json pat_tl)]
  | P_string_append pats -> seq_pat_json "string_append" pats
  | P_or _ | P_not _ -> `Null
       
type 'a function_clause_doc = {
    number : int;
    source : location_or_raw;
    pat : 'a pat;
    guard_source : location_or_raw option;
    body_source : location_or_raw;
  }

let function_clause_doc_to_json docinfo =
  `Assoc (
      [
        ("number", `Int docinfo.number);
        ("source", location_or_raw_to_json docinfo.source);
        ("pattern", pat_to_json docinfo.pat)
      ]
      @ (match docinfo.guard_source with Some s -> [("guard", location_or_raw_to_json s)] | None -> [])
      @ [
          ("body", location_or_raw_to_json docinfo.body_source)
        ]
    )

type 'a function_doc =
  | Multiple_clauses of 'a function_clause_doc list
  | Single_clause of 'a function_clause_doc

let function_doc_to_json = function
  | Multiple_clauses docinfos -> `List (List.map function_clause_doc_to_json docinfos)
  | Single_clause docinfo -> function_clause_doc_to_json docinfo

type 'a mapping_clause_doc = {
    number : int;
    source : location_or_raw;
    left : 'a pat option;
    right : 'a pat option;
    body : location_or_raw option;
  }

let mapping_clause_doc_to_json docinfo =
  `Assoc (
      [
        ("number", `Int docinfo.number);
        ("source", location_or_raw_to_json docinfo.source)
      ]
      @ (match docinfo.left with Some p -> [("left", pat_to_json p)] | None -> [])
      @ (match docinfo.right with Some p -> [("right", pat_to_json p)] | None -> [])
      @ (match docinfo.body with Some s -> [("body", location_or_raw_to_json s)] | None -> [])
    )

type 'a mapping_doc = 'a mapping_clause_doc list

let mapping_doc_to_json docinfos = `List (List.map mapping_clause_doc_to_json docinfos)
                    
type valspec_doc = {
    source : location_or_raw;
    type_source : location_or_raw;
  }

let docinfo_for_valspec (VS_aux (VS_val_spec ((TypSchm_aux (_, ts_annot) as ts), _, _, _), vs_annot) as vs) = {
    source = doc_loc (fst vs_annot) (Pretty_print_sail.doc_spec ~comment:false) vs;
    type_source = doc_loc (fst vs_annot) Pretty_print_sail.doc_typschm ts
  }
 
let valspec_doc_to_json docinfo =
  `Assoc [
      ("source", location_or_raw_to_json docinfo.source);
      ("type", location_or_raw_to_json docinfo.type_source)
    ]

type typdef_doc = location_or_raw

let typdef_doc_to_json = location_or_raw_to_json

let docinfo_for_typdef (TD_aux (_, annot) as td) = doc_loc (fst annot) Pretty_print_sail.doc_typdef td

type register_doc = {
    source : location_or_raw;
    type_source : location_or_raw;
    exp_source : location_or_raw option;
  }

let docinfo_for_register (DEC_aux (DEC_reg ((Typ_aux (_, typ_l) as typ), _, exp), rd_annot) as rd) = {
    source = doc_loc (fst rd_annot) (Pretty_print_sail.doc_dec) rd;
    type_source = doc_loc typ_l Pretty_print_sail.doc_typ typ;
    exp_source = Option.map (fun (E_aux (_, (l, _)) as exp) -> doc_loc l Pretty_print_sail.doc_exp exp) exp
  }

let register_doc_to_json docinfo =
  `Assoc (
      [
        ("source", location_or_raw_to_json docinfo.source);
        ("type", location_or_raw_to_json docinfo.type_source)
      ]
      @ (match docinfo.exp_source with
         | None -> []
         | Some source -> [("exp", location_or_raw_to_json source)])
    )

type let_doc = {
    source : location_or_raw;
    exp_source : location_or_raw;
  }

let docinfo_for_let (LB_aux (LB_val (pat, exp), annot) as lbind) = {
    source = doc_loc (fst annot) (Pretty_print_sail.doc_letbind) lbind;
    exp_source = doc_loc (exp_loc exp) Pretty_print_sail.doc_exp exp;
  }

let let_doc_to_json docinfo =
  `Assoc [
      ("source", location_or_raw_to_json docinfo.source);
      ("exp", location_or_raw_to_json docinfo.exp_source)
    ]
  
let pair_to_json x_label f y_label g (x, y) =
  match (f x, g y) with
  | `Null, `Null -> `Null
  | x, `Null -> `Assoc [(x_label, x)]
  | `Null, y -> `Assoc [(y_label, y)]
  | x, y -> `Assoc [(x_label, x); (y_label, y)]

type 'a docinfo = {
    functions : ('a function_doc * hyperlink list) Bindings.t;
    mappings : ('a mapping_doc * hyperlink list) Bindings.t;
    valspecs : (valspec_doc * hyperlink list) Bindings.t;
    typdefs : (typdef_doc * hyperlink list) Bindings.t;
    registers : (register_doc * hyperlink list) Bindings.t;
    lets : (let_doc * hyperlink list) Bindings.t;
    anchors : (location_or_raw * hyperlink list) Bindings.t;
  }

let bindings_to_json b f =
  Bindings.bindings b
  |> List.map (fun (key, elem) -> (string_of_id key, f elem))
  |> (fun elements -> `Assoc elements)

let docinfo_to_json docinfo =
  `Assoc [
      ("version", `Int docinfo_version);
      ("functions", bindings_to_json docinfo.functions (pair_to_json "function" function_doc_to_json "links" hyperlinks_to_json));
      ("mappings", bindings_to_json docinfo.mappings (pair_to_json "mapping" mapping_doc_to_json "links" hyperlinks_to_json));
      ("vals", bindings_to_json docinfo.valspecs (pair_to_json "val" valspec_doc_to_json "links" hyperlinks_to_json));
      ("types", bindings_to_json docinfo.typdefs (pair_to_json "type" typdef_doc_to_json "links" hyperlinks_to_json));
      ("registers", bindings_to_json docinfo.registers (pair_to_json "register" register_doc_to_json "links" hyperlinks_to_json));
      ("lets", bindings_to_json docinfo.lets (pair_to_json "let" let_doc_to_json "links" hyperlinks_to_json));
      ("anchors", bindings_to_json docinfo.anchors (pair_to_json "anchor" location_or_raw_to_json "links" hyperlinks_to_json));
    ]

let docinfo_for_funcl ?files ?outer_annot n (FCL_aux (FCL_Funcl (id, pexp), annot) as clause) =
  let annot = match outer_annot with None -> annot | Some annot -> annot in
  let source = doc_loc (fst annot) Pretty_print_sail.doc_funcl clause in
  let pat, guard, exp = match pexp with
    | Pat_aux (Pat_exp (pat, exp), _) -> pat, None, exp
    | Pat_aux (Pat_when (pat, guard, exp), _) -> pat, Some guard, exp in
  let guard_source = Option.map (fun exp -> doc_loc (exp_loc exp) Pretty_print_sail.doc_exp exp) guard in
  let body_source = match exp with
    | E_aux (E_block (exp :: exps), _) ->
       let first_loc = exp_loc exp in
       let last_loc = exp_loc (Util.last (exp :: exps)) in
       begin match Reporting.simp_loc first_loc, Reporting.simp_loc last_loc with
       | Some (p1, _), Some (_, p2) when p1.pos_fname = p2.pos_fname && Filename.is_relative p1.pos_fname ->
          Location (p1.pos_fname, p1.pos_lnum, p1.pos_bol, p1.pos_cnum, p2.pos_lnum, p2.pos_bol, p2.pos_cnum)
       | _, _ ->
          Raw (Pretty_print_sail.doc_block (exp :: exps) |> Pretty_print_sail.to_string)
       end
    | _ -> doc_loc (exp_loc exp) Pretty_print_sail.doc_exp exp in
  { number = n; source = source; pat = pat; guard_source = guard_source; body_source = body_source }

let included_clause files (FCL_aux (_, annot)) = included_loc files (fst annot)
       
let docinfo_for_fundef files (FD_aux (FD_function (_, _, clauses), annot) as fdef) =
  let clauses = List.filter (included_clause files) clauses in
  match clauses with
  | [] -> None
  | [clause] ->
     Some (Single_clause (docinfo_for_funcl ~outer_annot:annot 0 clause))
  | _ ->
     Some (Multiple_clauses (List.mapi docinfo_for_funcl clauses))

let docinfo_for_mpexp (MPat_aux (aux, annot)) =
  match aux with
  | MPat_pat mpat -> Rewrites.pat_of_mpat mpat
  | MPat_when (mpat, _) -> Rewrites.pat_of_mpat mpat
 
let docinfo_for_mapcl n (MCL_aux (aux, annot) as clause) =
  let source = doc_loc (fst annot) Pretty_print_sail.doc_mapcl clause in
  let left, right, body = match aux with
    | MCL_bidir (left, right) ->
       let left = docinfo_for_mpexp left in
       let right = docinfo_for_mpexp right in
       (Some left, Some right, None)
    | MCL_forwards (left, body) ->
       let left = docinfo_for_mpexp left in
     let body = doc_loc (exp_loc body) Pretty_print_sail.doc_exp body in
     (Some left, None, Some body)
    | MCL_backwards (right, body) ->
       let right = docinfo_for_mpexp right in
       let body = doc_loc (exp_loc body) Pretty_print_sail.doc_exp body in
       (None, Some right, Some body)
  in
  { number = n; source = source; left = left; right = right; body = body }
    
let included_mapping_clause files (MCL_aux (_, annot)) = included_loc files (fst annot)
    
let docinfo_for_mapdef files (MD_aux (MD_mapping (_, _, clauses), annot) as mdef) =
  let clauses = List.filter (included_mapping_clause files) clauses in
  match clauses with
  | [] -> None
  | _ ->
     Some (List.mapi docinfo_for_mapcl clauses)

let docinfo_for_ast ~files ~hyperlinks ast =
  let empty_docinfo = {
      functions = Bindings.empty;
      mappings = Bindings.empty;
      valspecs = Bindings.empty;
      typdefs = Bindings.empty;
      registers = Bindings.empty;
      lets = Bindings.empty;
      anchors = Bindings.empty;
    } in
  let initial_skip = match files with
    | [] -> false
    | _ -> true in
  let skip_file file =
    if List.exists (same_file file) files then (
      false
    ) else (
      initial_skip
    ) in
  let skipping = function
    | true :: _ -> true
    | _ -> false in
  let docinfo_for_def (docinfo, skips) def =
    let links = hyperlinks files def in
    match def with
    (* Maintain a stack of booleans, for each file if it was not
       specified via -doc_file, we push true to skip it. If no
       -doc_file flags are passed, include everything. *)
    | DEF_pragma (("file_start" | "include_start"), path, _) ->
       docinfo, (skip_file path :: skips)
    | DEF_pragma (("file_end" | "include_end"), path, _) ->
       docinfo, (match skips with _ :: skips -> skips | [] -> [])

    (* Function definiton may be scattered, so we can't skip it *)
    | DEF_fundef fdef ->
       let id = id_of_fundef fdef in
       begin match docinfo_for_fundef files fdef with
       | None -> docinfo
       | Some info -> { docinfo with functions = Bindings.add id (info, links) docinfo.functions }
       end,
       skips

    | DEF_mapdef mdef ->
       let id = id_of_mapdef mdef in
       begin match docinfo_for_mapdef files mdef with
       | None -> docinfo
       | Some info -> { docinfo with mappings = Bindings.add id (info, links) docinfo.mappings }
       end,
       skips

    | _ when skipping skips ->
       docinfo, skips

    | DEF_spec vs ->
       let id = id_of_val_spec vs in
       { docinfo with valspecs = Bindings.add id (docinfo_for_valspec vs, links) docinfo.valspecs },
       skips
    | DEF_type td ->
       let id = id_of_type_def td in
       { docinfo with typdefs = Bindings.add id (docinfo_for_typdef td, links) docinfo.typdefs },
       skips
    | DEF_reg_dec rd ->
       let id = id_of_dec_spec rd in
       { docinfo with registers = Bindings.add id (docinfo_for_register rd, links) docinfo.registers },
       skips
    | DEF_val (LB_aux (LB_val (pat, _ ), annot) as letbind) ->
       let ids = pat_ids pat in
       IdSet.fold (fun id docinfo ->
           { docinfo with lets = Bindings.add id (docinfo_for_let letbind, links) docinfo.lets }
         ) ids docinfo,
       skips
    | DEF_pragma _ ->
       docinfo, skips
    | _ ->
       docinfo, skips
  in
  let docinfo = List.fold_left docinfo_for_def (empty_docinfo, [initial_skip]) ast.defs |> fst in
  let process_anchors docinfo =
    let anchored = ref Bindings.empty in
    let pending_anchor = ref None in
    List.iter (fun def ->
        let l = def_loc def in
        match def with
        | DEF_pragma ("doc", command, l) ->
           begin match String.index_from_opt command 0 ' ' with
           | Some i ->
              let subcommand = String.sub command 0 i in
              let arg = String.sub command i (String.length command - i) |> String.trim in
              pending_anchor := Some arg
           | None ->
              raise (Reporting.err_general l "Invalid $doc directive")
           end
        | DEF_pragma _ -> ()
        | _ ->
           begin match !pending_anchor with
           | Some arg ->
              let links = hyperlinks files def in
              anchored := Bindings.add (mk_id arg) (doc_loc l Pretty_print_sail.doc_def def, links) !anchored;
              pending_anchor := None
           | None -> ()
           end
      ) ast.defs;
    { docinfo with anchors = !anchored }
  in
  process_anchors docinfo
