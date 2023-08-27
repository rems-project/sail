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

open Libsail

open Ast
open Ast_defs
open Ast_util
open PPrint
open Type_check
open Util
open Pretty_print_common
open Ocaml_backend

let lem_mode = ref false
let mword_mode = ref false

let maybe_zencode s = if !lem_mode then String.uncapitalize_ascii s else zencode_string s
let maybe_zencode_upper s = if !lem_mode then String.capitalize_ascii s else zencode_upper_string s

let rec rewriteExistential (kids : kinded_id list) (Typ_aux (typ_aux, annot) as typ) =
  print_endline (string_of_typ typ);
  match typ_aux with
  | Typ_tuple typs -> Typ_aux (Typ_tuple (List.map (rewriteExistential kids) typs), annot)
  | Typ_exist _ -> Reporting.unreachable annot __POS__ "nested Typ_exist in rewriteExistential"
  | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)])
    when string_of_id id = "atom" || string_of_id id = "int" ->
      (* List.exists (fun k -> string_of_kid (kopt_kid k) = string_of_kid kid) kids -> *)
      print_endline ("*** rewriting to int - kid is '" ^ string_of_kid kid ^ "'");
      Typ_aux (Typ_id (mk_id "int"), annot)
  | Typ_internal_unknown | Typ_id _ | Typ_var _ | Typ_fn _ | Typ_bidir _ | Typ_app _ -> typ

let frominterp_typedef (TD_aux (td_aux, (l, _))) =
  let fromValueArgs (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_tuple typs ->
        brackets
          (separate space
             [
               string "V_tuple";
               brackets (separate (semi ^^ space) (List.mapi (fun i _ -> string ("v" ^ string_of_int i)) typs));
             ]
          )
    | _ -> brackets (string "v0")
  in
  let fromValueKid (Kid_aux (Var name, _)) = string ("typq_" ^ name) in
  let fromValueNexp (Nexp_aux (nexp_aux, annot) as nexp) =
    match nexp_aux with
    | Nexp_constant num ->
        parens (separate space [string "Big_int.of_string"; dquotes (string (Nat_big_num.to_string num))])
    | Nexp_var var -> fromValueKid var
    | Nexp_id id -> string (string_of_id id ^ "FromInterpValue")
    | _ -> string ("NEXP(" ^ string_of_nexp nexp ^ ")")
  in
  let rec fromValueTypArg (A_aux (a_aux, _)) =
    match a_aux with
    | A_typ typ -> parens (string "fun v -> " ^^ parens (fromValueTyp typ "v"))
    | A_nexp nexp -> fromValueNexp nexp
    | A_bool _ -> parens (string "boolFromInterpValue")
  and fromValueTyp (Typ_aux (typ_aux, l) as typ) arg_name =
    match typ_aux with
    | Typ_id id ->
        parens (concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"; space; string arg_name])
    (* special case bit vectors for lem *)
    | Typ_app
        ( Id_aux (Id "vector", _),
          [A_aux (A_nexp len_nexp, _); A_aux (A_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _)), _)]
        )
      when !lem_mode ->
        parens (separate space [string (maybe_zencode "bitsFromInterpValue"); string arg_name])
    | Typ_app (typ_id, typ_args) ->
        assert (typ_args <> []);
        if string_of_id typ_id = "bits" then parens (separate space ([string "bitsFromInterpValue"] @ [string arg_name]))
        else
          parens
            (separate space
               ([string (maybe_zencode (string_of_id typ_id) ^ "FromInterpValue")]
               @ List.map fromValueTypArg typ_args
               @ [string arg_name]
               )
            )
    | Typ_var kid -> parens (separate space [fromValueKid kid; string arg_name])
    | Typ_fn _ -> parens (string "failwith \"fromValueTyp: Typ_fn arm unimplemented\"")
    | Typ_bidir _ -> parens (string "failwith \"fromValueTyp: Typ_bidir arm unimplemented\"")
    | Typ_exist (kids, _, t) -> parens (fromValueTyp (rewriteExistential kids t) arg_name)
    | Typ_tuple typs ->
        parens
          (string ("match " ^ arg_name ^ " with V_tuple ")
          ^^ brackets
               (separate
                  (string ";" ^^ space)
                  (List.mapi (fun i _ -> string (arg_name ^ "_tup" ^ string_of_int i)) typs)
               )
          ^^ string " -> "
          ^^ parens
               (separate comma_sp (List.mapi (fun i t -> fromValueTyp t (arg_name ^ "_tup" ^ string_of_int i)) typs))
          )
    | Typ_internal_unknown -> failwith "escaped Typ_internal_unknown"
  in
  let fromValueVals (Typ_aux (typ_aux, l) as typ) =
    match typ_aux with
    | Typ_tuple typs ->
        parens (separate comma_sp (List.mapi (fun i typ -> fromValueTyp typ ("v" ^ string_of_int i)) typs))
    | _ -> fromValueTyp typ "v0"
  in
  let fromValueTypq (QI_aux (qi_aux, _)) =
    match qi_aux with
    | QI_id (KOpt_aux (KOpt_kind (K_aux (kind_aux, _), kid), _)) -> fromValueKid kid
    | QI_constraint _ -> empty
  in
  let fromValueTypqs (TypQ_aux (typq_aux, _)) =
    match typq_aux with TypQ_no_forall -> [empty] | TypQ_tq quants -> List.map fromValueTypq quants
  in
  match td_aux with
  | TD_variant (id, typq, arms, _) -> begin
      match id with
      | Id_aux (Id "read_kind", _) -> empty
      | Id_aux (Id "write_kind", _) -> empty
      | Id_aux (Id "a64_barrier_domain", _) -> empty
      | Id_aux (Id "a64_barrier_type", _) -> empty
      | Id_aux (Id "barrier_kind", _) -> empty
      | Id_aux (Id "trans_kind", _) -> empty
      | Id_aux (Id "instruction_kind", _) -> empty
      | Id_aux (Id "cache_op_kind", _) -> empty
      | Id_aux (Id "regfp", _) -> empty
      | Id_aux (Id "regfps", _) -> empty
      | Id_aux (Id "niafp", _) -> empty
      | Id_aux (Id "niafps", _) -> empty
      | Id_aux (Id "diafp", _) -> empty
      | Id_aux (Id "diafps", _) -> empty
      (* | Id_aux ((Id "option"),_) -> empty *)
      | Id_aux (Id id_string, _) | Id_aux (Operator id_string, _) ->
          if !lem_mode && id_string = "option" then empty
          else (
            let fromInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"] in
            let fromFallback =
              separate space
                [
                  pipe;
                  underscore;
                  arrow;
                  string "failwith";
                  dquotes (string ("invalid interpreter value for " ^ string_of_id id));
                ]
            in
            let fromInterpValue =
              prefix 2 1
                (separate space
                   [
                     string "let";
                     fromInterpValueName;
                     separate space (fromValueTypqs typq @ [string "v"]);
                     equals;
                     string "match v with";
                   ]
                )
                (separate_map hardline
                   (fun (Tu_aux (Tu_ty_id (typ, ctor_id), _)) ->
                     separate space
                       [
                         pipe;
                         string "V_ctor";
                         parens (concat [dquotes (string (string_of_id ctor_id)); comma_sp; fromValueArgs typ]);
                         arrow;
                         string (maybe_zencode_upper (string_of_id ctor_id));
                         fromValueVals typ;
                       ]
                   )
                   arms
                ^^ hardline ^^ fromFallback
                )
            in
            fromInterpValue ^^ twice hardline
          )
    end
  | TD_abbrev (Id_aux (Id "regfps", _), _, _) -> empty
  | TD_abbrev (Id_aux (Id "niafps", _), _, _) -> empty
  | TD_abbrev (Id_aux (Id "bits", _), _, _) when !lem_mode -> empty
  | TD_abbrev (id, typq, typ_arg) -> begin
      let fromInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"] in
      (* HACK: print a type annotation for abbrevs of unquantified types, to help cases ocaml can't type-infer on its own *)
      let fromInterpValspec =
        (* HACK because of lem renaming *)
        if string_of_id id = "opcode" || string_of_id id = "integer" then empty
        else (
          match typ_arg with
          | A_aux (A_typ _, _) -> begin
              match typq with
              | TypQ_aux (TypQ_no_forall, _) ->
                  separate space [colon; string "value"; arrow; string (maybe_zencode (string_of_id id))]
              | _ -> empty
            end
          | _ -> empty
        )
      in
      let fromInterpValue =
        separate space
          [
            string "let";
            fromInterpValueName;
            separate space (fromValueTypqs typq);
            fromInterpValspec;
            equals;
            fromValueTypArg typ_arg;
          ]
      in
      fromInterpValue ^^ twice hardline
    end
  | TD_enum (Id_aux (Id "read_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "write_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "a64_barrier_domain", _), _, _) -> empty
  | TD_enum (Id_aux (Id "a64_barrier_type", _), _, _) -> empty
  | TD_enum (Id_aux (Id "barrier_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "trans_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "cache_op_kind", _), _, _) -> empty
  | TD_enum (id, ids, _) ->
      let fromInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"] in
      let fromFallback =
        separate space
          [
            pipe;
            underscore;
            arrow;
            string "failwith";
            dquotes (string ("invalid interpreter value for " ^ string_of_id id));
          ]
      in
      let fromInterpValue =
        prefix 2 1
          (separate space [string "let"; fromInterpValueName; string "v"; equals; string "match v with"])
          (separate_map hardline
             (fun id ->
               separate space
                 [
                   pipe;
                   string "V_ctor";
                   parens (concat [dquotes (string (string_of_id id)); comma_sp; string "[]"]);
                   arrow;
                   string (maybe_zencode_upper (string_of_id id));
                 ]
             )
             ids
          ^^ hardline ^^ fromFallback
          )
      in
      fromInterpValue ^^ twice hardline
  | TD_record (record_id, typq, fields, _) ->
      let fromInterpField (typ, id) =
        separate space
          [
            string (maybe_zencode ((if !lem_mode then string_of_id record_id ^ "_" else "") ^ string_of_id id));
            equals;
            fromValueTyp typ ("(StringMap.find \"" ^ string_of_id id ^ "\" fs)");
          ]
      in
      let fromInterpValueName = concat [string (maybe_zencode (string_of_id record_id)); string "FromInterpValue"] in
      let fromFallback =
        separate space
          [
            pipe;
            underscore;
            arrow;
            string "failwith";
            dquotes (string ("invalid interpreter value for " ^ string_of_id record_id));
          ]
      in
      let fromInterpValue =
        prefix 2 1
          (separate space
             [
               string "let";
               fromInterpValueName;
               separate space (fromValueTypqs typq @ [string "v"]);
               equals;
               string "match v with";
             ]
          )
          (separate space
             [pipe; string "V_record fs"; arrow; braces (separate_map (semi ^^ space) fromInterpField fields)]
          ^^ hardline ^^ fromFallback
          )
      in
      fromInterpValue ^^ twice hardline
  | _ -> empty

let tointerp_typedef (TD_aux (td_aux, (l, _))) =
  let toValueArgs (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_tuple typs -> parens (separate comma_sp (List.mapi (fun i _ -> string ("v" ^ string_of_int i)) typs))
    | _ -> parens (string "v0")
  in
  let toValueKid (Kid_aux (Var name, _)) = string ("typq_" ^ name) in
  let toValueNexp (Nexp_aux (nexp_aux, _) as nexp) =
    match nexp_aux with
    | Nexp_constant num ->
        parens (separate space [string "Big_int.of_string"; dquotes (string (Nat_big_num.to_string num))])
    | Nexp_var var -> toValueKid var
    | Nexp_id id -> string (string_of_id id ^ "ToInterpValue")
    | _ -> string ("NEXP(" ^ string_of_nexp nexp ^ ")")
  in
  let rec toValueTypArg (A_aux (a_aux, _)) =
    match a_aux with
    | A_typ typ -> parens (string "fun v -> " ^^ parens (toValueTyp typ "v"))
    | A_nexp nexp -> toValueNexp nexp
    | A_bool _ -> parens (string "boolToInterpValue")
  and toValueTyp (Typ_aux (typ_aux, l) as typ) arg_name =
    match typ_aux with
    | Typ_id id ->
        parens (concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"; space; string arg_name])
    (* special case bit vectors for lem *)
    | Typ_app
        ( Id_aux (Id "vector", _),
          [A_aux (A_nexp len_nexp, _); A_aux (A_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _)), _)]
        )
      when !lem_mode ->
        parens (separate space [string (maybe_zencode "bitsToInterpValue"); string arg_name])
    | Typ_app (typ_id, typ_args) ->
        assert (typ_args <> []);
        if string_of_id typ_id = "bits" then parens (separate space ([string "bitsToInterpValue"] @ [string arg_name]))
        else
          parens
            (separate space
               ([string (maybe_zencode (string_of_id typ_id) ^ "ToInterpValue")]
               @ List.map toValueTypArg typ_args
               @ [string arg_name]
               )
            )
    | Typ_var kid -> parens (separate space [toValueKid kid; string arg_name])
    | Typ_fn _ -> parens (string "failwith \"toValueTyp: Typ_fn arm unimplemented\"")
    | Typ_bidir _ -> parens (string "failwith \"toValueTyp: Typ_bidir arm unimplemented\"")
    | Typ_exist (kids, _, t) -> parens (toValueTyp (rewriteExistential kids t) arg_name)
    | Typ_tuple typs ->
        parens
          (string ("match " ^ arg_name ^ " with ")
          ^^ parens (separate comma_sp (List.mapi (fun i _ -> string (arg_name ^ "_tup" ^ string_of_int i)) typs))
          ^^ string " -> V_tuple "
          ^^ brackets
               (separate
                  (string ";" ^^ space)
                  (List.mapi (fun i t -> toValueTyp t (arg_name ^ "_tup" ^ string_of_int i)) typs)
               )
          )
    | Typ_internal_unknown -> failwith "escaped Typ_internal_unknown"
  in
  let toValueVals (Typ_aux (typ_aux, _) as typ) =
    match typ_aux with
    | Typ_tuple typs ->
        brackets
          (separate space
             [
               string "V_tuple";
               brackets (separate (semi ^^ space) (List.mapi (fun i typ -> toValueTyp typ ("v" ^ string_of_int i)) typs));
             ]
          )
    | _ -> brackets (toValueTyp typ "v0")
  in
  let toValueTypq (QI_aux (qi_aux, _)) =
    match qi_aux with
    | QI_id (KOpt_aux (KOpt_kind (K_aux (kind_aux, _), kid), _)) -> toValueKid kid
    | QI_constraint _ -> empty
  in
  let toValueTypqs (TypQ_aux (typq_aux, _)) =
    match typq_aux with TypQ_no_forall -> [empty] | TypQ_tq quants -> List.map toValueTypq quants
  in
  match td_aux with
  | TD_variant (id, typq, arms, _) -> begin
      match id with
      | Id_aux (Id "read_kind", _) -> empty
      | Id_aux (Id "write_kind", _) -> empty
      | Id_aux (Id "a64_barrier_domain", _) -> empty
      | Id_aux (Id "a64_barrier_type", _) -> empty
      | Id_aux (Id "barrier_kind", _) -> empty
      | Id_aux (Id "trans_kind", _) -> empty
      | Id_aux (Id "instruction_kind", _) -> empty
      | Id_aux (Id "cache_op_kind", _) -> empty
      | Id_aux (Id "regfp", _) -> empty
      | Id_aux (Id "regfps", _) -> empty
      | Id_aux (Id "niafp", _) -> empty
      | Id_aux (Id "niafps", _) -> empty
      | Id_aux (Id "diafp", _) -> empty
      | Id_aux (Id "diafps", _) -> empty
      (* | Id_aux ((Id "option"),_) -> empty *)
      | Id_aux (Id id_string, _) | Id_aux (Operator id_string, _) ->
          if !lem_mode && id_string = "option" then empty
          else (
            let toInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"] in
            let toInterpValue =
              prefix 2 1
                (separate space
                   [
                     string "let";
                     toInterpValueName;
                     separate space (toValueTypqs typq @ [string "v"]);
                     equals;
                     string "match v with";
                   ]
                )
                (separate_map hardline
                   (fun (Tu_aux (Tu_ty_id (typ, ctor_id), _)) ->
                     separate space
                       [
                         pipe;
                         string (maybe_zencode_upper (string_of_id ctor_id));
                         toValueArgs typ;
                         arrow;
                         string "V_ctor";
                         parens (concat [dquotes (string (string_of_id ctor_id)); comma_sp; toValueVals typ]);
                       ]
                   )
                   arms
                )
            in
            toInterpValue ^^ twice hardline
          )
    end
  | TD_abbrev (Id_aux (Id "regfps", _), _, _) -> empty
  | TD_abbrev (Id_aux (Id "niafps", _), _, _) -> empty
  | TD_abbrev (Id_aux (Id "bits", _), _, _) when !lem_mode -> empty
  | TD_abbrev (id, typq, typ_arg) -> begin
      let toInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"] in
      (* HACK: print a type annotation for abbrevs of unquantified types, to help cases ocaml can't type-infer on its own *)
      let toInterpValspec =
        (* HACK because of lem renaming *)
        if string_of_id id = "opcode" || string_of_id id = "integer" then empty
        else (
          match typ_arg with
          | A_aux (A_typ _, _) -> begin
              match typq with
              | TypQ_aux (TypQ_no_forall, _) ->
                  separate space [colon; string (maybe_zencode (string_of_id id)); arrow; string "value"]
              | _ -> empty
            end
          | _ -> empty
        )
      in
      let toInterpValue =
        separate space
          [
            string "let";
            toInterpValueName;
            separate space (toValueTypqs typq);
            toInterpValspec;
            equals;
            toValueTypArg typ_arg;
          ]
      in
      toInterpValue ^^ twice hardline
    end
  | TD_enum (Id_aux (Id "read_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "write_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "a64_barrier_domain", _), _, _) -> empty
  | TD_enum (Id_aux (Id "a64_barrier_type", _), _, _) -> empty
  | TD_enum (Id_aux (Id "barrier_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "trans_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "cache_op_kind", _), _, _) -> empty
  | TD_enum (id, ids, _) ->
      let toInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"] in
      let toInterpValue =
        prefix 2 1
          (separate space [string "let"; toInterpValueName; string "v"; equals; string "match v with"])
          (separate_map hardline
             (fun id ->
               separate space
                 [
                   pipe;
                   string (maybe_zencode_upper (string_of_id id));
                   arrow;
                   string "V_ctor";
                   parens (concat [dquotes (string (string_of_id id)); comma_sp; string "[]"]);
                 ]
             )
             ids
          )
      in
      toInterpValue ^^ twice hardline
  | TD_record (record_id, typq, fields, _) ->
      let toInterpField (typ, id) =
        parens
          (separate comma_sp
             [
               dquotes (string (string_of_id id));
               toValueTyp typ
                 ("r." ^ maybe_zencode ((if !lem_mode then string_of_id record_id ^ "_" else "") ^ string_of_id id));
             ]
          )
      in
      let toInterpValueName = concat [string (maybe_zencode (string_of_id record_id)); string "ToInterpValue"] in
      let toInterpValue =
        prefix 2 1
          (separate space [string "let"; toInterpValueName; separate space (toValueTypqs typq @ [string "r"]); equals])
          (separate space
             [
               string "V_record";
               parens
                 (separate space
                    [
                      string "List.fold_left (fun m (k, v) -> StringMap.add k v m) StringMap.empty";
                      brackets (separate_map (semi ^^ space) toInterpField fields);
                    ]
                 );
             ]
          )
      in
      toInterpValue ^^ twice hardline
  | _ -> empty

let tofrominterp_def (DEF_aux (aux, _)) =
  match aux with
  | DEF_type td -> group (frominterp_typedef td ^^ twice hardline ^^ tointerp_typedef td ^^ twice hardline)
  | _ -> empty

let tofrominterp_ast name { defs; _ } =
  (string "open Sail_lib;;" ^^ hardline)
  ^^ (string "open Value;;" ^^ hardline)
  ^^ (if !lem_mode then string "open Sail2_instr_kinds;;" ^^ hardline else empty)
  ^^ (string ("open " ^ String.capitalize_ascii name ^ ";;") ^^ hardline)
  ^^ (if !lem_mode then string ("open " ^ String.capitalize_ascii name ^ "_types;;") ^^ hardline else empty)
  ^^ (if !lem_mode then string ("open " ^ String.capitalize_ascii name ^ "_extras;;") ^^ hardline else empty)
  ^^ (string "module Big_int = Nat_big_num" ^^ ocaml_def_end)
  ^^ (if !mword_mode then string "include ToFromInterp_lib_mword" ^^ hardline else empty)
  ^^ ( if not !mword_mode then
         string
           "include ToFromInterp_lib_bitlist.Make(struct type t = Sail2_values.bitU0 let b0 = Sail2_values.B00 let b1 \
            = Sail2_values.B10 end)"
         ^^ hardline
       else empty
     )
  ^^ concat (List.map tofrominterp_def defs)

let tofrominterp_pp_ast name f ast = ToChannel.pretty 1. 80 f (tofrominterp_ast name ast)

let tofrominterp_output maybe_dir name ast =
  let dir = match maybe_dir with Some dir -> dir | None -> "." in
  let out_chan = open_out (Filename.concat dir (name ^ "_toFromInterp2.ml")) in
  tofrominterp_pp_ast name out_chan ast;
  close_out out_chan
