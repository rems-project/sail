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
open Ast_util
open PPrint
open Type_check
open Util
open Pretty_print_common
open Ocaml_backend

let lem_mode = ref false

let maybe_zencode s = if !lem_mode then String.uncapitalize_ascii s else zencode_string s
let maybe_zencode_upper s = if !lem_mode then String.capitalize_ascii s else zencode_upper_string s

let frominterp_typedef (TD_aux (td_aux, (l, _))) =
  let fromValueArgs (Typ_aux (typ_aux, _)) = match typ_aux with
    | Typ_tup typs -> brackets (separate space [string "V_tuple"; brackets (separate (semi ^^ space) (List.mapi (fun i _ -> string ("v" ^ (string_of_int i))) typs))])
    | _ -> brackets (string "v0")
  in
  let fromValueKid (Kid_aux ((Var name), _)) =
    string ("typq_" ^ name)
  in 
  let fromValueNexp (Nexp_aux (nexp_aux, _)) = match nexp_aux with
    | Nexp_constant num -> parens (separate space [string "Big_int.of_string"; dquotes (string (Nat_big_num.to_string num))])
    | Nexp_var var -> fromValueKid var
    | _ -> string "NEXP"
  in
  let rec fromValueTypArg (A_aux (a_aux, _)) = match a_aux with
    | A_typ typ -> fromValueTyp typ ""
    | A_nexp nexp -> fromValueNexp nexp
    | A_order order -> string ("Order_" ^ (string_of_order order))
    | _ -> string "TYP_ARG"
  and fromValueTyp ((Typ_aux (typ_aux, l)) as typ) arg_name = match typ_aux with
    | Typ_id id -> parens (concat [string (maybe_zencode (string_of_id id)); string ("FromInterpValue"); space; string arg_name])
    (* special case bit vectors for lem *)
    | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp len_nexp, _);
                                         A_aux (A_order (Ord_aux (Ord_dec, _)), _);
                                         A_aux (A_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _)), _)]) when !lem_mode ->
       parens (separate space ([string (maybe_zencode "bitsFromInterpValue"); fromValueNexp len_nexp; string arg_name]))
    | Typ_app (typ_id, typ_args) ->
       assert (typ_args <> []);
       parens (separate space ([string (maybe_zencode (string_of_id typ_id) ^ "FromInterpValue")] @ List.map fromValueTypArg typ_args @ [string arg_name]))
    | Typ_var kid -> parens (separate space [fromValueKid kid; string arg_name])
    | Typ_fn _ -> parens (string "failwith \"fromValueTyp: Typ_fn arm unimplemented\"")
    | _ -> parens (string "failwith \"fromValueTyp: type arm unimplemented\"")
  in 
  let fromValueVals ((Typ_aux (typ_aux, l)) as typ) = match typ_aux with
    | Typ_tup typs -> parens (separate comma_sp (List.mapi (fun i typ -> fromValueTyp typ ("v" ^ (string_of_int i))) typs))
    | _ -> fromValueTyp typ "v0"
  in
  let fromValueTypq (QI_aux (qi_aux, _)) = match qi_aux with
    | QI_id (KOpt_aux (KOpt_kind (K_aux (kind_aux, _), kid), _)) -> fromValueKid kid
    | QI_const _ -> empty
  in
  let fromValueTypqs (TypQ_aux (typq_aux, _)) = match typq_aux with
    | TypQ_no_forall -> [empty]
    | TypQ_tq quants -> List.map fromValueTypq quants
  in
  match td_aux with
  | TD_variant (id, typq, arms, _) ->
     begin match id with
     | Id_aux ((Id "read_kind"),_) -> empty
     | Id_aux ((Id "write_kind"),_) -> empty
     | Id_aux ((Id "barrier_kind"),_) -> empty
     | Id_aux ((Id "trans_kind"),_) -> empty
     | Id_aux ((Id "instruction_kind"),_) -> empty
     | Id_aux ((Id "regfp"),_) -> empty
     | Id_aux ((Id "regfps"),_) -> empty
     | Id_aux ((Id "niafp"),_) -> empty
     | Id_aux ((Id "niafps"),_) -> empty
     | Id_aux ((Id "diafp"),_) -> empty
     | Id_aux ((Id "diafps"),_) -> empty
     (* | Id_aux ((Id "option"),_) -> empty *)
     | Id_aux ((Id id_string), _)
       | Id_aux ((DeIid id_string), _) ->
        if !lem_mode && id_string = "option" then empty else
          let fromInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"] in
          let fromFallback = separate space [pipe; underscore; arrow; string "failwith";
                                             dquotes (string ("invalid interpreter value for " ^ (string_of_id id)))] in
          let fromInterpValue =
            prefix 2 1
              (separate space [string "let"; fromInterpValueName; separate space (fromValueTypqs typq @ [string "v"]); equals; string "match v with"])
              ((separate_map hardline
                  (fun (Tu_aux (Tu_ty_id (typ, ctor_id), _)) ->
                    separate space
                      [pipe; string "V_ctor"; parens (concat [dquotes (string (string_of_id ctor_id)); comma_sp;
                                                              fromValueArgs typ
                                                ]);
                       arrow; string (maybe_zencode_upper (string_of_id ctor_id)); fromValueVals typ
                      ]
                  )
                  arms)
               ^^ hardline ^^ fromFallback)
          in
          fromInterpValue ^^ (twice hardline)
     end
  | TD_abbrev (Id_aux (Id "regfps", _), _, _) -> empty
  | TD_abbrev (Id_aux (Id "niafps", _), _, _) -> empty
  | TD_abbrev (id, typq, typ_arg) ->
     let fromInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"] in
     let fromInterpValue =
       (separate space [string "let"; fromInterpValueName; separate space (fromValueTypqs typq); equals; fromValueTypArg typ_arg])
     in
     fromInterpValue ^^ (twice hardline)
  | TD_enum (Id_aux (Id "read_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "write_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "barrier_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "trans_kind", _), _, _) -> empty
  | TD_enum (id, ids, _) ->
     let fromInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "FromInterpValue"] in
     let fromFallback = separate space [pipe; underscore; arrow; string "failwith";
                                        dquotes (string ("invalid interpreter value for " ^ (string_of_id id)))] in
     let fromInterpValue =
       prefix 2 1
         (separate space [string "let"; fromInterpValueName; string "v"; equals; string "match v with"])
         ((separate_map hardline
             (fun id ->
               separate space
                 [pipe; string "V_ctor"; parens (concat [dquotes (string (string_of_id id)); comma_sp; string "[]"]);
                  arrow; string (maybe_zencode_upper (string_of_id id))]
             )
             ids)
          ^^ hardline ^^ fromFallback)
     in
     fromInterpValue ^^ (twice hardline)
  | TD_record (record_id, typq, fields, _) ->
     let fromInterpField (typ, id) =
       separate space [string (maybe_zencode ((if !lem_mode then string_of_id record_id ^ "_" else "") ^ string_of_id id)); equals; fromValueTyp typ ("(StringMap.find \"" ^ (string_of_id id) ^ "\" fs)")]
     in
     let fromInterpValueName = concat [string (maybe_zencode (string_of_id record_id)); string "FromInterpValue"] in
     let fromFallback = separate space [pipe; underscore; arrow; string "failwith";
                                        dquotes (string ("invalid interpreter value for " ^ (string_of_id record_id)))] in
     let fromInterpValue =
       prefix 2 1
         (separate space [string "let"; fromInterpValueName; separate space (fromValueTypqs typq @ [string "v"]); equals; string "match v with"])
         ((separate space [pipe; string "V_record fs"; arrow; braces (separate_map (semi ^^ space) fromInterpField fields)])
          ^^ hardline ^^ fromFallback)
     in
     fromInterpValue ^^ (twice hardline)
  | _ -> empty

let tointerp_typedef (TD_aux (td_aux, (l, _))) =
  let toValueArgs (Typ_aux (typ_aux, _)) = match typ_aux with
    | Typ_tup typs -> parens (separate comma_sp (List.mapi (fun i _ -> string ("v" ^ (string_of_int i))) typs))
    | _ -> parens (string "v0")
  in
  let toValueKid (Kid_aux ((Var name), _)) =
    string ("typq_" ^ name)
  in
  let toValueNexp (Nexp_aux (nexp_aux, _)) = match nexp_aux with
    | Nexp_constant num -> parens (separate space [string "Big_int.of_string"; dquotes (string (Nat_big_num.to_string num))])
    | Nexp_var var -> toValueKid var
    | _ -> string "NEXP"
  in
  let rec toValueTypArg (A_aux (a_aux, _)) = match a_aux with
    | A_typ typ -> toValueTyp typ ""
    | A_nexp nexp -> toValueNexp nexp
    | A_order order -> string ("Order_" ^ (string_of_order order))
    | _ -> string "TYP_ARG" 
  and toValueTyp ((Typ_aux (typ_aux, l)) as typ) arg_name = match typ_aux with
    | Typ_id id -> parens (concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"; space; string arg_name])
    (* special case bit vectors for lem *)
    | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp len_nexp, _);
                                         A_aux (A_order (Ord_aux (Ord_dec, _)), _);
                                         A_aux (A_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _)), _)]) when !lem_mode ->
       parens (separate space ([string (maybe_zencode "bitsToInterpValue"); toValueNexp len_nexp; string arg_name]))
    | Typ_app (typ_id, typ_args) ->
       assert (typ_args <> []);
       parens (separate space ([string ((maybe_zencode (string_of_id typ_id)) ^ "ToInterpValue")] @ List.map toValueTypArg typ_args @ [string arg_name]))
    | Typ_var kid -> parens (separate space [toValueKid kid; string arg_name])
    | _ -> parens (string "failwith \"toValueTyp: type arm unimplemented\"")
  in
  let toValueVals ((Typ_aux (typ_aux, _)) as typ) = match typ_aux with
    | Typ_tup typs -> brackets (separate space [string "V_tuple"; brackets (separate (semi ^^ space) (List.mapi (fun i typ -> toValueTyp typ ("v" ^ (string_of_int i))) typs))])
    | _ -> brackets (toValueTyp typ "v0")
  in
  let toValueTypq (QI_aux (qi_aux, _)) = match qi_aux with
    | QI_id (KOpt_aux (KOpt_kind (K_aux (kind_aux, _), kid), _)) -> toValueKid kid
    | QI_const _ -> empty
  in
  let toValueTypqs (TypQ_aux (typq_aux, _)) = match typq_aux with
    | TypQ_no_forall -> [empty]
    | TypQ_tq quants -> List.map toValueTypq quants
  in
  match td_aux with
  | TD_variant (id, typq, arms, _) ->
     begin match id with
     | Id_aux ((Id "read_kind"),_) -> empty
     | Id_aux ((Id "write_kind"),_) -> empty
     | Id_aux ((Id "barrier_kind"),_) -> empty
     | Id_aux ((Id "trans_kind"),_) -> empty
     | Id_aux ((Id "instruction_kind"),_) -> empty
     | Id_aux ((Id "regfp"),_) -> empty
     | Id_aux ((Id "regfps"),_) -> empty
     | Id_aux ((Id "niafp"),_) -> empty
     | Id_aux ((Id "niafps"),_) -> empty
     | Id_aux ((Id "diafp"),_) -> empty
     | Id_aux ((Id "diafps"),_) -> empty
     (* | Id_aux ((Id "option"),_) -> empty *)
     | Id_aux ((Id id_string), _)
       | Id_aux ((DeIid id_string), _) ->
        if !lem_mode && id_string = "option" then empty else
          let toInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"] in
          let toInterpValue =
            prefix 2 1
              (separate space [string "let"; toInterpValueName; separate space (toValueTypqs typq @ [string "v"]); equals; string "match v with"])
              ((separate_map hardline
                  (fun (Tu_aux (Tu_ty_id (typ, ctor_id), _)) ->
                    separate space
                      [pipe; string (maybe_zencode_upper (string_of_id ctor_id)); toValueArgs typ;
                       arrow; string "V_ctor"; parens (concat [dquotes (string (string_of_id ctor_id)); comma_sp; toValueVals typ])
                      ]
                  )
                  arms))
          in
          toInterpValue ^^ (twice hardline)
     end
  | TD_abbrev (Id_aux (Id "regfps", _), _, _) -> empty
  | TD_abbrev (Id_aux (Id "niafps", _), _, _) -> empty
  | TD_abbrev (id, typq, typ_arg) ->
     let toInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"] in
     let toInterpValue =
       (separate space [string "let"; toInterpValueName; separate space (toValueTypqs typq); equals; toValueTypArg typ_arg])
     in
     toInterpValue ^^ (twice hardline)
  | TD_enum (Id_aux (Id "read_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "write_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "barrier_kind", _), _, _) -> empty
  | TD_enum (Id_aux (Id "trans_kind", _), _, _) -> empty
  | TD_enum (id, ids, _) ->
     let toInterpValueName = concat [string (maybe_zencode (string_of_id id)); string "ToInterpValue"] in
     let toInterpValue =
       prefix 2 1
         (separate space [string "let"; toInterpValueName; string "v"; equals; string "match v with"])
         ((separate_map hardline
             (fun id ->
               separate space
                 [pipe; string (maybe_zencode_upper (string_of_id id));
                  arrow; string "V_ctor"; parens (concat [dquotes (string (string_of_id id)); comma_sp; string "[]"])]
             )
             ids))
     in
     toInterpValue ^^ (twice hardline)
  | TD_record (record_id, typq, fields, _) ->
     let toInterpField (typ, id) =
       parens (separate comma_sp [dquotes (string (string_of_id id)); toValueTyp typ ("r." ^ (maybe_zencode ((if !lem_mode then string_of_id record_id ^ "_" else "") ^ string_of_id id)))])
     in
     let toInterpValueName = concat [string (maybe_zencode (string_of_id record_id)); string "ToInterpValue"] in
     let toInterpValue =
       prefix 2 1
         (separate space [string "let"; toInterpValueName; separate space (toValueTypqs typq @ [string "r"]); equals])
         (separate space [string "V_record"; parens (separate space [string "List.fold_left (fun m (k, v) -> StringMap.add k v m) StringMap.empty"; (brackets (separate_map (semi ^^ space) toInterpField fields))])])
     in
     toInterpValue ^^ (twice hardline)
  | _ -> empty


let tofrominterp_def def = match def with
  | DEF_type td -> group (frominterp_typedef td ^^ twice hardline ^^ tointerp_typedef td ^^ twice hardline)
  | _ -> empty

let tofrominterp_defs name (Defs defs) =
  (string "open Sail_lib;;" ^^ hardline)
  ^^ (string "open Value;;" ^^ hardline)
  ^^ (string "open ToFromInterp_lib;;" ^^ hardline)
  ^^ (if !lem_mode then (string "open Sail2_instr_kinds;;" ^^ hardline) else empty)
  ^^ (string ("open " ^ String.capitalize_ascii name ^ ";;") ^^ hardline)
  ^^ (if !lem_mode then (string ("open " ^ String.capitalize_ascii name ^ "_types;;") ^^ hardline) else empty)
  ^^ (if !lem_mode then (string ("open " ^ String.capitalize_ascii name ^ "_extras;;") ^^ hardline) else empty)
  ^^ (string "module Big_int = Nat_big_num" ^^ ocaml_def_end)
  ^^ concat (List.map tofrominterp_def defs)

let tofrominterp_pp_defs name f defs =
  ToChannel.pretty 1. 80 f (tofrominterp_defs name defs)

let tofrominterp_output maybe_dir name defs =
  let dir = match maybe_dir with Some dir -> dir | None -> "." in
  let out_chan = open_out (Filename.concat dir (name ^ "_toFromInterp2.ml")) in
  tofrominterp_pp_defs name out_chan defs;
  close_out out_chan
