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

module Big_int = Nat_big_num

open Initial_check
open Type_check
open Ast
open Ast_util
open PPrint
open Pretty_print_common
open Pretty_print_sail

let defs_of_string = ast_of_def_string Ast_util.inc_ord

let find_registers defs =
  List.fold_left
    (fun acc def ->
      match def with
      | DEF_reg_dec (DEC_aux(DEC_reg (typ, id), annot)) ->
         let env = match annot with
           | (_, Some (env, _, _)) -> env
           | _ -> Env.empty
         in
         (Env.expand_synonyms env typ, id) :: acc
      | _ -> acc
    ) [] defs

let generate_regstate = function
  | [] -> ["type regstate = unit"]
  | registers ->
     let reg (typ, id) = Printf.sprintf "%s : %s" (string_of_id id) (to_string (doc_typ typ)) in
     let initreg (_, id) = Printf.sprintf "%s = undefined" (string_of_id id) in
     let regstate =
       "struct regstate = { " ^
       (String.concat ", " (List.map reg registers)) ^
       " }"
     in
     let initstate =
       "let initial_regstate : regstate = struct { " ^
       (String.concat ", " (List.map initreg registers)) ^
       " }"
     in
     regstate :: (if !Initial_check.opt_undefined_gen then [initstate] else [])

let rec regval_constr_id mwords (Typ_aux (t, l) as typ) = match t with
  | Typ_id id -> id
  | Typ_app (id, args) ->
     let name_arg (Typ_arg_aux (targ, _)) = match targ with
       | Typ_arg_typ targ -> string_of_id (regval_constr_id mwords targ)
       | Typ_arg_nexp nexp when is_nexp_constant (nexp_simp nexp) ->
          string_of_nexp (nexp_simp nexp)
       | Typ_arg_order (Ord_aux (Ord_inc, _)) -> "inc"
       | Typ_arg_order (Ord_aux (Ord_dec, _)) -> "dec"
       | _ ->
          raise (Reporting_basic.err_typ l "Unsupported register type")
     in
     let builtins = IdSet.of_list (List.map mk_id ["vector"; "list"; "option"]) in
     if IdSet.mem id builtins && not (mwords && is_bitvector_typ typ) then id else
     append_id id (String.concat "_" ("" :: List.map name_arg args))
  | _ -> raise (Reporting_basic.err_typ l "Unsupported register type")

let register_base_types mwords typs =
  let rec add_base_typs typs (Typ_aux (t, _) as typ) =
    let builtins = IdSet.of_list (List.map mk_id ["vector"; "list"; "option"]) in
    match t with
      | Typ_app (id, args)
        when IdSet.mem id builtins && not (mwords && is_bitvector_typ typ) ->
         let add_typ_arg base_typs (Typ_arg_aux (targ, _)) =
           match targ with
             | Typ_arg_typ typ -> add_base_typs typs typ
             | _ -> typs
         in
         List.fold_left add_typ_arg typs args
      | _ -> Bindings.add (regval_constr_id mwords typ) typ typs
  in
  List.fold_left add_base_typs Bindings.empty typs

let generate_regval_typ typs =
  let constr (constr_id, typ) =
    Printf.sprintf "Regval_%s : %s" (string_of_id constr_id) (to_string (doc_typ typ)) in
  let builtins =
    "Regval_vector : (int, bool, list(register_value)), " ^
    "Regval_list : list(register_value), " ^
    "Regval_option : option(register_value)"
  in
  ["union register_value = { " ^
  (String.concat ", " (builtins :: List.map constr (Bindings.bindings typs))) ^
  " }"]

let add_regval_conv id typ defs =
  let id = string_of_id id in
  let is_defined name = IdSet.mem (mk_id name) (ids_of_defs defs) in
  let typ_str = to_string (doc_typ typ) in
  (* Create a function that converts from regval to the target type. *)
  let from_name = id ^ "_of_regval" in
  let from_val = Printf.sprintf "val %s : register_value -> option(%s)" from_name typ_str in
  let from_function = String.concat "\n" [
    Printf.sprintf "function %s Regval_%s(v) = Some(v)" from_name id;
    Printf.sprintf "and %s _ = None" from_name
    ] in
  let from_defs = if is_defined from_name then [] else [from_val; from_function] in
  (* Create a function that converts from target type to regval. *)
  let to_name = "regval_of_" ^ id in
  let to_val = Printf.sprintf "val %s : %s -> register_value" to_name typ_str in
  let to_function = Printf.sprintf "function %s v = Regval_%s(v)" to_name id in
  let to_defs = if is_defined to_name then [] else [to_val; to_function] in
  let cdefs = concat_ast (List.map defs_of_string (from_defs @ to_defs)) in
  append_ast defs cdefs

let rec regval_convs_lem mwords (Typ_aux (t, _) as typ) = match t with
  | Typ_app _ when is_vector_typ typ && not (mwords && is_bitvector_typ typ) ->
     let _, size, ord, etyp = vector_typ_args_of typ in
     let size = string_of_nexp (nexp_simp size) in
     let is_inc = if is_order_inc ord then "true" else "false" in
     let etyp_of, of_etyp = regval_convs_lem mwords etyp in
     "(fun v -> vector_of_regval " ^ etyp_of ^ " v)",
     "(fun v -> regval_of_vector " ^ of_etyp ^ " " ^ size ^ " " ^ is_inc ^ " v)"
  | Typ_app (id, [Typ_arg_aux (Typ_arg_typ etyp, _)])
    when string_of_id id = "list" ->
     let etyp_of, of_etyp = regval_convs_lem mwords etyp in
     "(fun v -> list_of_regval " ^ etyp_of ^ " v)",
     "(fun v -> regval_of_list " ^ of_etyp ^ " v)"
  | Typ_app (id, [Typ_arg_aux (Typ_arg_typ etyp, _)])
    when string_of_id id = "option" ->
     let etyp_of, of_etyp = regval_convs_lem mwords etyp in
     "(fun v -> option_of_regval " ^ etyp_of ^ " v)",
     "(fun v -> regval_of_option " ^ of_etyp ^ " v)"
  | _ ->
     let id = string_of_id (regval_constr_id mwords typ) in
     "(fun v -> " ^ id ^ "_of_regval v)", "(fun v -> regval_of_" ^ id ^ " v)"

let register_refs_lem prefix_recordtype mwords registers =
  let generic_convs =
    separate_map hardline string [
      "val vector_of_regval : forall 'a. (register_value -> maybe 'a) -> register_value -> maybe (list 'a)";
      "let vector_of_regval of_regval = function";
      "  | Regval_vector (_, _, v) -> just_list (List.map of_regval v)";
      "  | _ -> Nothing";
      "end";
      "";
      "val regval_of_vector : forall 'a. ('a -> register_value) -> integer -> bool -> list 'a -> register_value";
      "let regval_of_vector regval_of size is_inc xs = Regval_vector (size, is_inc, List.map regval_of xs)";
      "";
      "val list_of_regval : forall 'a. (register_value -> maybe 'a) -> register_value -> maybe (list 'a)";
      "let list_of_regval of_regval = function";
      "  | Regval_list v -> just_list (List.map of_regval v)";
      "  | _ -> Nothing";
      "end";
      "";
      "val regval_of_list : forall 'a. ('a -> register_value) -> list 'a -> register_value";
      "let regval_of_list regval_of xs = Regval_list (List.map regval_of xs)";
      "";
      "val option_of_regval : forall 'a. (register_value -> maybe 'a) -> register_value -> maybe (maybe 'a)";
      "let option_of_regval of_regval = function";
      "  | Regval_option v -> Maybe.map of_regval v";
      "  | _ -> Nothing";
      "end";
      "";
      "val regval_of_option : forall 'a. ('a -> register_value) -> maybe 'a -> register_value";
      "let regval_of_option regval_of v = Regval_option (Maybe.map regval_of v)";
      "";
      ""
    ]
  in
  let register_ref (typ, id) =
    let idd = string (string_of_id id) in
    let field = if prefix_recordtype then string "regstate_" ^^ idd else idd in
    let of_regval, regval_of = regval_convs_lem mwords typ in
    concat [string "let "; idd; string " = <|"; hardline;
      string "  name = \""; idd; string "\";"; hardline;
      string "  read_from = (fun s -> s."; field; string ");"; hardline;
      string "  write_to = (fun s v -> (<| s with "; field; string " = v |>));"; hardline;
      string "  of_regval = "; string of_regval; string ";"; hardline;
      string "  regval_of = "; string regval_of; string " |>"; hardline]
  in
  let refs = separate_map hardline register_ref registers in
  let get_set_reg (_, id) =
    let idd = string_of_id id in
    string ("  if reg_name = \"" ^ idd ^ "\" then Just (" ^ idd ^ ".regval_of (" ^ idd ^ ".read_from s)) else"),
    string ("  if reg_name = \"" ^ idd ^ "\" then Maybe.map (" ^ idd ^ ".write_to s) (" ^ idd ^ ".of_regval v) else")
  in
  let getters_setters =
    let getters, setters = List.split (List.map get_set_reg registers) in
    string "val get_regval : string -> regstate -> maybe register_value" ^^ hardline ^^
    string "let get_regval reg_name s =" ^^ hardline ^^
    separate hardline getters ^^ hardline ^^
    string "  Nothing" ^^ hardline ^^ hardline ^^
    string "val set_regval : string -> register_value -> regstate -> maybe regstate" ^^ hardline ^^
    string "let set_regval reg_name v s =" ^^ hardline ^^
    separate hardline setters ^^ hardline ^^
    string "  Nothing" ^^ hardline ^^ hardline ^^
    string "let register_accessors = (get_regval, set_regval)" ^^ hardline ^^ hardline ^^
    string "let liftS s = liftState register_accessors s" ^^ hardline
  in
  separate hardline [generic_convs; refs; getters_setters]

let generate_regstate_defs mwords defs =
  (* FIXME We currently don't want to generate undefined_type functions
     for register state and values.  For the Lem backend, this would require
     taking the dependencies of those functions into account when partitioning
     definitions into the different lem files, which we currently don't do. *)
  let gen_undef = !Initial_check.opt_undefined_gen in
  Initial_check.opt_undefined_gen := false;
  let registers = find_registers defs in
  let def_ids = ids_of_defs (Defs defs) in
  let has_def name = IdSet.mem (mk_id name) def_ids in
  let regtyps = register_base_types mwords (List.map fst registers) in
  let option_typ =
    if has_def "option" then [] else
      ["union option ('a : Type) = {None, Some : 'a}"]
  in
  let regval_typ = if has_def "register_value" then [] else generate_regval_typ regtyps in
  let regstate_typ = if has_def "regstate" then [] else generate_regstate registers in
  let defs =
    option_typ @ regval_typ @ regstate_typ
    |> List.map defs_of_string
    |> concat_ast
    |> Bindings.fold add_regval_conv regtyps
  in
  Initial_check.opt_undefined_gen := gen_undef;
  defs

let add_regstate_defs mwords env (Defs defs) =
  let reg_defs, env = check env (generate_regstate_defs mwords defs) in
  env, append_ast (Defs defs) reg_defs
