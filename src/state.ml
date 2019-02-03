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

let is_defined defs name = IdSet.mem (mk_id name) (ids_of_defs (Defs defs))

let has_default_order defs =
  List.exists (function DEF_default (DT_aux (DT_order _, _)) -> true | _ -> false) defs

let find_registers defs =
  List.fold_left
    (fun acc def ->
      match def with
      | DEF_reg_dec (DEC_aux(DEC_reg (typ, id), (_, tannot))) ->
         let env = match destruct_tannot tannot with
           | Some (env, _, _) -> env
           | _ -> Env.empty
         in
         (Env.expand_synonyms env typ, id) :: acc
      | _ -> acc
    ) [] defs

let generate_regstate = function
  | [] -> ["type regstate = unit"]
  | registers ->
     let reg (typ, id) = Printf.sprintf "%s : %s" (string_of_id id) (to_string (doc_typ typ)) in
     ["struct regstate = { " ^ (String.concat ", " (List.map reg registers)) ^ " }"]

let generate_initial_regstate defs =
  let registers = find_registers defs in
  if registers = [] then [] else
  try
    (* Recursively choose a default value for every type in the spec.
       vals, constructed below, maps user-defined types to default values. *)
    let rec lookup_init_val vals (Typ_aux (typ_aux, _) as typ) =
      match typ_aux with
      | Typ_id id ->
         if string_of_id id = "bool" then "false" else
         if string_of_id id = "bit" then "bitzero" else
         if string_of_id id = "int" then "0" else
         if string_of_id id = "nat" then "0" else
         if string_of_id id = "real" then "0" else
         if string_of_id id = "string" then "\"\"" else
         if string_of_id id = "unit" then "()" else
         Bindings.find id vals []
      | Typ_app (id, _) when string_of_id id = "list" -> "[||]"
      | Typ_app (id, [A_aux (A_nexp nexp, _)]) when string_of_id id = "atom" ->
         string_of_nexp nexp
      | Typ_app (id, [A_aux (A_nexp nexp, _); _]) when string_of_id id = "range" ->
         string_of_nexp nexp
      | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_constant len, _)), _); _ ;
                      A_aux (A_typ etyp, _)])
        when string_of_id id = "vector" ->
         (* Output a list of initial values of the vector elements, or a
            literal binary zero value if this is a bitvector and the
            environment has a default indexing order (required by the
            typechecker for binary and hex literals) *)
         let literal_bitvec = is_bit_typ etyp && has_default_order defs in
         let init_elem = if literal_bitvec then "0" else lookup_init_val vals etyp in
         let rec elems len =
           if (Nat_big_num.less_equal len Nat_big_num.zero) then [] else
           init_elem :: elems (Nat_big_num.pred len)
         in
         if literal_bitvec then "0b" ^ (String.concat "" (elems len)) else
         "[" ^ (String.concat ", " (elems len)) ^ "]"
      | Typ_app (id, args) -> Bindings.find id vals args
      | Typ_tup typs ->
         "(" ^ (String.concat ", " (List.map (lookup_init_val vals) typs)) ^ ")"
      | Typ_exist (_, _, typ) -> lookup_init_val vals typ
      | _ -> raise Not_found
    in
    let typ_subst_quant_item typ (QI_aux (qi, _)) arg = match qi with
      | QI_id (KOpt_aux (KOpt_kind (_, kid), _)) ->
         typ_subst kid arg typ
      | _ -> typ
    in
    let typ_subst_typquant tq args typ =
      List.fold_left2 typ_subst_quant_item typ (quant_items tq) args
    in
    let add_typ_init_val (defs', vals) = function
      | TD_enum (id, _, id1 :: _, _) ->
         (* Choose the first value of an enumeration type as default *)
         (defs', Bindings.add id (fun _ -> string_of_id id1) vals)
      | TD_variant (id, _, tq, (Tu_aux (Tu_ty_id (typ1, id1), _)) :: _, _) ->
         (* Choose the first variant of a union type as default *)
         let init_val args =
           let typ1 = typ_subst_typquant tq args typ1 in
           string_of_id id1 ^ " (" ^ lookup_init_val vals typ1 ^ ")"
         in
         (defs', Bindings.add id init_val vals)
      | TD_abbrev (id, tq, A_aux (A_typ typ, _)) ->
         let init_val args = lookup_init_val vals (typ_subst_typquant tq args typ) in
         (defs', Bindings.add id init_val vals)
      | TD_record (id, _, tq, fields, _) ->
         let init_val args =
           let init_field (typ, id) =
             let typ = typ_subst_typquant tq args typ in
             string_of_id id ^ " = " ^ lookup_init_val vals typ
           in
           "struct { " ^ (String.concat ", " (List.map init_field fields)) ^ " }"
         in
         let def_name = "initial_" ^ string_of_id id in
         if quant_items tq = [] && not (is_defined defs def_name) then
           (defs' @ ["let " ^ def_name ^ " : " ^ string_of_id id ^ " = " ^ init_val []],
            Bindings.add id (fun _ -> def_name) vals)
         else (defs', Bindings.add id init_val vals)
      | TD_bitfield (id, typ, _) ->
         (defs', Bindings.add id (fun _ -> lookup_init_val vals typ) vals)
      | _ -> (defs', vals)
    in
    let (init_defs, init_vals) = List.fold_left (fun inits def -> match def with
      | DEF_type (TD_aux (td, _)) -> add_typ_init_val inits td
      | _ -> inits) ([], Bindings.empty) defs
    in
    let init_reg (typ, id) = string_of_id id ^ " = " ^ lookup_init_val init_vals typ in
    init_defs @
    ["let initial_regstate : regstate = struct { " ^ (String.concat ", " (List.map init_reg registers)) ^ " }"]
  with
  | _ -> [] (* Do not generate an initial register state if anything goes wrong *)

let rec regval_constr_id mwords (Typ_aux (t, l) as typ) = match t with
  | Typ_id id -> id
  | Typ_app (id, args) ->
     let name_arg (A_aux (targ, _)) = match targ with
       | A_typ targ -> string_of_id (regval_constr_id mwords targ)
       | A_nexp nexp when is_nexp_constant (nexp_simp nexp) ->
          string_of_nexp (nexp_simp nexp)
       | A_order (Ord_aux (Ord_inc, _)) -> "inc"
       | A_order (Ord_aux (Ord_dec, _)) -> "dec"
       | _ ->
          raise (Reporting.err_typ l "Unsupported register type")
     in
     let builtins = IdSet.of_list (List.map mk_id ["vector"; "list"; "option"]) in
     if IdSet.mem id builtins && not (mwords && is_bitvector_typ typ) then id else
     append_id id (String.concat "_" ("" :: List.map name_arg args))
  | _ -> raise (Reporting.err_typ l "Unsupported register type")

let register_base_types mwords typs =
  let rec add_base_typs typs (Typ_aux (t, _) as typ) =
    let builtins = IdSet.of_list (List.map mk_id ["vector"; "list"; "option"]) in
    match t with
      | Typ_app (id, args)
        when IdSet.mem id builtins && not (mwords && is_bitvector_typ typ) ->
         let add_typ_arg base_typs (A_aux (targ, _)) =
           match targ with
             | A_typ typ -> add_base_typs typs typ
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

let add_regval_conv id typ (Defs defs) =
  let id = string_of_id id in
  let typ_str = to_string (doc_typ typ) in
  (* Create a function that converts from regval to the target type. *)
  let from_name = id ^ "_of_regval" in
  let from_val = Printf.sprintf "val %s : register_value -> option(%s)" from_name typ_str in
  let from_function = String.concat "\n" [
    Printf.sprintf "function %s Regval_%s(v) = Some(v)" from_name id;
    Printf.sprintf "and %s _ = None()" from_name
    ] in
  let from_defs = if is_defined defs from_name then [] else [from_val; from_function] in
  (* Create a function that converts from target type to regval. *)
  let to_name = "regval_of_" ^ id in
  let to_val = Printf.sprintf "val %s : %s -> register_value" to_name typ_str in
  let to_function = Printf.sprintf "function %s v = Regval_%s(v)" to_name id in
  let to_defs = if is_defined defs to_name then [] else [to_val; to_function] in
  let cdefs = concat_ast (List.map defs_of_string (from_defs @ to_defs)) in
  append_ast (Defs defs) cdefs

let rec regval_convs_lem mwords (Typ_aux (t, _) as typ) = match t with
  | Typ_app _ when is_vector_typ typ && not (mwords && is_bitvector_typ typ) ->
     let size, ord, etyp = vector_typ_args_of typ in
     let size = string_of_nexp (nexp_simp size) in
     let is_inc = if is_order_inc ord then "true" else "false" in
     let etyp_of, of_etyp = regval_convs_lem mwords etyp in
     "(fun v -> vector_of_regval " ^ etyp_of ^ " v)",
     "(fun v -> regval_of_vector " ^ of_etyp ^ " " ^ size ^ " " ^ is_inc ^ " v)"
  | Typ_app (id, [A_aux (A_typ etyp, _)])
    when string_of_id id = "list" ->
     let etyp_of, of_etyp = regval_convs_lem mwords etyp in
     "(fun v -> list_of_regval " ^ etyp_of ^ " v)",
     "(fun v -> regval_of_list " ^ of_etyp ^ " v)"
  | Typ_app (id, [A_aux (A_typ etyp, _)])
    when string_of_id id = "option" ->
     let etyp_of, of_etyp = regval_convs_lem mwords etyp in
     "(fun v -> option_of_regval " ^ etyp_of ^ " v)",
     "(fun v -> regval_of_option " ^ of_etyp ^ " v)"
  | _ ->
     let id = string_of_id (regval_constr_id mwords typ) in
     "(fun v -> " ^ id ^ "_of_regval v)", "(fun v -> regval_of_" ^ id ^ " v)"

let register_refs_lem mwords registers =
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
      "  | Regval_option v -> Just (Maybe.bind v of_regval)";
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
    (* let field = if prefix_recordtype then string "regstate_" ^^ idd else idd in *)
    let of_regval, regval_of = regval_convs_lem mwords typ in
    concat [string "let "; idd; string "_ref = <|"; hardline;
      string "  name = \""; idd; string "\";"; hardline;
      string "  read_from = (fun s -> s."; idd; string ");"; hardline;
      string "  write_to = (fun v s -> (<| s with "; idd; string " = v |>));"; hardline;
      string "  of_regval = "; string of_regval; string ";"; hardline;
      string "  regval_of = "; string regval_of; string " |>"; hardline]
  in
  let refs = separate_map hardline register_ref registers in
  let get_set_reg (_, id) =
    let idd = string_of_id id in
    string ("  if reg_name = \"" ^ idd ^ "\" then Just (" ^ idd ^ "_ref.regval_of (" ^ idd ^ "_ref.read_from s)) else"),
    string ("  if reg_name = \"" ^ idd ^ "\" then Maybe.map (fun v -> " ^ idd ^ "_ref.write_to v s) (" ^ idd ^ "_ref.of_regval v) else")
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
    string "let register_accessors = (get_regval, set_regval)" ^^ hardline ^^ hardline
    (* string "let liftS s = liftState register_accessors s" ^^ hardline *)
  in
  separate hardline [generic_convs; refs; getters_setters]

(* TODO Generate well-typedness predicate for register states (and events),
   asserting that all lists representing non-bit-vectors have the right length. *)

let generate_isa_lemmas mwords (Defs defs : tannot defs) =
  let rec drop_while f = function
    | x :: xs when f x -> drop_while f xs
    | xs -> xs
  in
  let remove_leading_underscores str =
    String.concat "_" (drop_while (fun s -> s = "") (Util.split_on_char '_' str))
  in
  let remove_trailing_underscores str =
    Util.split_on_char '_' str |> List.rev |>
    drop_while (fun s -> s = "") |> List.rev |>
    String.concat "_"
  in
  let registers = find_registers defs in
  let regtyp_ids =
    register_base_types mwords (List.map fst registers)
    |> Bindings.bindings |> List.map fst
  in
  let register_defs =
    let reg_id id = remove_leading_underscores (string_of_id id) in
    hang 2 (flow_map (break 1) string
      (["lemmas register_defs"; "="; "get_regval_def"; "set_regval_def"] @
      (List.map (fun (typ, id) -> reg_id id ^ "_ref_def") registers)))
  in
  let conv_lemma typ_id =
    let typ_id = remove_trailing_underscores (string_of_id typ_id) in
    let typ_id' = remove_leading_underscores typ_id in
    string ("lemma regval_" ^ typ_id ^ "[simp]:") ^^ hardline ^^
    string ("  \"" ^ typ_id' ^ "_of_regval (regval_of_" ^ typ_id ^ " v) = Some v\"") ^^ hardline ^^
    string ("  by (auto simp: regval_of_" ^ typ_id ^ "_def)")
  in
  let register_lemmas (typ, id) =
    let id = remove_leading_underscores (string_of_id id) in
    let id' = remove_trailing_underscores id in
    separate_map hardline string [
      "lemma liftS_read_reg_" ^ id ^ "[liftState_simp]:";
      "  \"\\<lbrakk>read_reg " ^ id ^ "_ref\\<rbrakk>\\<^sub>S = readS (" ^ id' ^ " \\<circ> regstate)\"";
      "  by (auto simp: liftState_read_reg_readS register_defs)";
      "";
      "lemma liftS_write_reg_" ^ id ^ "[liftState_simp]:";
      "  \"\\<lbrakk>write_reg " ^ id ^ "_ref v\\<rbrakk>\\<^sub>S = updateS (regstate_update (" ^ id' ^ "_update (\\<lambda>_. v)))\"";
      "  by (auto simp: liftState_write_reg_updateS register_defs)"
    ]
  in
  string "abbreviation liftS (\"\\<lbrakk>_\\<rbrakk>\\<^sub>S\") where \"liftS \\<equiv> liftState (get_regval, set_regval)\"" ^^
  hardline ^^ hardline ^^
  register_defs ^^
  hardline ^^ hardline ^^
  separate_map (hardline ^^ hardline) conv_lemma regtyp_ids ^^
  hardline ^^ hardline ^^
  separate_map hardline string [
    "lemma vector_of_rv_rv_of_vector[simp]:";
    "  assumes \"\\<And>v. of_rv (rv_of v) = Some v\"";
    "  shows \"vector_of_regval of_rv (regval_of_vector rv_of len is_inc v) = Some v\"";
    "proof -";
    "  from assms have \"of_rv \\<circ> rv_of = Some\" by auto";
    "  then show ?thesis by (auto simp: vector_of_regval_def regval_of_vector_def)";
    "qed";
    "";
    "lemma option_of_rv_rv_of_option[simp]:";
    "  assumes \"\\<And>v. of_rv (rv_of v) = Some v\"";
    "  shows \"option_of_regval of_rv (regval_of_option rv_of v) = Some v\"";
    "  using assms by (cases v) (auto simp: option_of_regval_def regval_of_option_def)";
    "";
    "lemma list_of_rv_rv_of_list[simp]:";
    "  assumes \"\\<And>v. of_rv (rv_of v) = Some v\"";
    "  shows \"list_of_regval of_rv (regval_of_list rv_of v) = Some v\"";
    "proof -";
    "  from assms have \"of_rv \\<circ> rv_of = Some\" by auto";
    "  with assms show ?thesis by (induction v) (auto simp: list_of_regval_def regval_of_list_def)";
    "qed"] ^^
  hardline ^^ hardline ^^
  separate_map (hardline ^^ hardline) register_lemmas registers

let rec regval_convs_coq (Typ_aux (t, _) as typ) = match t with
  | Typ_app _ when is_vector_typ typ && not (is_bitvector_typ typ) ->
     let size, ord, etyp = vector_typ_args_of typ in
     let size = string_of_nexp (nexp_simp size) in
     let is_inc = if is_order_inc ord then "true" else "false" in
     let etyp_of, of_etyp = regval_convs_coq etyp in
     "(fun v => vector_of_regval " ^ size ^ " " ^ etyp_of ^ " v)",
     "(fun v => regval_of_vector " ^ of_etyp ^ " " ^ size ^ " " ^ is_inc ^ " v)"
  | Typ_app (id, [A_aux (A_typ etyp, _)])
    when string_of_id id = "list" ->
     let etyp_of, of_etyp = regval_convs_coq etyp in
     "(fun v => list_of_regval " ^ etyp_of ^ " v)",
     "(fun v => regval_of_list " ^ of_etyp ^ " v)"
  | Typ_app (id, [A_aux (A_typ etyp, _)])
    when string_of_id id = "option" ->
     let etyp_of, of_etyp = regval_convs_coq etyp in
     "(fun v => option_of_regval " ^ etyp_of ^ " v)",
     "(fun v => regval_of_option " ^ of_etyp ^ " v)"
  | _ ->
     let id = string_of_id (regval_constr_id true typ) in
     "(fun v => " ^ id ^ "_of_regval v)", "(fun v => regval_of_" ^ id ^ " v)"

let register_refs_coq registers =
  let generic_convs =
    separate_map hardline string [
      "Definition vector_of_regval {a} n (of_regval : register_value -> option a) (rv : register_value) : option (vec a n) := match rv with";
      "  | Regval_vector (n', _, v) => if n =? n' then map_bind (vec_of_list n) (just_list (List.map of_regval v)) else None";
      "  | _ => None";
      "end.";
      "";
      "Definition regval_of_vector {a} (regval_of : a -> register_value) (size : Z) (is_inc : bool) (xs : vec a size) : register_value := Regval_vector (size, is_inc, List.map regval_of (list_of_vec xs)).";
      "";
      "Definition list_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (list a) := match rv with";
      "  | Regval_list v => just_list (List.map of_regval v)";
      "  | _ => None";
      "end.";
      "";
      "Definition regval_of_list {a} (regval_of : a -> register_value) (xs : list a) : register_value := Regval_list (List.map regval_of xs).";
      "";
      "Definition option_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (option a) := match rv with";
      "  | Regval_option v => option_map of_regval v";
      "  | _ => None";
      "end.";
      "";
      "Definition regval_of_option {a} (regval_of : a -> register_value) (v : option a) := Regval_option (option_map regval_of v).";
      "";
      ""
    ]
  in
  let register_ref (typ, id) =
    let idd = string (string_of_id id) in
    (* let field = if prefix_recordtype then string "regstate_" ^^ idd else idd in *)
    let of_regval, regval_of = regval_convs_coq typ in
    concat [string "Definition "; idd; string "_ref := {|"; hardline;
      string "  name := \""; idd; string "\";"; hardline;
      string "  read_from := (fun s => s.("; idd; string "));"; hardline;
      string "  write_to := (fun v s => ({[ s with "; idd; string " := v ]}));"; hardline;
      string "  of_regval := "; string of_regval; string ";"; hardline;
      string "  regval_of := "; string regval_of; string " |}."; hardline]
  in
  let refs = separate_map hardline register_ref registers in
  let get_set_reg (_, id) =
    let idd = string_of_id id in
    string ("  if string_dec reg_name \"" ^ idd ^ "\" then Some (" ^ idd ^ "_ref.(regval_of) (" ^ idd ^ "_ref.(read_from) s)) else"),
    string ("  if string_dec reg_name \"" ^ idd ^ "\" then option_map (fun v => " ^ idd ^ "_ref.(write_to) v s) (" ^ idd ^ "_ref.(of_regval) v) else")
  in
  let getters_setters =
    let getters, setters = List.split (List.map get_set_reg registers) in
    string "Local Open Scope string." ^^ hardline ^^
    string "Definition get_regval (reg_name : string) (s : regstate) : option register_value :=" ^^ hardline ^^
    separate hardline getters ^^ hardline ^^
    string "  None." ^^ hardline ^^ hardline ^^
    string "Definition set_regval (reg_name : string) (v : register_value) (s : regstate) : option regstate :=" ^^ hardline ^^
    separate hardline setters ^^ hardline ^^
    string "  None." ^^ hardline ^^ hardline ^^
    string "Definition register_accessors := (get_regval, set_regval)." ^^ hardline ^^ hardline
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
  let regtyps = register_base_types mwords (List.map fst registers) in
  let option_typ =
    if is_defined defs "option" then [] else
      ["union option ('a : Type) = {None : unit, Some : 'a}"]
  in
  let regval_typ = if is_defined defs "register_value" then [] else generate_regval_typ regtyps in
  let regstate_typ = if is_defined defs "regstate" then [] else generate_regstate registers in
  let initregstate = if is_defined defs "initial_regstate" then [] else generate_initial_regstate defs in
  let defs =
    option_typ @ regval_typ @ regstate_typ @ initregstate
    |> List.map defs_of_string
    |> concat_ast
    |> Bindings.fold add_regval_conv regtyps
  in
  Initial_check.opt_undefined_gen := gen_undef;
  defs

let add_regstate_defs mwords env (Defs defs) =
  let reg_defs, env = Type_error.check env (generate_regstate_defs mwords defs) in
  env, append_ast (Defs defs) reg_defs
