open Libsail

open Type_check
open Ast
open Ast_defs
open Ast_util
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

(* Command line options *)
let opt_extern_types : string list ref = ref []

type global_context = { effect_info : Effects.side_effect_info }

let the_main_function_has_been_seen = ref false

let remove_empties (docs : document list) = List.filter (fun d -> d != empty) docs

type context = {
  global : global_context;
  env : Type_check.env;
      (** The typechecking environment of the current function. This environment is reset using [initial_context] when
          we start processing a new function.  *)
  kid_id_renames : id option KBindings.t;
      (** Associates a kind variable to the corresponding argument of the function, used for implicit arguments. *)
  kid_id_renames_rev : kid Bindings.t;  (** Inverse of the [kid_id_renames] mapping. *)
}

let context_init env global = { global; env; kid_id_renames = KBindings.empty; kid_id_renames_rev = Bindings.empty }
let context_with_env ctx env = { ctx with env }

let add_single_kid_id_rename ctx id kid =
  let kir =
    match Bindings.find_opt id ctx.kid_id_renames_rev with
    | Some kid -> KBindings.add kid None ctx.kid_id_renames
    | None -> ctx.kid_id_renames
  in
  {
    ctx with
    kid_id_renames = KBindings.add kid (Some id) kir;
    kid_id_renames_rev = Bindings.add id kid ctx.kid_id_renames_rev;
  }

let implicit_parens x = enclose (string "{") (string "}") x

let rec fix_id name =
  match name with
  (* Lean keywords to avoid, to expand as needed *)
  | "rec" -> name ^ "'"
  | "def" -> name ^ "'"
  | "main" ->
      the_main_function_has_been_seen := true;
      "sail_main"
  | _ -> if String.contains name '#' then fix_id (String.concat "_" (Util.split_on_char '#' name)) else name

let doc_id_ctor (Id_aux (i, _)) =
  match i with Id i -> string (fix_id i) | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_kid ctx (Kid_aux (Var x, _) as ki) =
  match KBindings.find_opt ki ctx.kid_id_renames with
  | Some (Some i) -> doc_id_ctor i
  | _ -> string ("k_" ^ String.sub x 1 (String.length x - 1))

(* TODO do a proper renaming and keep track of it *)

let is_enum env id = match Env.lookup_id id env with Enum _ -> true | _ -> false

let pat_is_plain_binder env (P_aux (p, _)) =
  match p with
  | P_id id when not (is_enum env id) -> Some (Some id, None)
  | P_typ (typ, P_aux (P_id id, _)) when not (is_enum env id) -> Some (Some id, Some typ)
  | P_wild | P_typ (_, P_aux (P_wild, _)) -> Some (None, None)
  | P_var (_, _) -> Some (Some (Id_aux (Id "var", Unknown)), None)
  | P_app (_, _) -> Some (Some (Id_aux (Id "app", Unknown)), None)
  | P_vector _ -> Some (Some (Id_aux (Id "vect", Unknown)), None)
  | P_tuple _ -> Some (Some (Id_aux (Id "tuple", Unknown)), None)
  | P_list _ -> Some (Some (Id_aux (Id "list", Unknown)), None)
  | P_cons (_, _) -> Some (Some (Id_aux (Id "cons", Unknown)), None)
  | P_lit (L_aux (L_unit, _)) -> Some (Some (Id_aux (Id "_", Unknown)), None)
  | P_lit _ -> Some (Some (Id_aux (Id "lit", Unknown)), None)
  | _ -> None

(* Copied from the Coq PP *)
let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    ((P_aux (P_id id, (l, mk_tannot env typ)), typ), E_aux (E_id id, (l, mk_tannot env typ)))
  in
  List.split (List.mapi arg typs)

(* Copied from the Coq PP *)
(* Sail currently has a single pattern to match against a list of
   argument types.  We need to tweak everything to match up,
   especially so that the function is presented in curried form.  In
   particular, if there's a single binder for multiple arguments
   (which rewriting can currently introduce) then we need to turn it
   into multiple binders and reconstruct it in the function body using
   the second return value of this function. *)
let rec untuple_args_pat typs (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let identity body = body in
  match (paux, typs) with
  | P_tuple [], _ | P_lit (L_aux (L_unit, _)), _ ->
      let annot = (l, mk_tannot Env.empty unit_typ) in
      ([(P_aux (P_lit (mk_lit L_unit), annot), unit_typ)], identity)
  (* The type checker currently has a special case for a single arg type; if
     that is removed, then remove the next case. *)
  | P_tuple pats, [typ] -> ([(pat, typ)], identity)
  | P_tuple pats, _ -> (List.combine pats typs, identity)
  | P_wild, _ ->
      let wild typ = (P_aux (P_wild, (l, mk_tannot env typ)), typ) in
      (List.map wild typs, identity)
  | P_typ (_, pat), _ -> untuple_args_pat typs pat
  | P_as _, _ :: _ :: _ | P_id _, _ :: _ :: _ ->
      let argpats, argexps = args_of_typ l env typs in
      let argexp = E_aux (E_tuple argexps, annot) in
      let bindargs (E_aux (_, bannot) as body) = E_aux (E_let (LB_aux (LB_val (pat, argexp), annot), body), bannot) in
      (argpats, bindargs)
  | _, [typ] -> ([(pat, typ)], identity)
  | _, _ -> unreachable l __POS__ "Unexpected pattern/type combination"

let string_of_nexp_con (Nexp_aux (n, l)) =
  match n with
  | Nexp_constant _ -> "NExp_constant"
  | Nexp_id _ -> "Nexp_id"
  | Nexp_var _ -> "Nexp_var"
  | Nexp_app _ -> "Nexp_app"
  | Nexp_if _ -> "Nexp_if"
  | Nexp_times _ -> "Nexp_times"
  | Nexp_sum _ -> "Nexp_sum"
  | Nexp_minus _ -> "Nexp_minus"
  | Nexp_neg _ -> "Nexp_neg"
  | Nexp_exp _ -> "Nexp_exp"

let string_of_typ_con (Typ_aux (t, _)) =
  match t with
  | Typ_app _ -> "Typ_app"
  | Typ_var _ -> "Typ_var"
  | Typ_fn _ -> "Typ_fn"
  | Typ_tuple _ -> "Typ_tuple"
  | Typ_exist _ -> "Typ_exist"
  | Typ_bidir _ -> "Typ_bidir"
  | Typ_internal_unknown -> "Typ_internal_unknown"
  | Typ_id _ -> "Typ_id"

let doc_big_int i = if i >= Z.zero then string (Big_int.to_string i) else parens (string (Big_int.to_string i))

let is_unit t = match t with Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true | _ -> false

(* Adapted from Coq PP *)
let rec doc_nexp ctx (Nexp_aux (n, l) as nexp) =
  let rec plussub (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_sum (n1, n2) -> separate space [plussub n1; plus; mul n2]
    | Nexp_minus (n1, n2) -> separate space [plussub n1; minus; mul n2]
    | _ -> mul nexp
  and mul (Nexp_aux (n, l) as nexp) =
    match n with Nexp_times (n1, n2) -> separate space [mul n1; star; uneg n2] | _ -> uneg nexp
  and uneg (Nexp_aux (n, l) as nexp) =
    match n with Nexp_neg n -> parens (separate space [minus; uneg n]) | _ -> exp nexp
  and exp (Nexp_aux (n, l) as nexp) =
    match n with Nexp_exp n -> separate space [string "2"; caret; exp n] | _ -> app nexp
  and app (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_if (i, t, e) ->
        separate space [string "if"; doc_nconstraint ctx i; string "then"; atomic t; string "else"; atomic e]
    | Nexp_app (Id_aux (Id "div", _), [n1; n2]) -> separate space [atomic n1; string "/"; atomic n2]
    | Nexp_app (Id_aux (Id "mod", _), [n1; n2]) -> separate space [atomic n1; string "%"; atomic n2]
    | Nexp_app (Id_aux (Id "abs", _), [n1]) -> separate dot [atomic n1; string "natAbs"]
    | _ -> atomic nexp
  and atomic (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_constant i -> doc_big_int i
    | Nexp_var ki -> doc_kid ctx ki
    | Nexp_id id -> doc_id_ctor id
    | Nexp_sum _ | Nexp_minus _ | Nexp_times _ | Nexp_neg _ | Nexp_exp _ | Nexp_if _
    | Nexp_app (Id_aux (Id ("div" | "mod"), _), [_; _])
    | Nexp_app (Id_aux (Id "abs", _), [_]) ->
        parens (plussub nexp)
    | _ -> failwith ("NExp " ^ string_of_nexp_con nexp ^ " " ^ string_of_nexp nexp ^ " not translatable yet.")
  in
  atomic nexp

and doc_nconstraint ctx (NC_aux (nc, _)) =
  match nc with
  | NC_and (n1, n2) -> flow (break 1) [doc_nconstraint ctx n1; string "∧"; doc_nconstraint ctx n2]
  | NC_or (n1, n2) -> flow (break 1) [doc_nconstraint ctx n1; string "∨"; doc_nconstraint ctx n2]
  | NC_equal (a1, a2) -> flow (break 1) [doc_typ_arg ctx `All a1; string "="; doc_typ_arg ctx `All a2]
  | NC_not_equal (a1, a2) -> flow (break 1) [doc_typ_arg ctx `All a1; string "≠"; doc_typ_arg ctx `All a2]
  | NC_app (f, args) -> doc_id_ctor f ^^ parens (separate_map comma_sp (doc_typ_arg ctx `All) args)
  | NC_false -> string "false"
  | NC_true -> string "true"
  | NC_ge (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string "≥"; doc_nexp ctx n2]
  | NC_le (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string "≤"; doc_nexp ctx n2]
  | NC_gt (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string ">"; doc_nexp ctx n2]
  | NC_lt (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string "<"; doc_nexp ctx n2]
  | NC_id i -> doc_id_ctor i
  | NC_set (n, vs) ->
      flow (break 1)
        [
          doc_nexp ctx n;
          string "∈";
          implicit_parens (separate_map comma_sp (fun x -> string (Nat_big_num.to_string x)) vs);
        ]
  | NC_var ki -> doc_kid ctx ki

and doc_typ_arg ctx rel (A_aux (t, _)) =
  match t with
  | A_typ t -> doc_typ ctx t
  | A_nexp n -> doc_nexp ctx n
  | A_bool nc -> (
      match rel with `Only_relevant -> empty | `All -> parens (doc_nconstraint ctx nc)
    )

and provably_nneg ctx x = Type_check.prove __POS__ ctx.env (nc_gteq x (nint 0))

and doc_typ ctx (Typ_aux (t, _) as typ) =
  match t with
  | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp m, _); A_aux (A_typ elem_typ, _)]) ->
      (* TODO: remove duplication with exists, below *)
      nest 2 (parens (flow space [string "Vector"; doc_typ ctx elem_typ; doc_nexp ctx m]))
  | Typ_id (Id_aux (Id "unit", _)) -> string "Unit"
  | Typ_id (Id_aux (Id "int", _)) -> string "Int"
  | Typ_id (Id_aux (Id "string", _)) -> string "String"
  | Typ_app (Id_aux (Id "atom_bool", _), _) | Typ_id (Id_aux (Id "bool", _)) -> string "Bool"
  | Typ_id (Id_aux (Id "bit", _)) -> parens (string "BitVec 1")
  | Typ_id (Id_aux (Id "nat", _)) -> string "Nat"
  | Typ_app (Id_aux (Id "bitvector", _), [A_aux (A_nexp m, _)]) | Typ_app (Id_aux (Id "bits", _), [A_aux (A_nexp m, _)])
    ->
      parens (string "BitVec " ^^ doc_nexp ctx m)
  | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp x, _)]) -> if provably_nneg ctx x then string "Nat" else string "Int"
  | Typ_app (Id_aux (Id "register", _), t_app) ->
      parens (string "RegisterRef RegisterType " ^^ separate_map comma (doc_typ_app ctx) t_app)
  | Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]) ->
      underscore (* TODO check if the type of implicit arguments can really be always inferred *)
  | Typ_app (Id_aux (Id "option", _), [A_aux (A_typ typ, _)]) -> parens (string "Option " ^^ doc_typ ctx typ)
  | Typ_app (Id_aux (Id "list", _), args) ->
      parens (string "List" ^^ space ^^ separate_map space (doc_typ_arg ctx `Only_relevant) args)
  | Typ_tuple ts -> parens (separate_map (space ^^ string "×" ^^ space) (doc_typ ctx) ts)
  | Typ_id id -> doc_id_ctor id
  | Typ_app (Id_aux (Id "range", _), [A_aux (A_nexp low, _); A_aux (A_nexp high, _)]) ->
      if provably_nneg ctx low then string "Nat" else string "Int"
  | Typ_app (Id_aux (Id "result", _), [A_aux (A_typ typ1, _); A_aux (A_typ typ2, _)]) ->
      parens (separate space [string "Result"; doc_typ ctx typ1; doc_typ ctx typ2])
  | Typ_var kid -> doc_kid ctx kid
  | Typ_app (id, args) -> doc_id_ctor id ^^ space ^^ separate_map space (doc_typ_arg ctx `Only_relevant) args
  | Typ_exist (_, _, typ) -> doc_typ ctx typ
  | _ -> failwith ("Type " ^ string_of_typ_con typ ^ " " ^ string_of_typ typ ^ " not translatable yet.")

and doc_typ_app ctx (A_aux (t, _) as typ) =
  match t with
  | A_typ t' -> doc_typ ctx t'
  | A_bool nc -> failwith ("Constraint " ^ string_of_n_constraint nc ^ "not translatable yet.")
  | A_nexp m -> doc_nexp ctx m

let rec captured_typ_var ((i, Typ_aux (t, _)) as typ) =
  match t with
  | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)])
  | Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]) ->
      Some (i, ki)
  | _ -> None

let doc_typ_id ctx (typ, fid) = flow (break 1) [doc_id_ctor fid; colon; doc_typ ctx typ]

let doc_kind ctx (kid : kid) (K_aux (k, _)) =
  match k with
  | K_int -> if provably_nneg ctx (Nexp_aux (Nexp_var kid, Unknown)) then string "Nat" else string "Int"
  | K_bool -> string "Bool"
  | K_type -> string "Type"

let doc_quant_item_all ctx (QI_aux (qi, _)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> flow (break 1) [doc_kid ctx ki; colon; doc_kind ctx ki k]
  | QI_constraint c -> doc_nconstraint ctx c

(* Used to annotate types with the original constraints *)
let doc_typ_quant_all ctx tq = match tq with TypQ_tq qs -> List.map (doc_quant_item_all ctx) qs | TypQ_no_forall -> []

let doc_typ_quant_in_comment ctx (TypQ_aux (tq, _)) =
  let typ_quants = doc_typ_quant_all ctx tq in
  if List.length typ_quants > 0 then
    string "/-- Type quantifiers: " ^^ nest 2 (flow comma_sp typ_quants) ^^ string " -/" ^^ hardline
  else empty

let doc_quant_item_relevant ctx (QI_aux (qi, annot)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> Some (flow (break 1) [doc_kid ctx ki; colon; doc_kind ctx ki k])
  | QI_constraint c -> None

(* Used to translate type parameters of types, so we drop the constraints *)
let doc_typ_quant_relevant ctx (TypQ_aux (tq, _) as tq_full) =
  (* We go through the type variables with an environment that contains all the constraints,
     in order to detect when we can translate the Kind as Nat *)
  let ctx = context_init (Type_check.Env.add_typquant Unknown tq_full ctx.env) ctx.global in
  match tq with TypQ_tq qs -> List.filter_map (doc_quant_item_relevant ctx) qs | TypQ_no_forall -> []

let doc_quant_item_only_vars ctx (QI_aux (qi, annot)) =
  match qi with QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> Some (doc_kid ctx ki) | QI_constraint c -> None

(* Used to translate type parameters of type abbreviations *)
let doc_typ_quant_only_vars ctx (TypQ_aux (tq, _) as tq_full) =
  match tq with TypQ_tq qs -> List.filter_map (doc_quant_item_only_vars ctx) qs | TypQ_no_forall -> []

let lean_escape_string s = Str.global_replace (Str.regexp "\"") "\"\"" s

let doc_lit (L_aux (lit, l)) =
  match lit with
  | L_unit -> string "()"
  | L_zero -> string "0#1"
  | L_one -> string "1#1"
  | L_false -> string "false"
  | L_true -> string "true"
  | L_num i -> doc_big_int i
  | L_hex n -> utf8string ("0x" ^ n)
  | L_bin n -> utf8string ("0b" ^ n)
  | L_undef -> utf8string "(Fail \"undefined value of unsupported type\")"
  | L_string s -> utf8string ("\"" ^ lean_escape_string s ^ "\"")
  | L_real s -> utf8string s (* TODO test if this is really working *)

let doc_vec_lit (L_aux (lit, _) as l) =
  match lit with
  | L_zero -> string "0"
  | L_one -> string "1"
  | _ -> failwith "Unexpected litteral found in vector: " ^^ doc_lit l

let string_of_exp_con (E_aux (e, _)) =
  match e with
  | E_block _ -> "E_block"
  | E_ref _ -> "E_ref"
  | E_app_infix _ -> "E_app_infix"
  | E_if _ -> "E_if"
  | E_loop _ -> "E_loop"
  | E_for _ -> "E_for"
  | E_vector_access _ -> "E_vector_access"
  | E_vector_subrange _ -> "E_vector_subrange"
  | E_vector_update _ -> "E_vector_update"
  | E_vector_update_subrange _ -> "E_vector_update_subrange"
  | E_vector_append _ -> "E_vector_append"
  | E_list _ -> "E_list"
  | E_cons _ -> "E_cons"
  | E_struct _ -> "E_struct"
  | E_struct_update _ -> "E_struct_update"
  | E_field _ -> "E_field"
  | E_match _ -> "E_match"
  | E_assign _ -> "E_assign"
  | E_sizeof _ -> "E_sizeof"
  | E_constraint _ -> "E_constraint"
  | E_exit _ -> "E_exit"
  | E_throw _ -> "E_throw"
  | E_try _ -> "E_try"
  | E_return _ -> "E_return"
  | E_assert _ -> "E_assert"
  | E_var _ -> "E_var"
  | E_internal_plet _ -> "E_internal_plet"
  | E_internal_return _ -> "E_internal_return"
  | E_internal_assume _ -> "E_internal_assume"
  | E_internal_value _ -> "E_internal_value"
  | E_id _ -> "E_id"
  | E_lit _ -> "E_lit"
  | E_typ _ -> "E_typ"
  | E_app _ -> "E_app"
  | E_tuple _ -> "E_tuple"
  | E_vector _ -> "E_vector"
  | E_let _ -> "E_let"

let rec is_anonymous_pat (P_aux (p, _) as full_pat) =
  match p with
  | P_wild -> true
  | P_id (Id_aux (Id s, _)) -> String.sub s 0 1 = "_"
  | P_lit (L_aux _) -> true
  | P_typ (_, p) -> is_anonymous_pat p
  | _ -> false

let string_of_pat_con (P_aux (p, _)) =
  match p with
  | P_app _ -> "P_app"
  | P_wild -> "P_wild"
  | P_lit _ -> "P_lit"
  | P_or _ -> "P_or"
  | P_not _ -> "P_not"
  | P_as _ -> "P_as"
  | P_typ _ -> "P_typ"
  | P_id _ -> "P_id"
  | P_var _ -> "P_var"
  | P_vector _ -> "P_vector"
  | P_vector_concat _ -> "P_vector_concat"
  | P_vector_subrange _ -> "P_vector_subrange"
  | P_tuple _ -> "P_tuple"
  | P_list _ -> "P_list"
  | P_cons _ -> "P_cons"
  | P_string_append _ -> "P_string_append"
  | P_struct _ -> "P_struct"

let string_of_def (DEF_aux (d, _)) =
  match d with
  | DEF_type _ -> "DEF_type"
  | DEF_constraint _ -> "DEF_constraint"
  | DEF_fundef _ -> "DEF_fundef"
  | DEF_mapdef _ -> "DEF_mapdef"
  | DEF_impl _ -> "DEF_impl"
  | DEF_let _ -> "DEF_let"
  | DEF_val (VS_aux (VS_val_spec (_, id, _), _)) -> "DEF_val " ^ string_of_id id
  | DEF_outcome _ -> "DEF_outcome"
  | DEF_instantiation _ -> "DEF_instantiation"
  | DEF_fixity _ -> "DEF_fixity"
  | DEF_overload _ -> "DEF_overload"
  | DEF_default _ -> "DEF_default"
  | DEF_scattered _ -> "DEF_scattered"
  | DEF_measure _ -> "DEF_measure"
  | DEF_loop_measures _ -> "DEF_loop_measures"
  | DEF_register _ -> "DEF_register"
  | DEF_internal_mutrec _ -> "DEF_internal_mutrec"
  | DEF_pragma _ -> "DEF_pragma"

(** Fix identifiers to match the standard Lean library. *)
let fixup_match_id (Id_aux (id, l) as id') =
  match id with Id id -> Id_aux (Id (match id with "Some" -> "some" | "None" -> "none" | _ -> id), l) | _ -> id'

let rec doc_pat ?(in_vector = false) (P_aux (p, (l, annot)) as pat) =
  match p with
  | P_wild -> underscore
  | P_lit lit when in_vector -> doc_vec_lit lit
  | P_lit lit -> doc_lit lit
  | P_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _), p) when in_vector -> doc_pat p ^^ string ":1"
  | P_typ (Typ_aux (Typ_app (Id_aux (Id id, _), [A_aux (A_nexp (Nexp_aux (Nexp_constant i, _)), _)]), _), p)
    when in_vector && (id = "bits" || id = "bitvector") ->
      doc_pat p ^^ string ":" ^^ doc_big_int i
  | P_typ (ptyp, p) -> doc_pat p
  | P_id id -> fixup_match_id id |> doc_id_ctor
  | P_tuple pats -> separate (string ", ") (List.map doc_pat pats) |> parens
  | P_list pats -> separate (string ", ") (List.map doc_pat pats) |> brackets
  | P_vector pats -> concat (List.map (doc_pat ~in_vector:true) pats)
  | P_vector_concat pats -> separate (string ",") (List.map (doc_pat ~in_vector:true) pats) |> brackets
  | P_app (Id_aux (Id "None", _), p) -> string "none"
  | P_app (cons, pats) -> doc_id_ctor (fixup_match_id cons) ^^ space ^^ separate_map (string ", ") doc_pat pats
  | P_var (p, _) -> doc_pat p
  | P_as (pat, id) -> doc_pat pat
  | P_struct (pats, _) ->
      let pats = List.map (fun (id, pat) -> separate space [doc_id_ctor id; coloneq; doc_pat pat]) pats in
      braces (space ^^ separate (comma ^^ space) pats ^^ space)
  | P_cons (hd_pat, tl_pat) -> parens (separate space [doc_pat hd_pat; string "::"; doc_pat tl_pat])
  | _ -> failwith ("Doc Pattern " ^ string_of_pat_con pat ^ " " ^ string_of_pat pat ^ " not translatable yet.")

(* Copied from the Coq PP *)
let rebind_cast_pattern_vars pat typ exp =
  let rec aux pat typ =
    match (pat, typ) with
    | P_aux (P_typ (target_typ, P_aux (P_id id, (l, ann))), _), source_typ when not (is_enum (env_of exp) id) ->
        if Typ.compare target_typ source_typ == 0 then []
        else (
          let l = Parse_ast.Generated l in
          let cast_annot = Type_check.replace_typ source_typ ann in
          let e_annot = Type_check.mk_tannot (env_of exp) source_typ in
          [LB_aux (LB_val (pat, E_aux (E_id id, (l, e_annot))), (l, ann))]
        )
    | P_aux (P_tuple pats, _), Typ_aux (Typ_tuple typs, _) -> List.concat (List.map2 aux pats typs)
    | _ -> []
  in
  let add_lb (E_aux (_, ann) as exp) lb = E_aux (E_let (lb, exp), ann) in
  (* Don't introduce new bindings at the top-level, we'd just go into a loop. *)
  let lbs =
    match (pat, typ) with
    | P_aux (P_tuple pats, _), Typ_aux (Typ_tuple typs, _) -> List.concat (List.map2 aux pats typs)
    | _ -> []
  in
  List.fold_left add_lb exp lbs

let wrap_with_pure (needs_return : bool) (d : document) =
  if needs_return then parens (nest 2 (flow space [string "pure"; d])) else d

let wrap_with_left_arrow (needs_return : bool) (d : document) =
  if needs_return then parens (nest 2 (flow space [string "←"; d])) else d

let get_fn_implicits (Typ_aux (t, _)) : bool list =
  let arg_implicit arg =
    match arg with
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]), _) -> true
    | _ -> false
  in
  match t with Typ_fn (args, cod) -> List.map arg_implicit args | _ -> []

let rec is_bitvector_pattern (P_aux (pat, _)) =
  match pat with P_vector _ | P_vector_concat _ -> true | P_as (pat, _) -> is_bitvector_pattern pat | _ -> false

let match_or_match_bv brs =
  if List.exists (function Pat_aux (Pat_exp (pat, _), _) -> is_bitvector_pattern pat | _ -> false) brs then "match_bv "
  else "match "

let rec doc_match_clause (as_monadic : bool) ctx (Pat_aux (cl, l)) =
  match cl with
  | Pat_exp (pat, branch) ->
      group (nest 2 (string "| " ^^ doc_pat pat ^^ string " =>" ^^ break 1 ^^ doc_exp as_monadic ctx branch))
  | Pat_when (pat, when_, branch) -> failwith "The Lean backend does not support 'when' clauses in patterns"

and doc_exp (as_monadic : bool) ctx (E_aux (e, (l, annot)) as full_exp) =
  let env = env_of_tannot annot in
  let d_of_arg arg =
    let arg_monadic = effectful (effect_of arg) in
    let wrap = match arg with E_aux (E_let _, _) | E_aux (E_internal_plet _, _) -> parens | _ -> fun x -> x in
    wrap_with_left_arrow arg_monadic (wrap (doc_exp arg_monadic ctx arg))
  in
  let d_of_field (FE_aux (FE_fexp (field, e), _) as fexp) =
    let field_monadic = effectful (effect_of e) in
    doc_fexp field_monadic ctx fexp
  in
  (* string (" /- " ^ string_of_exp_con full_exp ^ " -/ ") ^^ *)
  match e with
  | E_id id ->
      if Env.is_register id env then wrap_with_left_arrow (not as_monadic) (string "readReg " ^^ doc_id_ctor id)
      else wrap_with_pure as_monadic (doc_id_ctor id)
  | E_lit l -> wrap_with_pure as_monadic (doc_lit l)
  | E_app (Id_aux (Id "None", _), _) -> string "none"
  | E_app (Id_aux (Id "Some", _), args) ->
      let d_id = string "some" in
      let d_args = List.map d_of_arg args in
      nest 2 (parens (flow (break 1) (d_id :: d_args)))
  | E_app (Id_aux (Id "foreach#", _), args) -> begin
      let doc_loop_var (E_aux (e, (l, _)) as exp) =
        match e with
        | E_id id ->
            let id_pp = doc_id_ctor id in
            let typ = typ_of exp in
            (id_pp, id_pp)
        | E_lit (L_aux (L_unit, _)) -> (string "()", underscore)
        | _ -> raise (Reporting.err_unreachable l __POS__ ("Bad expression for variable in loop: " ^ string_of_exp exp))
      in
      let make_loop_vars extra_binders varstuple =
        match varstuple with
        | E_aux (E_tuple vs, _) ->
            let vs = List.map doc_loop_var vs in
            let mkpp f vs = separate (string ", ") (List.map f vs) in
            let tup_pp = mkpp (fun (pp, _) -> pp) vs in
            let match_pp = mkpp (fun (_, pp) -> pp) vs in
            (parens tup_pp, separate space ((string "λ" :: extra_binders) @ [parens match_pp; string "=>"]))
        | _ ->
            let exp_pp, match_pp = doc_loop_var varstuple in
            (exp_pp, separate space ((string "λ" :: extra_binders) @ [match_pp; string "=>"]))
      in
      match args with
      | [from_exp; to_exp; step_exp; ord_exp; vartuple; body] ->
          let loopvar, body =
            match body with
            | E_aux
                ( E_if
                    ( _,
                      E_aux
                        ( E_let
                            ( LB_aux
                                ( LB_val
                                    ( ( P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _)
                                      | P_aux (P_var (P_aux (P_id id, _), _), _)
                                      | P_aux (P_id id, _) ),
                                      _
                                    ),
                                  _
                                ),
                              body
                            ),
                          _
                        ),
                      _
                    ),
                  _
                ) ->
                (id, body)
            | _ -> raise (Reporting.err_unreachable l __POS__ ("Unable to find loop variable in " ^ string_of_exp body))
          in
          let effects = effectful (effect_of body) in
          let combinator = if as_monadic && effects then "foreach_M" else "foreach_" in
          let body_ctxt = add_single_kid_id_rename ctx loopvar (mk_kid ("loop_" ^ string_of_id loopvar)) in
          let from_exp_pp, to_exp_pp, step_exp_pp =
            (doc_exp false ctx from_exp, doc_exp false ctx to_exp, doc_exp false ctx step_exp)
          in
          (* The body has the right type for deciding whether a proof is necessary *)
          (* let vartuple_retyped = check_exp env (strip_exp vartuple) (typ_of body) in *)
          let vartuple_pp, body_lambda = make_loop_vars [doc_id_ctor loopvar] vartuple in
          let body_lambda = if effects then body_lambda ^^ string " do" else body_lambda in
          (* TODO: this should probably be construct_dep_pairs, but we would need
             to change it to use the updated context. *)
          let body_pp = doc_exp as_monadic body_ctxt body in
          parens
            ((prefix 2 1)
               ((separate space) [string combinator; from_exp_pp; to_exp_pp; step_exp_pp; vartuple_pp])
               (parens (prefix 2 1 (group body_lambda) body_pp))
            )
      | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
    end
  | E_app (f, args) ->
      let _, f_typ = Env.get_val_spec f env in
      let implicits = get_fn_implicits f_typ in
      let d_id =
        if Env.is_extern f env "lean" then string (Env.get_extern f env "lean")
        else doc_exp false ctx (E_aux (E_id f, (l, annot)))
      in
      let d_args = List.map d_of_arg args in
      let d_args = List.map snd (List.filter (fun x -> not (fst x)) (List.combine implicits d_args)) in
      let fn_monadic = not (Effects.function_is_pure f ctx.global.effect_info) in
      nest 2
        (wrap_with_left_arrow ((not as_monadic) && fn_monadic)
           (wrap_with_pure (as_monadic && not fn_monadic) (parens (flow (break 1) (d_id :: d_args))))
        )
  | E_vector vals ->
      string "#v" ^^ wrap_with_pure as_monadic (brackets (nest 2 (flow (comma ^^ break 1) (List.map d_of_arg vals))))
  | E_typ (typ, e) ->
      if effectful (effect_of e) then
        parens (separate space [doc_exp as_monadic ctx e; colon; string "SailM"; doc_typ ctx typ])
      else wrap_with_pure as_monadic (parens (separate space [doc_exp false ctx e; colon; doc_typ ctx typ]))
  | E_tuple es -> wrap_with_pure as_monadic (parens (separate_map (comma ^^ space) d_of_arg es))
  | E_internal_plet (lpat, lexp, e) | E_let (LB_aux (LB_val (lpat, lexp), _), e) ->
      let id_typ =
        match pat_is_plain_binder env lpat with
        | Some (_, Some typ) -> doc_pat lpat ^^ space ^^ colon ^^ space ^^ doc_typ ctx typ
        | _ -> doc_pat lpat
      in
      let pp_let_line_f l = group (nest 2 (flow (break 1) l)) in
      let pp_let_line =
        if effectful (effect_of lexp) then
          if is_unit (typ_of lexp) && is_anonymous_pat lpat then doc_exp true ctx lexp
          else pp_let_line_f [separate space [string "let"; id_typ; string "← do"]; doc_exp true ctx lexp]
        else pp_let_line_f [separate space [string "let"; id_typ; coloneq]; doc_exp false ctx lexp]
      in
      pp_let_line ^^ hardline ^^ doc_exp as_monadic ctx e
  | E_internal_return e -> doc_exp false ctx e (* ??? *)
  | E_struct fexps ->
      let args = List.map d_of_field fexps in
      wrap_with_pure as_monadic (braces (space ^^ align (separate hardline args) ^^ space))
  | E_field (exp, id) ->
      (* TODO *)
      wrap_with_pure as_monadic (doc_exp false ctx exp ^^ dot ^^ doc_id_ctor id)
  | E_struct_update (exp, fexps) ->
      let args = List.map d_of_field fexps in
      (* TODO *)
      wrap_with_pure as_monadic
        (braces (space ^^ doc_exp false ctx exp ^^ string " with " ^^ separate (comma ^^ space) args ^^ space))
  | E_match (discr, brs) ->
      let cases = separate_map hardline (doc_match_clause as_monadic ctx) brs in
      string (match_or_match_bv brs) ^^ doc_exp false ctx discr ^^ string " with" ^^ hardline ^^ cases
  | E_assign ((LE_aux (le_act, tannot) as le), e) -> (
      match le_act with
      | LE_id id | LE_typ (_, id) -> string "writeReg " ^^ doc_id_ctor id ^^ space ^^ doc_exp false ctx e
      | LE_deref e' -> string "writeRegRef " ^^ doc_exp false ctx e' ^^ space ^^ doc_exp false ctx e
      | _ -> failwith ("assign " ^ string_of_lexp le ^ "not implemented yet")
    )
  | E_if (i, t, e) ->
      let statements_monadic = as_monadic || effectful (effect_of t) || effectful (effect_of e) in
      nest 2 (string "if" ^^ space ^^ nest 1 (doc_exp false ctx i))
      ^^ hardline
      ^^ nest 2 (string "then" ^^ space ^^ nest 3 (doc_exp statements_monadic ctx t))
      ^^ hardline
      ^^ nest 2 (string "else" ^^ space ^^ nest 3 (doc_exp statements_monadic ctx e))
  | E_ref id -> string "Reg " ^^ doc_id_ctor id
  | E_exit _ -> string "throw Error.Exit"
  | E_throw e -> string "sailThrow " ^^ parens (doc_exp false ctx e)
  | E_try (e, cases) ->
      let x = E_aux (E_id (Id_aux (Id "the_exception", Unknown)), (Unknown, annot)) in
      let cases = doc_exp true ctx (E_aux (E_match (x, cases), (Unknown, annot))) in
      string "sailTryCatch "
      ^^ parens (doc_exp false ctx e)
      ^^ space
      ^^ parens (string "fun the_exception => " ^^ hardline ^^ cases)
  | E_assert (e1, e2) -> string "assert " ^^ d_of_arg e1 ^^ space ^^ d_of_arg e2
  | E_list es -> brackets (separate_map comma_sp (doc_exp as_monadic ctx) es)
  | E_cons (hd_e, tl_e) -> parens (separate space [doc_exp false ctx hd_e; string "::"; doc_exp false ctx tl_e])
  | _ -> failwith ("Expression " ^ string_of_exp_con full_exp ^ " " ^ string_of_exp full_exp ^ " not translatable yet.")

and doc_fexp with_arrow ctx (FE_aux (FE_fexp (field, e), _)) = doc_id_ctor field ^^ string " := " ^^ doc_exp false ctx e

let doc_binder ctx i t =
  let paranthesizer =
    match t with
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]), _) ->
        implicit_parens
    | _ -> parens
  in
  (* Overwrite the id if it's captured *)
  let ctx = match captured_typ_var (i, t) with Some (i, ki) -> add_single_kid_id_rename ctx i ki | _ -> ctx in
  (ctx, separate space [doc_id_ctor i; colon; doc_typ ctx t] |> paranthesizer)

let doc_funcl_init global (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let (TypQ_aux (tq, l) as tq_all), typ = Env.get_val_spec_orig id env in
  let arg_typs, ret_typ, _ =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ), _) -> (arg_typs, ret_typ, no_effect)
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  let pat, _, exp, _ = destruct_pexp pexp in
  let pats, fixup_binders = untuple_args_pat arg_typs pat in
  let binders : (id * typ) list =
    pats
    |> List.map (fun (pat, typ) ->
           match pat_is_plain_binder env pat with
           | Some (Some id, _) -> (id, typ)
           | Some (None, _) -> (Id_aux (Id "x", l), typ) (* TODO fresh name or wildcard instead of x *)
           | _ -> failwith "Argument pattern not translatable yet."
       )
  in
  let ctx = context_init env global in
  let ctx, binders =
    List.fold_left
      (fun (ctx, bs) (i, t) ->
        let ctx, d = doc_binder ctx i t in
        (ctx, bs @ [d])
      )
      (ctx, []) binders
  in
  let typ_quant_comment = doc_typ_quant_in_comment ctx tq_all in
  (* Use auto-implicits for type quanitifiers for now and see if this works *)
  let doc_ret_typ = doc_typ ctx ret_typ in
  let is_monadic = effectful (effect_of exp) in
  (* Add monad for stateful functions *)
  let doc_ret_typ = if is_monadic then string "SailM " ^^ doc_ret_typ else doc_ret_typ in
  let decl_val = [doc_ret_typ; coloneq] in
  (* Add do block for stateful functions *)
  let decl_val = if is_monadic then decl_val @ [string "do"] else decl_val in
  (typ_quant_comment, separate space ([string "def"; doc_id_ctor id] @ binders @ [colon] @ decl_val), ctx, fixup_binders)

let doc_funcl_body fixup_binders ctx (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let _, _, exp, _ = destruct_pexp pexp in
  (* If an argument was [x : (Int, Int)], which is transformed to [(arg0: Int) (arg1: Int)],
     this adds a let binding at the beginning of the function, of the form [let x := (arg0, arg1)] *)
  let exp = fixup_binders exp in
  let is_monadic = effectful (effect_of exp) in
  doc_exp is_monadic (context_with_env ctx env) exp

let doc_funcl ctx funcl =
  let comment, signature, ctx, fixup_binders = doc_funcl_init ctx.global funcl in
  comment ^^ nest 2 (signature ^^ hardline ^^ doc_funcl_body fixup_binders ctx funcl)

let doc_fundef ctx (FD_aux (FD_function (r, typa, fcls), fannot) as full_fundef) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [funcl] -> doc_funcl ctx funcl
  | _ -> failwith "FD_function with more than one clause"

let doc_type_union ctx (Tu_aux (Tu_ty_id (ty, i), _)) =
  nest 2 (flow space [pipe; doc_id_ctor i; parens (flow space [underscore; colon; doc_typ ctx ty])])

let string_of_type_def_con (TD_aux (td, _)) =
  match td with
  | TD_abbrev _ -> "TD_abbrev"
  | TD_record _ -> "TD_record"
  | TD_variant _ -> "TD_variant"
  | TD_abstract _ -> "TD_abstract"
  | TD_bitfield _ -> "TD_bitfield"
  | TD_enum _ -> "TD_enum"

let doc_typdef ctx (TD_aux (td, tannot) as full_typdef) =
  match td with
  | TD_enum (id, fields, _) ->
      let fields = List.map doc_id_ctor fields in
      let fields = List.map (fun i -> space ^^ pipe ^^ space ^^ i) fields in
      let derivers =
        if List.length fields == 0 then [string "DecidableEq"] else [string "Inhabited"; string "DecidableEq"]
      in
      let enums_doc = concat fields in
      let id = doc_id_ctor id in
      nest 2
        (flow (break 1) [string "inductive"; id; string "where"]
        ^^ enums_doc ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers
        )
      ^^ hardline ^^ hardline ^^ string "open " ^^ id
  | TD_record (id, tq, fields, _) ->
      let fields = List.map (doc_typ_id ctx) fields in
      let fields_doc = separate hardline fields in
      let rectyp = doc_typ_quant_relevant ctx tq in
      let rectyp = List.map (fun d -> parens d) rectyp |> separate space in
      doc_typ_quant_in_comment ctx tq ^^ hardline
      ^^ nest 2
           (flow (break 1) (remove_empties [string "structure"; doc_id_ctor id; rectyp; string "where"])
           ^^ hardline ^^ fields_doc
           )
  | TD_abbrev (id, tq, A_aux (A_typ (Typ_aux (Typ_app (Id_aux (Id "range", _), _), _) as t), _)) ->
      let vars = doc_typ_quant_relevant ctx tq in
      let vars = List.map parens vars in
      let vars = separate space vars in
      nest 2 (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor id; vars; coloneq; doc_typ ctx t]))
  | TD_abbrev (id, tq, A_aux (A_typ t, _)) ->
      let vars = doc_typ_quant_only_vars ctx tq in
      let vars = separate space vars in
      nest 2 (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor id; vars; coloneq; doc_typ ctx t]))
  | TD_abbrev (id, tq, A_aux (A_nexp ne, _)) ->
      let vars = doc_typ_quant_only_vars ctx tq in
      let vars = separate space vars in
      nest 2 (flow (break 1) [string "abbrev"; doc_id_ctor id; colon; string "Int"; coloneq; doc_nexp ctx ne])
  | TD_abbrev (id, tq, A_aux (A_bool nc, _)) -> empty
  | TD_variant (id, tq, ar, _) ->
      let pp_tus = concat (List.map (fun tu -> hardline ^^ doc_type_union ctx tu) ar) in
      let rectyp = doc_typ_quant_relevant ctx tq in
      let rectyp = List.map (fun d -> parens d) rectyp |> separate space in
      let id = doc_id_ctor id in
      doc_typ_quant_in_comment ctx tq ^^ hardline
      ^^ nest 2 (nest 2 (flow space (remove_empties [string "inductive"; id; rectyp; string "where"])) ^^ pp_tus)
      ^^ hardline ^^ hardline
      ^^ flow space [string "open"; id]
  | _ -> failwith ("Type definition " ^ string_of_type_def_con full_typdef ^ " not translatable yet.")

(* Copied from the Coq PP *)
let doc_val ctx pat exp =
  let id, pat_typ =
    match pat with
    | P_aux (P_typ (typ, P_aux (P_id id, _)), _) -> (id, Some typ)
    | P_aux (P_id id, _) -> (id, None)
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _) when Id.compare id (id_of_kid kid) == 0 -> (id, None)
    | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _)), _)
      when Id.compare id (id_of_kid kid) == 0 ->
        (id, Some typ)
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 && Id.compare id (id_of_kid kid) == 0 ->
        (id, None)
    | P_aux
        (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 && Id.compare id (id_of_kid kid) == 0 ->
        (id, Some typ)
    | _ -> failwith ("Pattern " ^ string_of_pat_con pat ^ " " ^ string_of_pat pat ^ " not translatable yet.")
  in
  let typpp = match pat_typ with None -> empty | Some typ -> space ^^ colon ^^ space ^^ doc_typ ctx typ in
  let idpp = doc_id_ctor id in
  let base_pp = doc_exp false ctx exp in
  nest 2 (group (string "def" ^^ space ^^ idpp ^^ typpp ^^ space ^^ coloneq ^/^ base_pp))

let rec doc_defs_rec ctx defs types docdefs =
  match defs with
  | [] -> (types, docdefs)
  | DEF_aux (DEF_fundef fdef, dannot) :: defs' ->
      let env = dannot.env in
      let pp_f =
        if Env.is_extern (id_of_fundef fdef) env "lean" then empty
        else docdefs ^^ group (doc_fundef ctx fdef) ^/^ hardline
      in

      doc_defs_rec ctx defs' types pp_f
  | DEF_aux (DEF_type tdef, _) :: defs' when List.mem (string_of_id (id_of_type_def tdef)) !opt_extern_types ->
      doc_defs_rec ctx defs' types docdefs
  | DEF_aux (DEF_type tdef, _) :: defs' ->
      doc_defs_rec ctx defs' (types ^^ group (doc_typdef ctx tdef) ^/^ hardline) docdefs
  | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), _)), _) :: defs' ->
      doc_defs_rec ctx defs' types (docdefs ^^ group (doc_val ctx pat exp) ^/^ hardline)
  | _ :: defs' -> doc_defs_rec ctx defs' types docdefs

let doc_defs ctx defs = doc_defs_rec ctx defs empty empty

(* Remove all imports for now, they will be printed in other files. Probably just for testing. *)
let rec remove_imports (defs : (Libsail.Type_check.tannot, Libsail.Type_check.env) def list) depth =
  match defs with
  | [] -> []
  | DEF_aux (DEF_pragma ("include_start", _, _), _) :: ds -> remove_imports ds (depth + 1)
  | DEF_aux (DEF_pragma ("include_end", _, _), _) :: ds -> remove_imports ds (depth - 1)
  | d :: ds -> if depth > 0 then remove_imports ds depth else d :: remove_imports ds depth

let add_reg_typ typ_map (typ, id, _) =
  let typ_id = State.id_of_regtyp IdSet.empty typ in
  Bindings.add typ_id (id, typ) typ_map

let register_enums registers =
  separate hardline
    [
      string "inductive Register : Type where";
      separate_map hardline (fun (_, id, _) -> string "  | " ^^ doc_id_ctor id) registers;
      string "  deriving DecidableEq, Hashable";
      string "open Register";
      empty;
    ]

let type_enum ctx registers =
  separate hardline
    [
      string "abbrev RegisterType : Register → Type";
      separate_map hardline
        (fun (typ, id, _) -> string "  | ." ^^ doc_id_ctor id ^^ string " => " ^^ doc_typ ctx typ)
        registers;
      empty;
    ]

let inhabit_enum ctx typ_map =
  separate_map hardline
    (fun (_, (id, typ)) ->
      string "instance : Inhabited (RegisterRef RegisterType "
      ^^ doc_typ ctx typ ^^ string ") where" ^^ hardline ^^ string "  default := .Reg " ^^ doc_id_ctor id
    )
    typ_map

let doc_reg_info env global registers =
  let ctx = context_init env global in
  let type_map = List.fold_left add_reg_typ Bindings.empty registers in
  let type_map = Bindings.bindings type_map in
  separate hardline
    [register_enums registers; type_enum ctx registers; string "open RegisterRef"; inhabit_enum ctx type_map; empty]

let doc_monad_abbrev defs (has_registers : bool) =
  let find_exc_typ defs =
    let is_exc_typ_def = function
      | DEF_aux (DEF_type td, _) -> string_of_id (id_of_type_def td) = "exception"
      | _ -> false
    in
    if List.exists is_exc_typ_def defs then "exception" else "Unit"
  in
  let exc = find_exc_typ defs in
  let pp_register_type =
    if has_registers then string "PreSailM RegisterType trivialChoiceSource " ^^ string exc
    else string "PreSailM PEmpty.elim trivialChoiceSource " ^^ string exc
  in
  separate space [string "abbrev"; string "SailM"; coloneq; pp_register_type] ^^ hardline ^^ hardline

let doc_instantiations ctx env =
  let params = Monad_params.find_monad_parameters env in
  match params with
  | None -> empty
  | Some params ->
      nest 2
        (separate hardline
           [
             string "instance : Arch where";
             string "va_size := 64";
             string "pa := " ^^ doc_typ ctx params.pa_type;
             string "abort := " ^^ doc_typ ctx params.abort_type;
             string "translation := " ^^ doc_typ ctx params.translation_summary_type;
             string "fault := " ^^ doc_typ ctx params.fault_type;
             string "tlb_op := " ^^ doc_typ ctx params.tlbi_type;
             string "cache_op := " ^^ doc_typ ctx params.cache_op_type;
             string "barrier := " ^^ doc_typ ctx params.barrier_type;
             string "arch_ak := " ^^ doc_typ ctx params.arch_ak_type;
             string "sys_reg_id := " ^^ doc_typ ctx params.sys_reg_id_type ^^ hardline;
           ]
        )
      ^^ hardline
let main_function_stub =
  nest 2
    (separate hardline
       [
         string "def main (_ : List String) : IO UInt32 := do";
         string "main_of_sail_main ⟨default, (), default, default, default⟩ sail_main";
         string "return 0";
         empty;
       ]
    )

let pp_ast_lean (env : Type_check.env) effect_info ({ defs; _ } as ast : Libsail.Type_check.typed_ast) o =
  (* TODO: remove the following line once we can handle the includes *)
  (* let defs = remove_imports defs 0 in *)
  let regs = State.find_registers defs in
  let global = { effect_info } in
  let ctx = context_init env global in
  let has_registers = List.length regs > 0 in
  let register_refs = if has_registers then doc_reg_info env global regs else empty in
  let monad = doc_monad_abbrev defs has_registers in
  let instantiations = doc_instantiations ctx env in
  let types, fundefs = doc_defs ctx defs in
  let main_function = if !the_main_function_has_been_seen then main_function_stub else empty in
  print o (types ^^ register_refs ^^ monad ^^ instantiations ^^ fundefs ^^ main_function);
  !the_main_function_has_been_seen
