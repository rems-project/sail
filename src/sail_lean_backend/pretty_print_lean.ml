open Libsail

open Type_check
open Ast
open Ast_defs
open Ast_util
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

let doc_id_ctor (Id_aux (i, _)) =
  match i with Id i -> string i | Operator x -> string (Util.zencode_string ("op " ^ x))

let is_enum env id = match Env.lookup_id id env with Enum _ -> true | _ -> false

let pat_is_plain_binder env (P_aux (p, _)) =
  match p with
  | (P_id id | P_typ (_, P_aux (P_id id, _))) when not (is_enum env id) -> Some (Some id)
  | P_wild | P_typ (_, P_aux (P_wild, _)) -> Some None
  | P_var (_, _) -> Some (Some (Id_aux (Id "var", Unknown)))
  | P_app (_, _) -> Some (Some (Id_aux (Id "app", Unknown)))
  | P_vector _ -> Some (Some (Id_aux (Id "vect", Unknown)))
  | P_tuple _ -> Some (Some (Id_aux (Id "tuple", Unknown)))
  | P_list _ -> Some (Some (Id_aux (Id "list", Unknown)))
  | P_cons (_, _) -> Some (Some (Id_aux (Id "cons", Unknown)))
  | P_lit _ -> Some (Some (Id_aux (Id "lit", Unknown)))
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
   into multiple binders and reconstruct it in the function body. *)
let rec untuple_args_pat typs (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let identity body = body in
  match (paux, typs) with
  | P_tuple [], _ ->
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
  (* TODO Occurrences of the unit literal are removed right now, in order to be able to compile `initialize_registers`. *)
  | P_lit (L_aux (L_unit, _)), _ -> ([], identity)
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

let doc_nexp (Nexp_aux (n, l) as nexp) =
  match n with
  | Nexp_constant i -> string (Big_int.to_string i)
  | _ -> failwith ("NExp " ^ string_of_nexp_con nexp ^ " " ^ string_of_nexp nexp ^ " not translatable yet.")

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

let rec doc_typ (Typ_aux (t, _) as typ) =
  match t with
  | Typ_id (Id_aux (Id "unit", _)) -> string "Unit"
  | Typ_id (Id_aux (Id "int", _)) -> string "Int"
  | Typ_id (Id_aux (Id "bool", _)) -> string "Bool"
  | Typ_id (Id_aux (Id "bit", _)) -> parens (string "BitVec 1")
  | Typ_id (Id_aux (Id "nat", _)) -> string "Nat"
  | Typ_app (Id_aux (Id "bitvector", _), [A_aux (A_nexp m, _)]) -> string "BitVec " ^^ doc_nexp m
  | Typ_tuple ts -> parens (separate_map (space ^^ string "×" ^^ space) doc_typ ts)
  | Typ_id (Id_aux (Id id, _)) -> string id
  | _ -> failwith ("Type " ^ string_of_typ_con typ ^ " " ^ string_of_typ typ ^ " not translatable yet.")

let doc_typ_id (typ, fid) = concat [doc_id_ctor fid; space; colon; space; doc_typ typ; hardline]

let doc_typ_quant tq =
  match tq with
  | TypQ_tq qs -> (
      match qs with [] -> string "" | _ -> failwith "Type quantifier not translatable yet."
    )
  | TypQ_no_forall -> string ""

let lean_escape_string s = Str.global_replace (Str.regexp "\"") "\"\"" s

let doc_lit (L_aux (lit, l)) =
  match lit with
  | L_unit -> string "()"
  | L_zero -> string "0#1"
  | L_one -> string "1#1"
  | L_false -> string "false"
  | L_true -> string "true"
  | L_num i ->
      let s = Big_int.to_string i in
      string s
  | L_hex n -> utf8string ("0x" ^ n)
  | L_bin n -> utf8string ("0b" ^ n)
  | L_undef -> utf8string "(Fail \"undefined value of unsupported type\")"
  | L_string s -> utf8string ("\"" ^ lean_escape_string s ^ "\"")
  | L_real s -> utf8string s (* TODO test if this is really working *)

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

let rec doc_exp (E_aux (e, (l, annot)) as full_exp) =
  let env = env_of_tannot annot in
  match e with
  | E_id id -> string (string_of_id id) (* TODO replace by a translating via a binding map *)
  | E_lit l -> doc_lit l
  | E_app (Id_aux (Id "internal_pick", _), _) ->
      string "sorry" (* TODO replace by actual implementation of internal_pick *)
  | E_internal_plet _ -> string "sorry" (* TODO replace by actual implementation of internal_plet *)
  | E_app (f, args) ->
      let d_id =
        if Env.is_extern f env "lean" then string (Env.get_extern f env "lean") else doc_exp (E_aux (E_id f, (l, annot)))
      in
      let d_args = List.map doc_exp args in
      nest 2 (parens (flow (break 1) (d_id :: d_args)))
  | E_vector vals -> failwith "vector found"
  | E_typ (typ, e) -> parens (separate space [doc_exp e; colon; doc_typ typ])
  | E_tuple es -> parens (separate_map (comma ^^ space) doc_exp es)
  | E_let (LB_aux (LB_val (lpat, lexp), _), e) ->
      let id =
        match pat_is_plain_binder env lpat with
        | Some (Some (Id_aux (Id id, _))) -> id
        | Some None -> "x" (* TODO fresh name or wildcard instead of x *)
        | _ -> failwith "Let pattern not translatable yet."
      in
      nest 2 (flow (break 1) [string "let"; string id; coloneq; doc_exp lexp]) ^^ hardline ^^ doc_exp e
  | _ -> failwith ("Expression " ^ string_of_exp_con full_exp ^ " " ^ string_of_exp full_exp ^ " not translatable yet.")

let doc_funcl_init (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let TypQ_aux (tq, l), typ = Env.get_val_spec_orig id env in
  let arg_typs, ret_typ, _ =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ), _) -> (arg_typs, ret_typ, no_effect)
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  match tq with
  | TypQ_tq [] | TypQ_no_forall ->
      ();
      let pat, _, _, _ = destruct_pexp pexp in
      let pats, _ = untuple_args_pat arg_typs pat in
      let binders : (id * typ) list =
        pats
        |> List.map (fun (pat, typ) ->
               match pat_is_plain_binder env pat with
               | Some (Some id) -> (id, typ)
               | Some None -> (Id_aux (Id "x", l), typ) (* TODO fresh name or wildcard instead of x *)
               | _ -> failwith "Argument pattern not translatable yet."
           )
      in
      let binders : document list =
        binders |> List.map (fun (i, t) -> separate space [string (string_of_id i); colon; doc_typ t] |> parens)
      in
      separate space ([string "def"; string (string_of_id id)] @ binders @ [colon; doc_typ ret_typ; coloneq])
  | TypQ_tq qs ->
      let qs = List.map string_of_quant_item qs in
      let foo = String.concat ";" qs in
      failwith ("Type quantifiers (" ^ foo ^ ") not translatable yet")

let doc_funcl_body (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let _, _, exp, _ = destruct_pexp pexp in
  doc_exp exp

let doc_funcl funcl = nest 2 (doc_funcl_init funcl ^^ hardline ^^ doc_funcl_body funcl)

let doc_fundef (FD_aux (FD_function (r, typa, fcls), fannot)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [funcl] -> doc_funcl funcl
  | _ -> failwith "FD_function with more than one clause"

let string_of_type_def_con (TD_aux (td, _)) =
  match td with
  | TD_abbrev _ -> "TD_abbrev"
  | TD_record _ -> "TD_record"
  | TD_variant _ -> "TD_variant"
  | TD_abstract _ -> "TD_abstract"
  | TD_bitfield _ -> "TD_bitfield"
  | TD_enum _ -> "TD_enum"

let doc_typdef (TD_aux (td, tannot) as full_typdef) =
  match td with
  | TD_enum (Id_aux (Id id, _), fields, _) ->
      let derivers = if List.length fields > 0 then [string "Inhabited"] else [] in
      let fields = List.map doc_id_ctor fields in
      let fields = List.map (fun i -> space ^^ pipe ^^ space ^^ i) fields in
      let enums_doc = concat fields in
      nest 2
        (flow (break 1) [string "inductive"; string id; string "where"]
        ^^ enums_doc ^^ hardline ^^ string "deriving" ^^ space
        ^^ separate (comma ^^ space) derivers
        )
  | TD_record (Id_aux (Id id, _), TypQ_aux (tq, _), fields, _) ->
      let fields = List.map doc_typ_id fields in
      let enums_doc = concat fields in
      let rectyp = doc_typ_quant tq in
      nest 2 (flow (break 1) [string "structure"; string id; rectyp; string "where"] ^^ hardline ^^ enums_doc)
  | _ -> failwith ("Type definition " ^ string_of_type_def_con full_typdef ^ " not translatable yet.")

let doc_def (DEF_aux (aux, def_annot) as def) =
  match aux with
  | DEF_fundef fdef -> group (doc_fundef fdef) ^/^ hardline
  | DEF_type tdef -> group (doc_typdef tdef) ^/^ hardline
  | _ -> empty

(* Remove all imports for now, they will be printed in other files. Probably just for testing. *)
let rec remove_imports (defs : (Libsail.Type_check.tannot, Libsail.Type_check.env) def list) depth =
  match defs with
  | [] -> []
  | DEF_aux (DEF_pragma ("include_start", _, _), _) :: ds -> remove_imports ds (depth + 1)
  | DEF_aux (DEF_pragma ("include_end", _, _), _) :: ds -> remove_imports ds (depth - 1)
  | d :: ds -> if depth > 0 then remove_imports ds depth else d :: remove_imports ds depth

let pp_ast_lean ({ defs; _ } as ast : Libsail.Type_check.typed_ast) o =
  let defs = remove_imports defs 0 in
  let output : document = separate_map empty doc_def defs in
  output_string o "import Sail.sail\n\n";
  print o output;
  ()
