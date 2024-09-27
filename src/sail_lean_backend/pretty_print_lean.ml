open Libsail

open Type_check
open Ast
open Ast_defs
open Ast_util
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

let is_enum env id = match Env.lookup_id id env with Enum _ -> true | _ -> false

let pat_is_plain_binder env (P_aux (p, _)) =
  match p with
  | (P_id id | P_typ (_, P_aux (P_id id, _))) when not (is_enum env id) -> Some (Some id)
  | P_wild -> Some None
  | _ -> None

(* Copied from the Coq PP *)
let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    ((P_aux (P_id id, (l, mk_tannot env typ)), typ), E_aux (E_id id, (l, mk_tannot env typ)))
  in
  List.split (List.mapi arg typs)

(* Copied from the Coq PP *)
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
  | _, [typ] -> ([(pat, typ)], identity)
  | _, _ -> unreachable l __POS__ "Unexpected pattern/type combination"

let doc_typ (Typ_aux (t, _) as typ) =
  match t with Typ_id (Id_aux (Id "unit", _)) -> string "Unit" | _ -> failwith "Type not translatable yet."

let doc_funcl_init (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let TypQ_aux (tq, l), typ = Env.get_val_spec_orig id env in
  let arg_typs, ret_typ, _ =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ), _) -> (arg_typs, ret_typ, no_effect)
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  match tq with
  | TypQ_tq _ -> failwith "Type quantifiers not translatable yet"
  | TypQ_no_forall ->
      ();
      let pat, _, _, _ = destruct_pexp pexp in
      let pats, _ = untuple_args_pat arg_typs pat in
      let binders : (id * typ) list =
        pats
        |> List.map (fun (pat, typ) ->
               match pat_is_plain_binder env pat with
               | Some (Some id) -> (id, typ)
               | Some None -> (Id_aux (Id "x", l), typ)
               | _ -> (Id_aux (Id "x", l), typ) (*failwith "Argument pattern not translatable yet."*)
           )
      in
      let binders : document list =
        binders |> List.map (fun (i, t) -> separate space [string (string_of_id i); string ":"; doc_typ t] |> parens)
      in
      separate space ([string "def"; string (string_of_id id)] @ binders @ [string ":"; doc_typ ret_typ; string ":="])

let doc_funcl funcl = separate hardline [doc_funcl_init funcl; string "  _"] ^^ hardline

let doc_fundef (FD_aux (FD_function (r, typa, fcls), fannot)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [funcl] -> doc_funcl funcl
  | _ -> failwith "FD_function with more than one clause"

let doc_def (DEF_aux (aux, def_annot) as def) =
  match aux with DEF_fundef fdef -> group (doc_fundef fdef) ^/^ hardline | _ -> empty

(* Remove all imports for now, they will be printed in other files. Probably just for testing. *)
let rec remove_imports (defs : (Libsail.Type_check.tannot, Libsail.Type_check.env) def list) depth =
  match defs with
  | [] -> []
  | DEF_aux (DEF_pragma ("include_start", _, _), _) :: ds -> remove_imports ds (depth + 1)
  | DEF_aux (DEF_pragma ("include_end", _, _), _) :: ds -> remove_imports ds (depth - 1)
  | d :: ds -> if depth > 0 then remove_imports ds depth else d :: remove_imports ds depth

let pp_ast_lean ({ defs; _ } as ast : Libsail.Type_check.typed_ast) o =
  let defs = remove_imports defs 0 in
  let output : document = separate empty (List.map doc_def defs) in
  print o output;
  ()
