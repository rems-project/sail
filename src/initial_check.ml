open Type_internal
open Ast

type kind = Type_internal.kind
type typ = Type_internal.t

type envs = Nameset.t * kind Envmap.t * t Envmap.t
type 'a envs_out = 'a * envs

let id_to_string (Id_aux(id,l)) =
  match id with | Id(x) | DeIid(x) -> x

(*placeholder, write in type_internal*)
let kind_to_string _ = " kind pp place holder "

let typ_error l msg opt_id opt_kind =
  raise (Reporting_basic.err_typ 
           l
           (msg ^
              (match opt_id, opt_kind with
              | Some(id),Some(kind) -> (id_to_string id) ^ " of " ^ (kind_to_string kind)
              | Some(id),None -> ": " ^ (id_to_string id)
              | None,Some(kind) -> " " ^ (kind_to_string kind)
              | None,None -> "")))
                
let to_ast_id (Parse_ast.Id_aux(id,l)) =
    Id_aux( (match id with
             | Parse_ast.Id(x) -> Id(x)
             | Parse_ast.DeIid(x) -> DeIid(x)) , l)

let to_ast_kind (k_env : kind Envmap.t) (Parse_ast.K_aux(Parse_ast.K_kind(klst),l)) : (Ast.kind * kind) =
  let to_ast_basic_kind (Parse_ast.BK_aux(k,l')) =
    match k with
    | Parse_ast.BK_type -> BK_aux(BK_type,l'), { k = K_Typ}
    | Parse_ast.BK_nat -> BK_aux(BK_nat,l'), { k = K_Nat }
    | Parse_ast.BK_order -> BK_aux(BK_order,l'), { k = K_Ord }
    | Parse_ast.BK_effects -> BK_aux(BK_effects,l'), { k = K_Efct }
  in
  match klst with
  | [] -> raise (Reporting_basic.err_unreachable l "Kind with empty kindlist encountered")
  | [k] -> let k_ast,k_typ = to_ast_basic_kind k in
           K_aux(K_kind([k_ast]),l), k_typ
  | ks -> let k_pairs = List.map to_ast_basic_kind ks in
          let reverse_typs = List.rev (List.map snd k_pairs) in
          let ret,args = List.hd reverse_typs, List.rev (List.tl reverse_typs) in
          match ret.k with
          | K_Typ -> K_aux(K_kind(List.map fst k_pairs), l), { k = K_Lam(args,ret) }
          | _ -> typ_error l "Type constructor must have an -> kind ending in Type" None None

let rec to_ast_typ (k_env : kind Envmap.t) (t: Parse_ast.atyp) : Ast.typ =
  match t with
  | Parse_ast.ATyp_aux(t,l) ->
    Typ_aux( (match t with 
              | Parse_ast.ATyp_id(id) -> 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Typ -> Typ_var id
                              | K_infer -> k.k <- K_Typ; Typ_var id
                              | _ -> typ_error l "Required a variable with kind Type, encountered " (Some id) (Some k))
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
              | Parse_ast.ATyp_wild -> Typ_wild
              | Parse_ast.ATyp_fn(arg,ret,efct) -> Typ_fn( (to_ast_typ k_env arg),
                                                           (to_ast_typ k_env ret),
                                                           (to_ast_effects k_env efct))
              | Parse_ast.ATyp_tup(typs) -> Typ_tup( List.map (to_ast_typ k_env) typs)
              | Parse_ast.ATyp_app(pid,typs) -> 
                let id = to_ast_id pid in 
                let k = Envmap.apply k_env (id_to_string id) in
                (match k with 
                | Some({k = K_Lam(args,t)}) -> Typ_app(id,(List.map2 (fun k a -> (to_ast_typ_arg k_env k a)) args typs))
                | None -> typ_error l "Required a type constructor, encountered an unbound variable" (Some id) None
                | _ -> typ_error l "Required a type constructor, encountered a base kind variable" (Some id) None)
              | _ -> typ_error l "Required an item of kind Type, encountered an illegal form for this kind" None None
    ), l)

and to_ast_nexp (k_env : kind Envmap.t) (n: Parse_ast.atyp) : Ast.nexp =
  match n with
  | Parse_ast.ATyp_aux(t,l) ->
    (match t with
    | Parse_ast.ATyp_id(id) ->                 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> Nexp_aux((match k.k with
                                      | K_Nat -> Nexp_id id
                                      | K_infer -> k.k <- K_Nat; Nexp_id id
                                      | _ -> typ_error l "Required a variable with kind Nat, encountered " (Some id) (Some k)),l)
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
    | Parse_ast.ATyp_constant(i) -> Nexp_aux(Nexp_constant(i),l)
    | Parse_ast.ATyp_sum(t1,t2) ->
      let n1 = to_ast_nexp k_env t1 in
      let n2 = to_ast_nexp k_env t2 in
      Nexp_aux(Nexp_sum(n1,n2),l)
    | Parse_ast.ATyp_exp(t1) -> Nexp_aux(Nexp_exp(to_ast_nexp k_env t1),l)
    | Parse_ast.ATyp_tup(typs) ->
      let rec times_loop (typs : Parse_ast.atyp list) (one_ok : bool) : nexp =
        (match typs,one_ok with
        | [],_ | [_],false -> raise (Reporting_basic.err_unreachable l "to_ast_nexp has ATyp_tup with empty list or list with one element")
        | [t],true -> to_ast_nexp k_env t
        | (t1::typs),_ -> let n1 = to_ast_nexp k_env t1 in
                          let n2 = times_loop typs true in 
                          (Nexp_aux((Nexp_times(n1,n2)),l)))  (*TODO This needs just a portion of the l, think about adding a way to split*)
      in
      times_loop typs false
    | _ -> typ_error l "Requred an item of kind Nat, encountered an illegal form for this kind" None None)
    
and to_ast_order (k_env : kind Envmap.t) (o: Parse_ast.atyp) : Ast.order =
  match o with
  | Parse_ast.ATyp_aux(t,l) ->
    Ord_aux( (match t with
               | Parse_ast.ATyp_id(id) -> 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Ord -> Ord_id id
                              | K_infer -> k.k <- K_Ord; Ord_id id
                              | _ -> typ_error l "Required a variable with kind Order, encountered " (Some id) (Some k))
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
               | Parse_ast.ATyp_inc -> Ord_inc
               | Parse_ast.ATyp_dec -> Ord_dec
               | _ -> typ_error l "Requred an item of kind Order, encountered an illegal form for this kind" None None
    ), l)

and to_ast_effects (k_env : kind Envmap.t) (e : Parse_ast.atyp) : Ast.effects =
  match e with
  | Parse_ast.ATyp_aux(t,l) ->
    Effects_aux( (match t with
               | Parse_ast.ATyp_efid(id) ->  
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Efct -> Effects_var id
                              | K_infer -> k.k <- K_Efct; Effects_var id
                              | _ -> typ_error l "Required a variable with kind Effect, encountered " (Some id) (Some k))
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
               | Parse_ast.ATyp_set(effects) ->
                 Effects_set( List.map 
                             (fun efct -> match efct with
                             | Parse_ast.Effect_aux(e,l) ->
                               Effect_aux((match e with 
                               | Parse_ast.Effect_rreg -> Effect_rreg
                               | Parse_ast.Effect_wreg -> Effect_wreg
                               | Parse_ast.Effect_rmem -> Effect_rmem
                               | Parse_ast.Effect_wmem -> Effect_wmem
                               | Parse_ast.Effect_undef -> Effect_undef
                               | Parse_ast.Effect_unspec -> Effect_unspec
                               | Parse_ast.Effect_nondet -> Effect_nondet),l))
                             effects)
               | _ -> typ_error l "Required an item of kind Effects, encountered an illegal form for this kind" None None
    ), l)

and to_ast_typ_arg (k_env : kind Envmap.t) (kind : kind) (arg : Parse_ast.atyp) : Ast.typ_arg =
  let l = (match arg with Parse_ast.ATyp_aux(_,l) -> l) in
  Typ_arg_aux (  
    (match kind.k with 
    | K_Typ -> Typ_arg_typ (to_ast_typ k_env arg)
    | K_Nat  -> Typ_arg_nexp (to_ast_nexp k_env arg)
    | K_Ord -> Typ_arg_order (to_ast_order k_env arg)
    | K_Efct -> Typ_arg_effects (to_ast_effects k_env arg)
    | _ -> raise (Reporting_basic.err_unreachable l "To_ast_typ_arg received Lam kind or infer kind")),
    l)

let to_ast_nexp_constraint (k_env : kind Envmap.t) (c : Parse_ast.nexp_constraint) : nexp_constraint =
  match c with 
  | Parse_ast.NC_aux(nc,l) ->
    NC_aux( (match nc with
             | Parse_ast.NC_fixed(t1,t2) -> 
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_fixed(n1,n2)
             | Parse_ast.NC_bounded_ge(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_bounded_ge(n1,n2)
             | Parse_ast.NC_bounded_le(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_bounded_le(n1,n2)
             | Parse_ast.NC_nat_set_bounded(id,bounds) ->
               NC_nat_set_bounded(to_ast_id id, bounds)
    ), l)               

let to_ast_typquant (k_env: kind Envmap.t) (tq : Parse_ast.typquant) : typquant * kind Envmap.t =
  assert false

let to_ast_typschm (k_env : kind Envmap.t) (tschm : Parse_ast.typschm) : Ast.typschm =
  match tschm with
  | Parse_ast.TypSchm_aux(ts,l) -> 
    (match ts with | Parse_ast.TypSchm_ts(tquant,t) ->
      let tq,k_env = to_ast_typquant k_env tquant in
      let typ = to_ast_typ k_env t in
      TypSchm_aux(TypSchm_ts(tq,typ),l))

(*
type 
def_aux =  (* Top-level definition *)
   DEF_type of type_def (* type definition *)
 | DEF_fundef of fundef (* function definition *)
 | DEF_val of letbind (* value definition *)
 | DEF_spec of val_spec (* top-level type constraint *)
 | DEF_default of default_typing_spec (* default kind and type assumptions *)
 | DEF_reg_dec of atyp * id (* register declaration *)
 | DEF_scattered_function of rec_opt * tannot_opt * effects_opt * id (* scattered function definition header *)
 | DEF_scattered_funcl of funcl (* scattered function definition clause *)
 | DEF_scattered_variant of id * naming_scheme_opt * typquant (* scattered union definition header *)
 | DEF_scattered_unioncl of id * atyp * id (* scattered union definition member *)
 | DEF_scattered_end of id (* scattered definition end *)


type 
def = 
   DEF_aux of def_aux * l *)

let to_ast_def (names, k_env, t_env) partial_defs def : ((tannot def) option) envs_out * (tannot def) list = 
  match def with
  | Parse_ast.DEF_aux(d,l) ->
    (match d with
    | Parse_ast.DEF_type(t_def) -> assert false
    | Parse_ast.DEF_fundef(f_def) -> assert false
    | Parse_ast.DEF_val(lbind) -> assert false
    | Parse_ast.DEF_spec(val_spec) -> assert false
    | Parse_ast.DEF_default(typ_spec) -> assert false
    )


let rec to_ast_defs_helper envs partial_defs = function
  | [] -> ([],envs,partial_defs)
  | d::ds  -> let ((d', envs), partial_defs) = to_ast_def envs partial_defs d in
              match d' with
              | Some def -> let (defs, envs, p_defs) = to_ast_defs_helper envs partial_defs ds in 
                            (def::defs,envs, partial_defs)
              | None -> to_ast_defs_helper envs partial_defs ds
                

let to_ast (bound_names : Nameset.t) (kind_env : kind Envmap.t) (typ_env : t Envmap.t) (Parse_ast.Defs(defs)) =
  let defs,_,partial_defs = to_ast_defs_helper (bound_names,kind_env,typ_env) [] defs in
  (* (Defs defs) *) (*TODO there will be type defs in partial defs that need to replace "placeholders" in the def list *)
  (Defs [ ] ) (* Until not all forms return assert false *)
