open Ast
module Envmap = Finite_map.Fmap_map(String)
module Nameset' = Set.Make(String)
module Nameset = struct
  include Nameset'
  let pp ppf nameset =
    Format.fprintf ppf "{@[%a@]}"
      (Pp.lst ",@ " Pp.pp_str)
      (Nameset'.elements nameset)
end

type kind = { mutable k : k_aux }
and k_aux =
  | K_Typ
  | K_Nat
  | K_Ord
  | K_Efct
  | K_Val
  | K_Lam of kind list * kind
  | K_infer

type t = { mutable t : t_aux }
and t_aux =
  | Tvar of string
  | Tid of string
  | Tfn of t * t * effect
  | Ttup of t list
  | Tapp of string * t_arg list
  | Tuvar of t_uvar
and t_uvar = { index : int; mutable subst : t option }
and nexp = { mutable nexp : nexp_aux }
and nexp_aux =
  | Nvar of string
  | Nconst of int
  | Nadd of nexp * nexp
  | Nmult of nexp * nexp
  | N2n of nexp
  | Nneg of nexp (* Unary minus for representing new vector sizes after vector slicing *)
  | Nuvar of n_uvar
and n_uvar = { nindex : int; mutable nsubst : t option }
and effect = { mutable effect : effect_aux }
and effect_aux =
  | Evar of string
  | Eset of base_effect list
  | Euvar of e_uvar
and e_uvar = { eindex : int; mutable esubst : t option }
and order = { mutable order : order_aux }
and order_aux =
  | Ovar of string
  | Oinc
  | Odec
  | Ouvar of o_uvar
and o_uvar = { oindex : int; mutable osubst : t option }
and t_arg =
  | TA_typ of t
  | TA_nexp of nexp
  | TA_eft of effect
  | TA_ord of order 

type tag =
  | Emp
  | External
  | Default
  | Constructor
  | Enum
  | Spec

(* Constraints for nexps, plus the location which added the constraint *)
type nexp_range =
  | LtEq of Parse_ast.l * nexp * nexp
  | Eq of Parse_ast.l * nexp * nexp
  | GtEq of Parse_ast.l * nexp * nexp
  | In of Parse_ast.l * string * int list

type t_params = (string * kind) list
type tannot = ((t_params * t) * tag * nexp_range list) option

type exp = tannot Ast.exp

let v_count = ref 0
let t_count = ref 0
let n_count = ref 0
let o_count = ref 0
let e_count = ref 0

let reset_fresh _ = 
  begin v_count := 0;
        t_count := 0;
        n_count := 0;
	o_count := 0;
	e_count := 0;
  end
let new_id _ =
  let i = !v_count in
  v_count := i+1;
  (string_of_int i) ^ "v"
let new_t _ = 
  let i = !t_count in
  t_count := i + 1;
  {t = Tuvar { index = i; subst = None }}
let new_n _ = 
  let i = !n_count in
  n_count := i + 1;
  { nexp = Nuvar { nindex = i; nsubst = None }}
let new_o _ = 
  let i = !o_count in
  o_count := i + 1;
  { order = Ouvar { oindex = i; osubst = None }}
let new_e _ =
  let i = !e_count in
  e_count := i + 1;
  { effect = Euvar { eindex = i; esubst = None }}
  
let nat_t = {t = Tapp("enum",[TA_nexp{nexp= Nconst 0};TA_nexp{nexp = Nconst max_int};TA_ord{order=Oinc}])}
let unit_t = { t = Tid "unit" } 
let bool_t = {t = Tid "bool" }

let initial_kind_env = 
  Envmap.from_list [ 
    ("bool", {k = K_Typ});
    ("nat", {k = K_Typ});
    ("unit", {k = K_Typ});
    ("bit", {k = K_Typ});
    ("list", {k = K_Lam( [{k = K_Typ}], {k = K_Typ})});
    ("reg", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("enum", {k = K_Lam( [ {k = K_Nat}; {k= K_Nat}; {k=K_Ord} ], {k = K_Typ}) });
    ("vector", {k = K_Lam( [ {k = K_Nat}; {k = K_Nat}; {k= K_Ord} ; {k=K_Typ}], {k=K_Typ}) } )
  ]

let nat_typ = {t=Tid "nat"}
let pure = {effect=Eset []}
let initial_typ_env =
  Envmap.from_list [
    ("ignore",Some(([("a",{k=K_Typ})],{t=Tfn ({t=Tvar "a"},unit_t,pure)}),External,[]));
    ("+",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure)}),External,[]));
    ("*",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure)}),External,[]));
    
  ]

let rec t_subst s_env t =
  match t.t with
  | Tvar i -> (match Envmap.apply s_env i with
               | Some(TA_typ t1) -> t1
               | _ -> t)
  | Tid _ | Tuvar _ -> t
  | Tfn(t1,t2,e) -> {t =Tfn((t_subst s_env t1),(t_subst s_env t2),(e_subst s_env e)) }
  | Ttup(ts) -> { t= Ttup(List.map (t_subst s_env) ts) }
  | Tapp(i,args) -> {t= Tapp(i,List.map (ta_subst s_env) args)}
and ta_subst s_env ta =
  match ta with
  | TA_typ t -> TA_typ (t_subst s_env t)
  | TA_nexp n -> TA_nexp (n_subst s_env n)
  | TA_eft e -> TA_eft (e_subst s_env e)
  | TA_ord o -> TA_ord (o_subst s_env o)
and n_subst s_env n =
  match n.nexp with
  | Nvar i -> (match Envmap.apply s_env i with
               | Some(TA_nexp n1) -> n1
               | _ -> n)
  | Nconst _ | Nuvar _ -> n
  | N2n n1 -> { nexp = N2n (n_subst s_env n1) }
  | Nneg n1 -> { nexp = Nneg (n_subst s_env n1) }
  | Nadd(n1,n2) -> { nexp = Nadd(n_subst s_env n1,n_subst s_env n2) }
  | Nmult(n1,n2) -> { nexp = Nmult(n_subst s_env n1,n_subst s_env n2) }
and o_subst s_env o =
  match o.order with
  | Ovar i -> (match Envmap.apply s_env i with
               | Some(TA_ord o1) -> o1
               | _ -> o)
  | _ -> o
and e_subst s_env e =
  match e.effect with
  | Evar i -> (match Envmap.apply s_env i with
               | Some(TA_eft e1) -> e1
               | _ -> e)
  | _ -> e

let subst k_env t =
  let subst_env = Envmap.from_list
    (List.map (fun (id,k) -> (id, 
                              match k.k with
                              | K_Typ -> TA_typ (new_t ())
                              | K_Nat -> TA_nexp (new_n ())
                              | K_Ord -> TA_ord (new_o ())
                              | K_Efct -> TA_eft (new_e ())
                              | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "substitution given an environment with a non-base-kind kind"))) k_env) 
  in
  t_subst subst_env t

let eq_error l msg = raise (Reporting_basic.err_typ l msg)

let compare_effect (BE_aux(e1,_)) (BE_aux(e2,_)) =
  match e1,e2 with 
  | (BE_rreg,BE_rreg) -> 0
  | (BE_rreg,_) -> -1
  | (_,BE_rreg) -> 1
  | (BE_wreg,BE_wreg) -> 0
  | (BE_wreg,_) -> -1
  | (_,BE_wreg) -> 1
  | (BE_rmem,BE_rmem) -> 0
  | (BE_rmem,_) -> -1
  | (_,BE_rmem) -> 1
  | (BE_wmem,BE_wmem) -> 0
  | (BE_wmem,_) -> -1
  | (_,BE_wmem) -> 1
  | (BE_undef,BE_undef) -> 0
  | (BE_undef,_) -> -1
  | (_,BE_undef) -> 1
  | (BE_unspec,BE_unspec) -> 0
  | (BE_unspec,_) -> -1
  | (_,BE_unspec) -> 1
  | (BE_nondet,BE_nondet) -> 0

let effect_sort = List.sort compare_effect

(* Check that o1 is or can be eqaul to o2. In the event that one is polymorphic, inc or dec can be used polymorphically but 'a cannot be used as inc or dec *)
let order_eq l o1 o2 = 
  match (o1.order,o2.order) with 
  | (Oinc,Oinc) | (Odec,Odec) | (Oinc,Ovar _) | (Odec,Ovar _) -> o2
  | (_,Ouvar i) -> o2.order <- o1.order; o2
  | (Ouvar i,_) -> o1.order <- o2.order; o2
  | (Ovar v1,Ovar v2) -> if v1=v2 then o2 else eq_error l ("Order variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | (Oinc,Odec) | (Odec,Oinc) -> eq_error l "Order mismatch of inc and dec"
  | (Ovar v1,Oinc) -> eq_error l ("Polymorphic order " ^ v1 ^ " cannot be used where inc is expected")
  | (Ovar v1,Odec) -> eq_error l ("Polymorhpic order " ^ v1 ^ " cannot be used where dec is expected")

(*Similarly to above.*)
let effects_eq l e1 e2 =
  match e1.effect,e2.effect with
  | Eset _ , Evar _ -> e2
  | Euvar i,_ -> e1.effect <- e2.effect; e2
  | _,Euvar i -> e2.effect <- e1.effect; e2
  | Eset es1,Eset es2 -> if ( effect_sort es1 = effect_sort es2 ) then e2 else eq_error l ("Effects must be the same") (*Print out both effect lists?*)
  | Evar v1, Evar v2 -> if v1 = v2 then e2 else eq_error l ("Effect variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Evar v1, Eset _ -> eq_error l ("Effect variable " ^ v1 ^ " cannot be used where a concrete set of effects is specified")

(* Is checking for structural equality only, other forms of equality will be handeled by constraints *)
let rec nexp_eq n1 n2 =
  match n1.nexp,n2.nexp with
  | Nvar v1,Nvar v2 -> v1=v2
  | Nconst n1,Nconst n2 -> n1=n2
  | Nadd(nl1,nl2), Nadd(nr1,nr2) -> nexp_eq nl1 nr1 && nexp_eq nl2 nr2
  | Nmult(nl1,nl2), Nmult(nr1,nr2) -> nexp_eq nl1 nr1 && nexp_eq nl2 nr2
  | N2n n,N2n n2 -> nexp_eq n n2
  | Nneg n,Nneg n2 -> nexp_eq n n2
  | Nuvar _, n -> n1.nexp <- n2.nexp; true
  | n,Nuvar _ -> n2.nexp <- n1.nexp; true
  | _,_ -> false

(*Is checking for structural equality amongst the types, building constraints for kind Nat. 
  When considering two enum type applications, will check for consistency instead of equality
  Note: needs an environment to handle type abbreviations, and to lookup in the case either is a Tid or Tapp*)
let rec type_consistent l t1 t2 = 
  match t1.t,t2.t with
  | Tvar v1,Tvar v2 -> if v1 = v2 then (t2,[]) else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Tid v1,Tid v2 -> if v1 = v2 then (t2,[]) else eq_error l ("Types " ^ v1 ^ " and " ^ v2 ^ " do not match") (*lookup for abbrev*)
  | Tfn(tin1,tout1,effect1),Tfn(tin2,tout2,effect2) -> 
    let (tin,cin) = type_consistent l tin1 tin2 in
    let (tout,cout) = type_consistent l tout1 tout2 in
    let effect = effects_eq l effect1 effect2 in
    (t2,cin@cout)
  | Ttup t1s, Ttup t2s ->
    (t2,(List.flatten (List.map snd (List.map2 (type_consistent l) t1s t2s))))
  | Tapp(id1,args1), Tapp(id2,args2) ->
    if id1=id2 && (List.length args2 = List.length args2) then
      if id1="enum" then
        (match args1,args2 with
        | [TA_nexp b1;TA_nexp r1; TA_ord o1],[TA_nexp b2;TA_nexp r2;TA_ord o2] ->
          (match (order_eq l o1 o2).order with
          | Oinc -> 
            if (nexp_eq b1 b2)&&(nexp_eq r1 r2)
            then (t2,[])
            else (t2, [GtEq(l,b1,b2);LtEq(l,r1,r2)])
          | Odec ->
            if (nexp_eq b1 b2)&&(nexp_eq r1 r2)
            then (t2,[])
            else (t2, [LtEq(l,b1,b2);GtEq(l,r1,r2)])
          | _ ->
            if (nexp_eq b1 b2)&&(nexp_eq r1 r2)
            then (t2,[])
            else (t2, [Eq(l,b1,b2);Eq(l,r1,r2)]))
        | _ -> raise (Reporting_basic.err_unreachable l "enum application incorrectly kinded"))
      else          
      (t2,(List.flatten (List.map2 (type_arg_eq l) args1 args2)))
    else eq_error l ("Type application of " ^ id1 ^ " and " ^ id2 ^ " must match")
  | Tuvar _, t -> t1.t <- t2.t; (t2,[])
  | t,Tuvar _ -> t2.t <- t1.t; (t2,[])
  | _,_ -> eq_error l ("Type mismatch")

and type_arg_eq l ta1 ta2 = 
  match ta1,ta2 with
  | TA_typ t1,TA_typ t2 -> snd (type_consistent l t1 t2)
  | TA_nexp n1,TA_nexp n2 -> if nexp_eq n1 n2 then [] else [Eq(l,n1,n2)]
  | TA_eft e1,TA_eft e2 -> (ignore(effects_eq l e1 e2);[])
  | TA_ord o1,TA_ord o2 -> (ignore(order_eq l o1 o2);[])
  | _,_ -> eq_error l "Type arguments must be of the same kind" 


let rec type_coerce l t1 e t2 = 
  match t1.t,t2.t with
  | Ttup t1s, Ttup t2s ->
    let tl1,tl2 = List.length t1s,List.length t2s in
    if tl1=tl2 then 
      let ids = List.map (fun _ -> Id_aux(Id (new_id ()),l)) t1s in
      let vars = List.map2 (fun i t -> E_aux(E_id(i),(l,Some(([],t),Emp,[])))) ids t1s in
      let (coerced_ts,cs,coerced_vars) = 
        List.fold_right2 (fun v (t1,t2) (ts,cs,es) -> let (t',c',e') = type_coerce l t1 v t2 in
                                                      ((t'::ts),c'@cs,(e'::es)))
          vars (List.combine t1s t2s) ([],[],[]) in
      if vars = coerced_vars then (t2,cs,e)
      else let e' = E_aux(E_case(e,[(Pat_aux(Pat_exp(P_aux(P_tup (List.map2 (fun i t -> P_aux(P_id i,(l,(Some(([],t),Emp,[]))))) ids t1s),(l,Some(([],t1),Emp,[]))),
                                               E_aux(E_tuple coerced_vars,(l,Some(([],t2),Emp,cs)))),
                                             (l,Some(([],t2),Emp,[]))))]),
                          (l,(Some(([],t2),Emp,[])))) in
           (t2,cs,e')
    else eq_error l ("A tuple of length " ^ (string_of_int tl1) ^ " cannot be used where a tuple of length " ^ (string_of_int tl2) ^ " is expected")
  | Tapp(id1,args1),Tapp(id2,args2) ->
    if id1=id2 
    then let t',cs' = type_consistent l t1 t2 in (t',cs',e)
    else (match id1,id2 with
    | "vector","enum" -> 
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;TA_ord {order = Oinc}] -> (t2,[],e) (*TODO*)
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;TA_ord {order = Odec}] -> (t2,[],e) (*TODO*)
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> (t2,[],e) (*TODO*)
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert non-bit vector into an enum")
    | "enum","vector" -> (t2,[],e) (*TODO*)
    | _,_ -> let t',cs' = type_consistent l t1 t2 in (t',cs',e))
  | Tapp("enum",args1),Tid(i) -> (t2,[],e) (*Need env*)
  | Tid(i),Tapp("enum",args1) -> (t2,[],e) (*Need env*)
  | _,_ -> let t',cs = type_consistent l t1 t2 in (t',cs,e)
