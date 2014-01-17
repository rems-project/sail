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

(* Constraints for nexps, plus the location which added the constraint *)
type nexp_range =
  | LtEq of Parse_ast.l * nexp * nexp
  | Eq of Parse_ast.l * nexp * nexp
  | GtEq of Parse_ast.l * nexp * nexp
  | In of Parse_ast.l * string * int list

type t_params = (string * kind) list
type tannot = ((t_params * t) * tag * nexp_range list) option

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
    ("+",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure)}),External,[]));
  ]


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

(*Is checking for structural equality amongst the types, building constraints for kind Nat. Note: needs an environment to handle type abbreviations*)
let rec type_eq l t1 t2 = 
  match t1.t,t2.t with
  | Tvar v1,Tvar v2 -> if v1 = v2 then (t2,[]) else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Tid v1,Tid v2 -> if v1 = v2 then (t2,[]) else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified") (*lookup for abbrev*)
  | Tfn(tin1,tout1,effect1),Tfn(tin2,tout2,effect2) -> 
    let (tin,cin) = type_eq l tin1 tin2 in
    let (tout,cout) = type_eq l tout1 tout2 in
    let effect = effects_eq l effect1 effect2 in
    (t2,cin@cout)
  | Ttup t1s, Ttup t2s ->
    (t2,(List.flatten (List.map snd (List.map2 (type_eq l) t1s t2s))))
  | Tapp(id1,args1), Tapp(id2,args2) ->
    if id1=id2 && (List.length args2 = List.length args2) then
      (t2,(List.flatten (List.map2 (type_arg_eq l) args1 args2)))
    else eq_error l ("Type application of " ^ id1 ^ " and " ^ id2 ^ " must match")
  | Tuvar _, t -> t1.t <- t2.t; (t2,[])
  | t,Tuvar _ -> t2.t <- t1.t; (t2,[])
  | _,_ -> eq_error l ("Type mismatch")

and type_arg_eq l ta1 ta2 = 
  match ta1,ta2 with
  | TA_typ t1,TA_typ t2 -> snd (type_eq l t1 t2)
  | TA_nexp n1,TA_nexp n2 -> if nexp_eq n1 n2 then [] else [Eq(l,n1,n2)]
  | TA_eft e1,TA_eft e2 -> (ignore(effects_eq l e1 e2);[])
  | TA_ord o1,TA_ord o2 -> (ignore(order_eq l o1 o2);[])
  | _,_ -> eq_error l "Type arguments must be of the same kind" 


let rec type_coerce l t1 t2 = 
  match t1.t,t2.t with
  | Tid v1,Tid v2 -> if v1 = v2 then (None,[]) else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified") (*lookup for abbrev*)
  | Ttup t1s, Ttup t2s ->
    (None,(List.flatten (List.map snd (List.map2 (type_eq l) t1s t2s))))
  | Tapp(id1,args1), Tapp(id2,args2) ->
    if id1=id2 && (List.length args2 = List.length args2) then
      (None,(List.flatten (List.map2 (type_arg_eq l) args1 args2)))
    else eq_error l ("Type application of " ^ id1 ^ " and " ^ id2 ^ " must match")
  | _,_ -> let (t2,consts) = type_eq l t1 t2 in
	     (None,consts)
