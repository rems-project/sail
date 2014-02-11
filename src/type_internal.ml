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
  | InS of Parse_ast.l * nexp * int list

type t_params = (string * kind) list
type tannot = ((t_params * t) * tag * nexp_range list * effect) option
type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type rec_env = (string * rec_kind * ((string * tannot) list))
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap; 
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : rec_env list;
 }  

type exp = tannot Ast.exp

let rec effect_remove_dups = function
  | [] -> []
  | (BE_aux(be,l))::es -> 
    if (List.exists (fun (BE_aux(be',_)) -> be = be') es)
    then effect_remove_dups es
    else (BE_aux(be,l))::(effect_remove_dups es)
      
let add_effect e ef =
  match ef.effect with
  | Evar s -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "add_effect given var instead of uvar")
  | Eset bases -> {effect = Eset (effect_remove_dups (e::bases))}
  | Euvar _ -> ef.effect <- Eset [e]; ef

let union_effects e1 e2 =
  match e1.effect,e2.effect with
  | Evar s,_ | _,Evar s -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "union_effects given var(s) instead of uvar(s)")
  | Euvar _,_ -> e1.effect <- e2.effect; e2
  | _,Euvar _ -> e2.effect <- e1.effect; e2
  | Eset b1, Eset b2 -> {effect= Eset (effect_remove_dups (b1@b2))}  

let rec lookup_record_typ (typ : string) (env : rec_env list) : rec_env option =
  match env with
    | [] -> None
    | ((id,_,_) as r)::env -> 
      if typ = id then Some(r) else lookup_record_typ typ env

let rec fields_match f1 f2 =
  match f1 with
    | [] -> true
    | f::fs -> (List.mem_assoc f f2) && fields_match fs f2

let rec lookup_record_fields (fields : string list) (env : rec_env list) : rec_env option =
  match env with
    | [] -> None
    | ((id,r,fs) as re)::env ->
      if ((List.length fields) = (List.length fs)) &&
	 (fields_match fields fs) then
	Some re
      else lookup_record_fields fields env

let rec lookup_possible_records (fields : string list) (env : rec_env list) : rec_env list =
  match env with
    | [] -> []
    | ((id,r,fs) as re)::env ->
      if (((List.length fields) <= (List.length fs)) &&
	  (fields_match fields fs))
      then re::(lookup_possible_records fields env)
      else lookup_possible_records fields env

let lookup_field_type (field: string) ((id,r_kind,fields) : rec_env) : tannot =
  if List.mem_assoc field fields
  then List.assoc field fields
  else None

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
  
let nat_t = {t = Tapp("enum",[TA_nexp{nexp= Nconst 0};TA_nexp{nexp = Nconst max_int};])}
let unit_t = { t = Tid "unit" }
let bit_t = {t = Tid "bit" }
let bool_t = {t = Tid "bool" }

let initial_kind_env = 
  Envmap.from_list [ 
    ("bool", {k = K_Typ});
    ("nat", {k = K_Typ});
    ("unit", {k = K_Typ});
    ("bit", {k = K_Typ});
    ("list", {k = K_Lam( [{k = K_Typ}], {k = K_Typ})});
    ("reg", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("enum", {k = K_Lam( [ {k = K_Nat}; {k= K_Nat}], {k = K_Typ}) });
    ("vector", {k = K_Lam( [ {k = K_Nat}; {k = K_Nat}; {k= K_Ord} ; {k=K_Typ}], {k=K_Typ}) } )
  ]

let nat_typ = {t=Tid "nat"}
let pure_e = {effect=Eset []}
let initial_typ_env =
  Envmap.from_list [
    ("ignore",Some(([("a",{k=K_Typ});("b",{k=K_Efct})],{t=Tfn ({t=Tvar "a"},unit_t,{effect=Evar "b"})}),External,[],pure_e));
    ("+",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External,[],pure_e));
    ("*",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External,[],pure_e));    
  ]

let initial_abbrev_env =
  Envmap.from_list [
    ("nat",Some(([],nat_t),Emp,[],pure_e));
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

let rec cs_subst t_env cs =
  match cs with
    | [] -> []
    | Eq(l,n1,n2)::cs -> Eq(l,n_subst t_env n1,n_subst t_env n2)::(cs_subst t_env cs)
    | GtEq(l,n1,n2)::cs -> GtEq(l,n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | LtEq(l,n1,n2)::cs -> LtEq(l,n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | In(l,s,ns)::cs -> InS(l,n_subst t_env {nexp=Nvar s},ns)::(cs_subst t_env cs)
    | InS(l,n,ns)::cs -> InS(l,n_subst t_env n,ns)::(cs_subst t_env cs)

let subst k_env t cs e =
  let subst_env = Envmap.from_list
    (List.map (fun (id,k) -> (id, 
                              match k.k with
                              | K_Typ -> TA_typ (new_t ())
                              | K_Nat -> TA_nexp (new_n ())
                              | K_Ord -> TA_ord (new_o ())
                              | K_Efct -> TA_eft (new_e ())
                              | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "substitution given an environment with a non-base-kind kind"))) k_env) 
  in
  t_subst subst_env t, cs_subst subst_env cs, e_subst subst_env e

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let rec t_to_string t = 
  match t.t with
    | Tid i -> i
    | Tvar i -> "'" ^ i
    | Tfn(t1,t2,e) -> (t_to_string t1) ^ " -> " ^ (t_to_string t2) ^ " effect " ^ e_to_string e
    | Ttup(tups) -> "(" ^ string_of_list " * " t_to_string tups ^ ")"
    | Tapp(i,args) -> i ^ "<" ^  string_of_list ", " targ_to_string args ^ ">"
    | Tuvar({index = i;subst = a}) -> string_of_int i ^ "()"
and targ_to_string = function
  | TA_typ t -> t_to_string t
  | TA_nexp n -> n_to_string n
  | TA_eft e -> e_to_string e
  | TA_ord o -> o_to_string o
and n_to_string n =
  match n.nexp with
    | Nvar i -> "'" ^ i
    | Nconst i -> string_of_int i
    | Nadd(n1,n2) -> (n_to_string n1) ^ " + " ^ (n_to_string n2)
    | Nmult(n1,n2) -> (n_to_string n1) ^ " * " ^ (n_to_string n2)
    | N2n n -> "2**" ^ (n_to_string n)
    | Nneg n -> "-" ^ (n_to_string n)
    | Nuvar({nindex=i;nsubst=a}) -> string_of_int i ^ "()"
and e_to_string e = 
  match e.effect with
  | Evar i -> "'" ^ i
  | Eset es -> if []=es then "pure" else "{" ^ "effects not printing" ^"}"
  | Euvar({eindex=i;esubst=a}) -> string_of_int i ^ "()"
and o_to_string o = 
  match o.order with
  | Ovar i -> "'" ^ i
  | Oinc -> "inc"
  | Odec -> "dec"
  | Ouvar({oindex=i;osubst=a}) -> string_of_int i ^ "()"

let get_abbrev d_env t =
  match t.t with
    | Tid i ->
      (match Envmap.apply d_env.abbrevs i with
	| Some(Some((params,t),tag,cs,efct)) ->
	  Some(subst params t cs efct)
	| _ -> None)
    | Tapp(i,args) ->
      (match Envmap.apply d_env.abbrevs i with
	| Some(Some((params,t),tag,cs,efct)) ->
	  let env = Envmap.from_list2 (List.map fst params) args in
	  Some(t_subst env t, cs_subst env cs, e_subst env efct)
	| _ -> None)
    | _ -> None


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
  When considering two enum type applications, will check for consistency instead of equality*)
let rec type_consistent l d_env t1 t2 = 
  match t1.t,t2.t with
  | Tvar v1,Tvar v2 -> 
    if v1 = v2 then (t2,[]) 
    else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Tid v1,Tid v2 -> 
    if v1 = v2 then (t2,[]) 
    else (match get_abbrev d_env t1,get_abbrev d_env t2 with
      | Some(t1,cs1,e1),Some(t2,cs2,e2) ->
	let t',cs' = type_consistent l d_env t1 t2 in
	t',cs1@cs2@cs'
      | Some(t1,cs1,e1),None ->
	let t',cs' = type_consistent l d_env t1 t2 in
	t',cs1@cs'
      | None,Some(t2,cs2,e2) ->
	let t',cs' = type_consistent l d_env t1 t2 in
	t',cs2@cs'
      | None,None ->  eq_error l ("Types " ^ v1 ^ " and " ^ v2 ^ " do not match"))
  | Tapp("enum",[TA_nexp b1;TA_nexp r1;]),Tapp("enum",[TA_nexp b2;TA_nexp r2;]) -> 
    if (nexp_eq b1 b2)&&(nexp_eq r1 r2) then (t2,[])
    else (t2, [GtEq(l,b1,b2);LtEq(l,r1,r2)])
  | Tapp(id1,args1), Tapp(id2,args2) ->
    let la1,la2 = List.length args1, List.length args2 in
    if id1=id2 && la1 = la2 then (t2,(List.flatten (List.map2 (type_arg_eq l d_env) args1 args2)))
    else
      (match get_abbrev d_env t1,get_abbrev d_env t2 with
	| Some(t1,cs1,e1),Some(t2,cs2,e2) ->
	  let t',cs' = type_consistent l d_env t1 t2 in
	  t',cs1@cs2@cs'
	| Some(t1,cs1,e1),None ->
	  let t',cs' = type_consistent l d_env t1 t2 in
	  t',cs1@cs'
	| None,Some(t2,cs2,e2) ->
	  let t',cs' = type_consistent l d_env t1 t2 in
	  t',cs2@cs'
	| None,None -> eq_error l ("Type application of " ^ (t_to_string t1) ^ " and " ^ (t_to_string t2) ^ " must match"))
  | Tfn(tin1,tout1,effect1),Tfn(tin2,tout2,effect2) -> 
    let (tin,cin) = type_consistent l d_env tin1 tin2 in
    let (tout,cout) = type_consistent l d_env tout1 tout2 in
    let effect = effects_eq l effect1 effect2 in
    (t2,cin@cout)
  | Ttup t1s, Ttup t2s ->
    (t2,(List.flatten (List.map snd (List.map2 (type_consistent l d_env) t1s t2s))))
  | Tuvar _, t -> t1.t <- t2.t; (t2,[])
  | t,Tuvar _ -> t2.t <- t1.t; (t2,[])
  | _,_ ->
    (match get_abbrev d_env t1,get_abbrev d_env t2 with
      | Some(t1,cs1,e1),Some(t2,cs2,e2) ->
	let t',cs' = type_consistent l d_env t1 t2 in
	t',cs1@cs2@cs'
      | Some(t1,cs1,e1),None ->
	let t',cs' = type_consistent l d_env t1 t2 in
	t',cs1@cs'
      | None,Some(t2,cs2,e2) ->
	let t',cs' = type_consistent l d_env t1 t2 in
	t',cs2@cs'
      | None,None -> eq_error l ("Type mismatch :" ^ (t_to_string t1) ^ " , " ^ (t_to_string t2)))

and type_arg_eq l d_env ta1 ta2 = 
  match ta1,ta2 with
  | TA_typ t1,TA_typ t2 -> snd (type_consistent l d_env t1 t2)
  | TA_nexp n1,TA_nexp n2 -> if nexp_eq n1 n2 then [] else [Eq(l,n1,n2)]
  | TA_eft e1,TA_eft e2 -> (ignore(effects_eq l e1 e2);[])
  | TA_ord o1,TA_ord o2 -> (ignore(order_eq l o1 o2);[])
  | _,_ -> eq_error l "Type arguments must be of the same kind" 

let rec type_coerce l d_env t1 e t2 = 
  match t1.t,t2.t with
  | Ttup t1s, Ttup t2s ->
    let tl1,tl2 = List.length t1s,List.length t2s in
    if tl1=tl2 then 
      let ids = List.map (fun _ -> Id_aux(Id (new_id ()),l)) t1s in
      let vars = List.map2 (fun i t -> E_aux(E_id(i),(l,Some(([],t),Emp,[],pure_e)))) ids t1s in
      let (coerced_ts,cs,coerced_vars) = 
        List.fold_right2 (fun v (t1,t2) (ts,cs,es) -> let (t',c',e') = type_coerce l d_env t1 v t2 in
                                                      ((t'::ts),c'@cs,(e'::es)))
          vars (List.combine t1s t2s) ([],[],[]) in
      if vars = coerced_vars then (t2,cs,e)
      else let e' = E_aux(E_case(e,[(Pat_aux(Pat_exp(P_aux(P_tup (List.map2 (fun i t -> P_aux(P_id i,(l,(Some(([],t),Emp,[],pure_e))))) ids t1s),(l,Some(([],t1),Emp,[],pure_e))),
                                               E_aux(E_tuple coerced_vars,(l,Some(([],t2),Emp,cs,pure_e)))),
                                             (l,Some(([],t2),Emp,[],pure_e))))]),
                          (l,(Some(([],t2),Emp,[],pure_e)))) in
           (t2,cs,e')
    else eq_error l ("A tuple of length " ^ (string_of_int tl1) ^ " cannot be used where a tuple of length " ^ (string_of_int tl2) ^ " is expected")
  | Tapp(id1,args1),Tapp(id2,args2) ->
    if id1=id2 
    then let t',cs' = type_consistent l d_env t1 t2 in (t',cs',e)
    else (match id1,id2 with
    | "vector","enum" -> 
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(l,b2,{nexp=Nconst 0});Eq(l,r2,{nexp=N2n({nexp=Nadd(b1,r1)})})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_num_inc",l)),[e]),(l,Some(([],t2),Emp,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(l,b2,{nexp=Nconst 0});Eq(l,r2,{nexp=N2n({nexp=Nadd({nexp=Nneg b1},r1)})})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_num_dec",l)),[e]),(l,Some(([],t2),Emp,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
	eq_error l "Cannot convert a vector to an enum without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert non-bit vector into an enum"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or enum is not properly kinded"))
    | "enum","vector" -> 
      (match args2,args1 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(l,b1,{nexp=Nconst 0});Eq(l,{nexp=Nadd(b2,r2)},{nexp=N2n r1})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_vec_inc",l)),[e]),(l,Some(([],t2),Emp,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(l,b1,{nexp=N2n{nexp=Nadd(b2,{nexp=Nneg r2})}});
		  Eq(l,r1,b1)] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_vec_dec",l)),[e]),(l,Some(([],t2),Emp,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
	eq_error l "Cannot convert an enum to a vector without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert an enum into a non-bit vector"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or enum is not properly kinded"))
    | _,_ -> 
      (match get_abbrev d_env t1,get_abbrev d_env t2 with
	| Some(t1,cs1,ef1),Some(t2,cs2,ef2) ->
	  let t',cs',e' = type_coerce l d_env t1 e t2 in
	  (t',cs1@cs2@cs',e')
	| Some(t1,cs1,ef1),None ->
	  let t',cs',e' = type_coerce l d_env t1 e t2 in
	  (t',cs1@cs',e')
	| None,Some(t2,cs2,ef2) ->
	  let t',cs',e' = type_coerce l d_env t1 e t2 in
	  (t',cs2@cs',e')
	| None,None ->
	  let t',cs' = type_consistent l d_env t1 t2 in (t',cs',e)))
  | Tapp("enum",[TA_nexp b1;TA_nexp r1;]),Tid("bit") ->
    let t',cs'= type_consistent l d_env t1 {t=Tapp("enum",[TA_nexp{nexp=Nconst 0};TA_nexp{nexp=Nconst 1}])} 
    in (t2,cs',E_aux(E_if(E_aux(E_app(Id_aux(Id "is_zero",l),[e]),(l,Some(([],bool_t),Emp,[],pure_e))),
			  E_aux(E_lit(L_aux(L_zero,l)),(l,Some(([],bit_t),Emp,[],pure_e))),
			  E_aux(E_lit(L_aux(L_one,l)),(l,Some(([],bit_t),Emp,[],pure_e)))),
		     (l,Some(([],bit_t),Emp,cs',pure_e))))
  | Tapp("enum",[TA_nexp b1;TA_nexp r1;]),Tid(i) -> 
    (match get_abbrev d_env t2 with
      | Some(t2,cs2,ef2) ->
	let t',cs',e' = type_coerce l d_env t1 e t2 in
	(t',cs2@cs',e')
      | None -> 
	(match Envmap.apply d_env.enum_env i with
	  | Some(enums) -> 
	    (t2,[Eq(l,b1,{nexp=Nconst 0});LtEq(l,r1,{nexp=Nconst (List.length enums)})],
	     E_aux(E_case(e,
			  List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_lit(L_aux((L_num i),l)),
								      (l,Some(([],t1),Emp,[],pure_e))),
								E_aux(E_id(Id_aux(Id a,l)),
								      (l,Some(([],t2),Emp,[],pure_e)))),
							(l,Some(([],t2),Emp,[],pure_e)))) enums),
		   (l,Some(([],t2),Emp,[],pure_e))))
	  | None -> eq_error l ("Type mismatch: " ^ (t_to_string t1) ^ " , " ^ (t_to_string t2))))
  | Tid("bit"),Tid("bool") ->
    let e' = E_aux(E_app((Id_aux(Id "is_one",l)),[e]),(l,Some(([],bool_t),External,[],pure_e))) in
    (t2,[],e')
  | Tid(i),Tapp("enum",[TA_nexp b1;TA_nexp r1;]) -> 
    (match get_abbrev d_env t1 with
      | Some(t1,cs1,ef1) ->
	let t',cs',e' = type_coerce l d_env t1 e t2 in
	(t',cs1@cs',e')
      | None -> 
	(match Envmap.apply d_env.enum_env i with
	  | Some(enums) -> 
	    (t2,[Eq(l,b1,{nexp=Nconst 0});GtEq(l,r1,{nexp=Nconst (List.length enums)})],
	     E_aux(E_case(e,
			  List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_id(Id_aux(Id a,l)),
								      (l,Some(([],t1),Emp,[],pure_e))),
								E_aux(E_lit(L_aux((L_num i),l)),
								      (l,Some(([],t2),Emp,[],pure_e)))),
							(l,Some(([],t2),Emp,[],pure_e)))) enums),
		   (l,Some(([],t2),Emp,[],pure_e))))
	  | None -> eq_error l ("Type mismatch: " ^ (t_to_string t1) ^ " , " ^ (t_to_string t2))))
  | _,_ -> 
    (match get_abbrev d_env t1,get_abbrev d_env t2 with
      | Some(t1,cs1,ef1),Some(t2,cs2,ef2) -> 
	let t',cs',e' = type_coerce l d_env t1 e t2 in
	(t',cs'@cs1@cs2,e')
      | Some(t1,cs1,ef1),None ->
	let t',cs',e' = type_coerce l d_env t1 e t2 in
	(t',cs'@cs1,e')
      | None,Some(t2,cs2,ef2) ->
	let t',cs',e' = type_coerce l d_env t1 e t2 in
	(t',cs'@cs2,e')
      | None,None -> let t',cs = type_consistent l d_env t1 t2 in (t',cs,e))
