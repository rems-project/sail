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
  | Tabbrev of t * t
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
  | External of string option
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

(* eval an nexp as much as possible *)
let rec eval_nexp n =
  match n.nexp with
    | Nconst i -> n
    | Nmult(n1,n2) ->
      (match (eval_nexp n1).nexp,(eval_nexp n2).nexp with
	| Nconst i1, Nconst i2 -> {nexp=Nconst (i1*i2)}
	| _,_ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | Nadd(n1,n2) ->
      (match (eval_nexp n1).nexp,(eval_nexp n2).nexp with
	| Nconst i1, Nconst i2 -> {nexp=Nconst (i1+i2)}
	| _,_ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | Nneg n1 ->
      (match (eval_nexp n1).nexp with
	| Nconst i -> {nexp = Nconst(- i)}
	| _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | N2n n1 ->
      (match (eval_nexp n1).nexp with
	| Nconst i ->
	  let rec two_pow = function
	    | 0 -> 1;
	    | n -> 2* (two_pow n-1) in
	  {nexp = Nconst(two_pow i)}
	| _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | Nvar _ | Nuvar _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const")


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

let rec fresh_var i mkr bindings =
  let v = "v" ^ (string_of_int i) in
  match Envmap.apply bindings v with
  | Some _ -> fresh_var (i+1) mkr bindings
  | None -> mkr v

let fresh_tvar bindings t =
  match t.t with
  | Tuvar { index = i } -> fresh_var i (fun v -> t.t <- Tvar v; (v,{k=K_Typ})) bindings
let fresh_nvar bindings n =
  match n.nexp with
  | Nuvar { nindex = i } -> fresh_var i (fun v -> n.nexp <- Nvar v; (v,{k=K_Nat})) bindings
let fresh_ovar bindings o =
  match o.order with
  | Ouvar { oindex = i } -> fresh_var i (fun v -> o.order <- Ovar v; (v,{k=K_Ord})) bindings
let fresh_evar bindings e =
  match e.effect with
  | Euvar { eindex = i } -> fresh_var i (fun v -> e.effect <- Evar v; (v,{k=K_Efct})) bindings
  
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
    ("register", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("enum", {k = K_Lam( [ {k = K_Nat}; {k= K_Nat}], {k = K_Typ}) });
    ("vector", {k = K_Lam( [ {k = K_Nat}; {k = K_Nat}; {k= K_Ord} ; {k=K_Typ}], {k=K_Typ}) } )
  ]

let nat_typ = {t=Tid "nat"}
let pure_e = {effect=Eset []}
let initial_typ_env =
  Envmap.from_list [
    ("ignore",Some(([("a",{k=K_Typ});("b",{k=K_Efct})],{t=Tfn ({t=Tvar "a"},unit_t,{effect=Evar "b"})}),External None,[],pure_e));
    ("+",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "add"),[],pure_e));
    ("*",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "multiply"),[],pure_e));
    ("-",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "minus"),[],pure_e));
    ("mod",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "mod"),[],pure_e));
    ("quot",Some(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "quot"),[],pure_e));
    (*Type incomplete*)
    (":",Some(([("a",{k=K_Typ});("b",{k=K_Typ});("c",{k=K_Typ})],
	       {t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "b"}])},{t=Tvar "c"},pure_e)}),External (Some "vec_concat"),[],pure_e));
    ("to_num_inc",Some(([("a",{k=K_Typ})],{t= Tfn ({t=Tvar "a"},nat_typ,pure_e)}),External None,[],pure_e));
    ("to_num_dec",Some(([("a",{k=K_Typ})],{t= Tfn ({t=Tvar "a"},nat_typ,pure_e)}),External None,[],pure_e));
    ("to_vec_inc",Some(([("a",{k=K_Typ})],{t= Tfn (nat_typ,{t=Tvar "a"},pure_e)}),External None,[],pure_e));
    ("to_vec_dec",Some(([("a",{k=K_Typ})],{t= Tfn (nat_typ,{t=Tvar "a"},pure_e)}),External None,[],pure_e));
    ("==",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "eq"),[],pure_e));
    ("!=",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "neq"),[],pure_e));
    ("<",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "lt"),[],pure_e));
    (">",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "gt"),[],pure_e));
    ("<_u",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "ltu"),[],pure_e));
    (">_u",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "gtu"),[],pure_e));
    ("is_one",Some(([],{t= Tfn (bit_t,bool_t,pure_e)}),External (Some "is_one"),[],pure_e));
    ("~",Some((["a",{k=K_Typ}],{t= Tfn ({t=Tvar "a"},{t=Tvar "a"},pure_e)}),External (Some "bitwise_not"),[],pure_e));
    ("|",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},{t=Tvar "a"},pure_e)}),External (Some "bitwise_or"),[],pure_e));
    ("^",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},{t=Tvar "a"},pure_e)}),External (Some "bitwise_xor"),[],pure_e));
    ("&",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},{t=Tvar "a"},pure_e)}),External (Some "bitwise_and"),[],pure_e));
    ("^^",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([bit_t;nat_typ])},{t=Tvar "a"},pure_e)}),External (Some "duplicate"),[],pure_e));
    ("<<<",Some((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};nat_typ])},{t=Tvar "a"},pure_e)}),External (Some "bitwise_leftshift"),[],pure_e));
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
  | Tuvar _ -> new_t ()
  | Tid _ -> t
  | Tfn(t1,t2,e) -> {t =Tfn((t_subst s_env t1),(t_subst s_env t2),(e_subst s_env e)) }
  | Ttup(ts) -> { t= Ttup(List.map (t_subst s_env) ts) }
  | Tapp(i,args) -> {t= Tapp(i,List.map (ta_subst s_env) args)}
  | Tabbrev(ti,ta) -> {t = Tabbrev(t_subst s_env ti,t_subst s_env ta) }
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
  | Nuvar _ -> new_n ()
  | Nconst _ -> n
  | N2n n1 -> { nexp = N2n (n_subst s_env n1) }
  | Nneg n1 -> { nexp = Nneg (n_subst s_env n1) }
  | Nadd(n1,n2) -> { nexp = Nadd(n_subst s_env n1,n_subst s_env n2) }
  | Nmult(n1,n2) -> { nexp = Nmult(n_subst s_env n1,n_subst s_env n2) }
and o_subst s_env o =
  match o.order with
  | Ovar i -> (match Envmap.apply s_env i with
               | Some(TA_ord o1) -> o1
               | _ -> o)
  | Ouvar _ -> new_o ()
  | _ -> o
and e_subst s_env e =
  match e.effect with
  | Evar i -> (match Envmap.apply s_env i with
               | Some(TA_eft e1) -> e1
               | _ -> e)
  | Euvar _ -> new_e ()
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

let rec t_remove_unifications s_env t =
  match t.t with
  | Tvar _ | Tid _-> s_env
  | Tuvar _ -> Envmap.insert s_env (fresh_tvar s_env t)
  | Tfn(t1,t2,e) -> e_remove_unifications (t_remove_unifications (t_remove_unifications s_env t1) t2) e
  | Ttup(ts) -> List.fold_right (fun t s_env -> t_remove_unifications s_env t) ts s_env
  | Tapp(i,args) -> List.fold_right (fun t s_env -> ta_remove_unifications s_env t) args s_env
  | Tabbrev(ti,ta) -> (t_remove_unifications (t_remove_unifications s_env ti) ta)
and ta_remove_unifications s_env ta =
  match ta with
  | TA_typ t -> (t_remove_unifications s_env t)
  | TA_nexp n -> (n_remove_unifications s_env n)
  | TA_eft e -> (e_remove_unifications s_env e)
  | TA_ord o -> (o_remove_unifications s_env o)
and n_remove_unifications s_env n =
  match n.nexp with
  | Nvar _ | Nconst _-> s_env
  | Nuvar _ -> Envmap.insert s_env (fresh_nvar s_env n)
  | N2n n1 | Nneg n1 -> (n_remove_unifications s_env n1)
  | Nadd(n1,n2) | Nmult(n1,n2) -> (n_remove_unifications (n_remove_unifications s_env n1) n2)
and o_remove_unifications s_env o =
  match o.order with
  | Ouvar _ -> Envmap.insert s_env (fresh_ovar s_env o)
  | _ -> s_env
and e_remove_unifications s_env e =
  match e.effect with
  | Euvar _ -> Envmap.insert s_env (fresh_evar s_env e)
  | _ -> s_env

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
    | Tabbrev(ti,ta) -> (t_to_string ti) ^ " : " ^ (t_to_string ta)
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

let tag_to_string = function
  | Emp -> "Emp"
  | External None -> "External" 
  | External (Some s) -> "External " ^ s
  | Default -> "Default"
  | Constructor -> "Constructor"
  | Enum -> "Enum"
  | Spec -> "Spec"

let tannot_to_string = function
  | None -> "No tannot"
  | Some((vars,t),tag,ncs,ef) ->
    "Tannot: type = " ^ (t_to_string t) ^ " tag = " ^ tag_to_string tag ^ " constraints = not printing effect = " ^ e_to_string ef

let rec t_to_typ t =
  Typ_aux (
   (match t.t with
    | Tid i -> Typ_id (Id_aux((Id i), Parse_ast.Unknown))
    | Tvar i -> Typ_var (Kid_aux((Var i),Parse_ast.Unknown)) 
    | Tfn(t1,t2,e) -> Typ_fn (t_to_typ t1, t_to_typ t2, e_to_ef e)
    | Ttup ts -> Typ_tup(List.map t_to_typ ts)
    | Tapp(i,args) -> Typ_app(Id_aux((Id i), Parse_ast.Unknown),List.map targ_to_typ_arg args)), Parse_ast.Unknown)
and targ_to_typ_arg targ = 
 Typ_arg_aux( 
  (match targ with
    | TA_nexp n -> Typ_arg_nexp (n_to_nexp n) 
    | TA_typ t -> Typ_arg_typ (t_to_typ t)
    | TA_ord o -> Typ_arg_order (o_to_order o)
    | TA_eft e -> Typ_arg_effect (e_to_ef e)), Parse_ast.Unknown)
and n_to_nexp n =
  Nexp_aux(
  (match n.nexp with
    | Nvar i -> Nexp_var (Kid_aux((Var i),Parse_ast.Unknown)) 
    | Nconst i -> Nexp_constant i 
    | Nmult(n1,n2) -> Nexp_times(n_to_nexp n1,n_to_nexp n2) 
    | Nadd(n1,n2) -> Nexp_sum(n_to_nexp n1,n_to_nexp n2) 
    | N2n n -> Nexp_exp (n_to_nexp n) 
    | Nneg n -> Nexp_neg (n_to_nexp n)), Parse_ast.Unknown)
and e_to_ef ef =
 Effect_aux( 
  (match ef.effect with
    | Evar i -> Effect_var (Kid_aux((Var i),Parse_ast.Unknown)) 
    | Eset effects -> Effect_set effects), Parse_ast.Unknown)
and o_to_order o =
 Ord_aux( 
  (match o.order with
    | Ovar i -> Ord_var (Kid_aux((Var i),Parse_ast.Unknown)) 
    | Oinc -> Ord_inc 
    | Odec -> Ord_dec), Parse_ast.Unknown)


let rec get_abbrev d_env t =
  match t.t with
    | Tid i ->
      (match Envmap.apply d_env.abbrevs i with
	| Some(Some((params,ta),tag,cs,efct)) ->
          let ta,cs,efct = subst params ta cs efct in
          let ta,cs',efct' = get_abbrev d_env ta in
          (match ta.t with
          | Tabbrev(t',ta) -> ({t=Tabbrev({t=Tabbrev(t,t')},ta)},cs@cs',union_effects efct efct')
          | _ -> ({t = Tabbrev(t,ta)},cs,efct))
	| _ -> t,[],pure_e)
    | Tapp(i,args) ->
      (match Envmap.apply d_env.abbrevs i with
	| Some(Some((params,ta),tag,cs,efct)) ->
	  let env = Envmap.from_list2 (List.map fst params) args in
          let ta,cs',efct' = get_abbrev d_env (t_subst env ta) in
          (match ta.t with
          | Tabbrev(t',ta) -> ({t=Tabbrev({t=Tabbrev(t,t')},ta)},cs_subst env (cs@cs'),e_subst env (union_effects efct efct'))
          | _ -> ({t = Tabbrev(t,ta)},cs_subst env cs,e_subst env efct))
	| _ -> t,[],pure_e)
    | _ -> t,[],pure_e

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
let rec type_consistent_internal l d_env t1 cs1 t2 cs2 = 
  let t1,cs1',_ = get_abbrev d_env t1 in
  let t2,cs2',_ = get_abbrev d_env t2 in
  let cs1,cs2 = cs1@cs1',cs2@cs2' in
  match t1.t,t2.t with
  | Tabbrev(_,t1),Tabbrev(_,t2) -> type_consistent_internal l d_env t1 cs1 t2 cs2
  | Tabbrev(_,t1),_ -> type_consistent_internal l d_env t1 cs1 t2 cs2
  | _,Tabbrev(_,t2) -> type_consistent_internal l d_env t1 cs1 t2 cs2
  | Tvar v1,Tvar v2 -> 
    if v1 = v2 then (t2,[]) 
    else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Tid v1,Tid v2 -> 
    if v1 = v2 then (t2,cs1@cs2) 
    else eq_error l ("Types " ^ v1 ^ " and " ^ v2 ^ " do not match")
  | Tapp("enum",[TA_nexp b1;TA_nexp r1;]),Tapp("enum",[TA_nexp b2;TA_nexp r2;]) -> 
    if (nexp_eq b1 b2)&&(nexp_eq r1 r2) then (t2,[])
    else (t2, cs1@cs2@[GtEq(l,b1,b2);LtEq(l,r1,r2)])
  | Tapp(id1,args1), Tapp(id2,args2) ->
    let la1,la2 = List.length args1, List.length args2 in
    if id1=id2 && la1 = la2 then (t2,cs1@cs2@(List.flatten (List.map2 (type_arg_eq l d_env) args1 args2)))
    else eq_error l ("Type application of " ^ (t_to_string t1) ^ " and " ^ (t_to_string t2) ^ " must match")
  | Tfn(tin1,tout1,effect1),Tfn(tin2,tout2,effect2) -> 
    let (tin,cin) = type_consistent l d_env tin1 tin2 in
    let (tout,cout) = type_consistent l d_env tout1 tout2 in
    let effect = effects_eq l effect1 effect2 in
    (t2,cs1@cs2@cin@cout)
  | Ttup t1s, Ttup t2s ->
    (t2,cs1@cs2@(List.flatten (List.map snd (List.map2 (type_consistent l d_env) t1s t2s))))
  | Tuvar _, t -> t1.t <- t2.t; (t2,cs1@cs2)
  | t,Tuvar _ -> t2.t <- t1.t; (t2,cs1@cs2)
  | _,_ -> eq_error l ("Type mismatch found " ^ (t_to_string t1) ^ " but expected a " ^ (t_to_string t2))

and type_arg_eq l d_env ta1 ta2 = 
  match ta1,ta2 with
  | TA_typ t1,TA_typ t2 -> snd (type_consistent l d_env t1 t2)
  | TA_nexp n1,TA_nexp n2 -> if nexp_eq n1 n2 then [] else [Eq(l,n1,n2)]
  | TA_eft e1,TA_eft e2 -> (ignore(effects_eq l e1 e2);[])
  | TA_ord o1,TA_ord o2 -> (ignore(order_eq l o1 o2);[])
  | _,_ -> eq_error l "Type arguments must be of the same kind" 

and type_consistent l d_env t1 t2 =
  type_consistent_internal l d_env t1 [] t2 []

let rec type_coerce_internal l d_env t1 cs1 e t2 cs2 = 
  let t1,cs1',_ = get_abbrev d_env t1 in
  let t2,cs2',_ = get_abbrev d_env t2 in
  let cs1,cs2 = cs1@cs1',cs2@cs2' in
  match t1.t,t2.t with
  | Tabbrev(_,t1),Tabbrev(_,t2) -> type_coerce_internal l d_env t1 cs1 e t2 cs2
  | Tabbrev(_,t1),_ -> type_coerce_internal l d_env t1 cs1 e t2 cs2
  | _,Tabbrev(_,t2) -> type_coerce_internal l d_env t1 cs1 e t2 cs2
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
	(t2,cs,E_aux(E_app((Id_aux(Id "to_num_inc",l)),[e]),(l,Some(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(l,b2,{nexp=Nconst 0});Eq(l,r2,{nexp=N2n({nexp=Nadd({nexp=Nneg b1},r1)})})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_num_dec",l)),[e]),(l,Some(([],t2),External None,cs,pure_e))))
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
	(t2,cs,E_aux(E_app((Id_aux(Id "to_vec_inc",l)),[e]),(l,Some(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(l,b1,{nexp=N2n{nexp=Nadd(b2,{nexp=Nneg r2})}});
		  Eq(l,r1,b1)] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_vec_dec",l)),[e]),(l,Some(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
	eq_error l "Cannot convert an enum to a vector without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert an enum into a non-bit vector"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or enum is not properly kinded"))
    | "register",_ ->
      (match args1 with
	| [TA_typ t] ->
          let new_e = E_aux(E_cast(t_to_typ t,e),(l,Some(([],t),External None,[],pure_e))) in (*Wrong effect, should be reading a register*)
	  type_coerce l d_env t new_e t2
	| _ -> raise (Reporting_basic.err_unreachable l "register is not properly kinded"))
    | _,_ -> 
      let t',cs' = type_consistent l d_env t1 t2 in (t',cs',e))
  | Tid("bit"),Tapp("vector",[TA_nexp {nexp=Nconst i};TA_nexp r1;TA_ord o;TA_typ {t=Tid "bit"}]) ->
    let cs = [Eq(l,r1,{nexp = Nconst 1})] in
    (t2,cs,E_aux(E_vector_indexed [(i,e)],(l,Some(([],t2),Emp,cs,pure_e))))    
  | Tapp("vector",[TA_nexp ({nexp=Nconst i} as b1);TA_nexp r1;TA_ord o;TA_typ {t=Tid "bit"}]),Tid("bit") ->
    let cs = [Eq(l,r1,{nexp = Nconst 1})] in
    (t2,cs,E_aux((E_vector_access (e,(E_aux(E_lit(L_aux(L_num i,l)),(l,Some(([],{t=Tapp("enum",[TA_nexp b1;TA_nexp {nexp=Nconst 0}])}),Emp,cs,pure_e)))))),
                 (l,Some(([],t2),Emp,cs,pure_e))))
  | Tid("bit"),Tapp("enum",[TA_nexp b1;TA_nexp r1]) ->
    let t',cs'= type_consistent l d_env {t=Tapp("enum",[TA_nexp{nexp=Nconst 0};TA_nexp{nexp=Nconst 1}])} t2 in
    (t2,cs',E_aux(E_case (e,[Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_zero,l)),(l,Some(([],t1),Emp,[],pure_e))),
					     E_aux(E_lit(L_aux(L_num 0,l)),(l,Some(([],t2),Emp,[],pure_e)))),
				     (l,Some(([],t2),Emp,[],pure_e)));
			     Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_one,l)),(l,Some(([],t1),Emp,[],pure_e))),
					     E_aux(E_lit(L_aux(L_num 1,l)),(l,Some(([],t2),Emp,[],pure_e)))),
				     (l,Some(([],t2),Emp,[],pure_e)));]),
		  (l,Some(([],t2),Emp,[],pure_e))))    
  | Tapp("enum",[TA_nexp b1;TA_nexp r1;]),Tid("bit") ->
    let t',cs'= type_consistent l d_env t1 {t=Tapp("enum",[TA_nexp{nexp=Nconst 0};TA_nexp{nexp=Nconst 1}])} 
    in (t2,cs',E_aux(E_if(E_aux(E_app(Id_aux(Id "is_zero",l),[e]),(l,Some(([],bool_t),Emp,[],pure_e))),
			  E_aux(E_lit(L_aux(L_zero,l)),(l,Some(([],bit_t),Emp,[],pure_e))),
			  E_aux(E_lit(L_aux(L_one,l)),(l,Some(([],bit_t),Emp,[],pure_e)))),
		     (l,Some(([],bit_t),Emp,cs',pure_e))))
  | Tapp("enum",[TA_nexp b1;TA_nexp r1;]),Tid(i) -> 
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
    | None -> eq_error l ("Type mismatch: found a " ^ (t_to_string t1) ^ " but expected " ^ (t_to_string t2)))
  | Tid("bit"),Tid("bool") ->
    let e' = E_aux(E_app((Id_aux(Id "is_one",l)),[e]),(l,Some(([],bool_t),External None,[],pure_e))) in
    (t2,[],e')
  | Tid(i),Tapp("enum",[TA_nexp b1;TA_nexp r1;]) -> 
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
    | None -> eq_error l ("Type mismatch: " ^ (t_to_string t1) ^ " , " ^ (t_to_string t2)))
  | _,_ -> let t',cs = type_consistent l d_env t1 t2 in (t',cs,e)

and type_coerce l d_env t1 e t2 = type_coerce_internal l d_env t1 [] e t2 []

let resolve_constraints a = a


let check_tannot l annot constraints efs = 
  match annot with
  | Some((params,t),tag,cs,e) -> 
    effects_eq l efs e;
    let params = Envmap.to_list (t_remove_unifications (Envmap.from_list params) t) in
    Some((params,t),tag,cs,e)
  | None -> raise (Reporting_basic.err_unreachable l "check_tannot given the place holder annotation")

