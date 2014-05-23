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
and n_uvar = { nindex : int; mutable nsubst : nexp option; mutable nin : bool; }
and effect = { mutable effect : effect_aux }
and effect_aux =
  | Evar of string
  | Eset of base_effect list
  | Euvar of e_uvar
and e_uvar = { eindex : int; mutable esubst : effect option }
and order = { mutable order : order_aux }
and order_aux =
  | Ovar of string
  | Oinc
  | Odec
  | Ouvar of o_uvar
and o_uvar = { oindex : int; mutable osubst : order option }
and t_arg =
  | TA_typ of t
  | TA_nexp of nexp
  | TA_eft of effect
  | TA_ord of order 

type tag =
  | Emp_local
  | Emp_global
  | External of string option
  | Default
  | Constructor
  | Enum
  | Spec

type constraint_origin =
  | Patt of Parse_ast.l
  | Expr of Parse_ast.l
  | Fun of Parse_ast.l
  | Specc of Parse_ast.l

(* Constraints for nexps, plus the location which added the constraint *)
type nexp_range =
  | LtEq of constraint_origin * nexp * nexp
  | Eq of constraint_origin * nexp * nexp
  | GtEq of constraint_origin * nexp * nexp
  | In of constraint_origin * string * int list
  | InS of constraint_origin * nexp * int list (* This holds the given value for string after a substitution *)
  | CondCons of constraint_origin * nexp_range list * nexp_range list
  | BranchCons of constraint_origin * nexp_range list

type t_params = (string * kind) list
type tannot = 
  | NoTyp
  | Base of (t_params * t) * tag * nexp_range list * effect
  | Overload of tannot * tannot list (* First tannot is the most polymorphic version; the list includes all variants. All t to be Tfn *)

(*type tannot = ((t_params * t) * tag * nexp_range list * effect) option*)
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

let get_index n =
 match n.nexp with
   | Nuvar {nindex = i} -> i
   | _ -> assert false

let get_c_loc = function
  | Patt l | Expr l | Specc l | Fun l -> l

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let rec t_to_string t = 
  match t.t with
    | Tid i -> i
    | Tvar i -> "'" ^ i
    | Tfn(t1,t2,e) -> (t_to_string t1) ^ " -> " ^ (t_to_string t2) ^ " effect " ^ e_to_string e
    | Ttup(tups) -> "(" ^ string_of_list ", " t_to_string tups ^ ")"
    | Tapp(i,args) -> i ^ "<" ^  string_of_list ", " targ_to_string args ^ ">"
    | Tabbrev(ti,ta) -> (t_to_string ti) ^ " : " ^ (t_to_string ta)
    | Tuvar({index = i;subst = a}) -> "Tu_" ^ string_of_int i ^ "("^ (match a with | None -> "None" | Some t -> t_to_string t) ^")"
and targ_to_string = function
  | TA_typ t -> t_to_string t
  | TA_nexp n -> n_to_string n
  | TA_eft e -> e_to_string e
  | TA_ord o -> o_to_string o
and n_to_string n =
  match n.nexp with
    | Nvar i -> "'" ^ i
    | Nconst i -> string_of_int i
    | Nadd(n1,n2) -> "("^ (n_to_string n1) ^ " + " ^ (n_to_string n2) ^")"
    | Nmult(n1,n2) -> "(" ^ (n_to_string n1) ^ " * " ^ (n_to_string n2) ^ ")"
    | N2n n -> "2**" ^ (n_to_string n)
    | Nneg n -> "-" ^ (n_to_string n)
    | Nuvar({nindex=i;nsubst=a}) -> "Nu_" ^ string_of_int i ^ "()"
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
  | Emp_local -> "Emp_local"
  | Emp_global -> "Emp_global"
  | External None -> "External" 
  | External (Some s) -> "External " ^ s
  | Default -> "Default"
  | Constructor -> "Constructor"
  | Enum -> "Enum"
  | Spec -> "Spec"

let rec tannot_to_string = function
  | NoTyp -> "No tannot"
  | Base((vars,t),tag,ncs,ef) ->
    "Tannot: type = " ^ (t_to_string t) ^ " tag = " ^ tag_to_string tag ^ " constraints = not printing effect = " ^ e_to_string ef
  | Overload(poly,variants) ->
    "Overloaded: poly = " ^ tannot_to_string poly

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
  else NoTyp

let rec compare_nexps n1 n2 =
  match n1.nexp,n2.nexp with 
  | Nconst n1, Nconst n2 -> compare n1 n2
  | Nconst _ , _        -> -1
  | _        , Nconst _ ->  1
  | Nvar i1  , Nvar i2  ->  compare i1 i2
  | Nvar _   , _        -> -1
  | _        , Nvar _   ->  1 
  | Nuvar {nindex = n1}, Nuvar {nindex = n2} -> compare n1 n2
  | Nuvar _  , _        -> -1
  | _        , Nuvar _  ->  1
  | Nmult(_,n1),Nmult(_,n2) -> compare_nexps n1 n2
  | Nmult _  , _        -> -1
  | _        , Nmult _  ->  1
  | Nadd(n1,_),Nadd(n2,_) -> compare_nexps n1 n2
  | Nadd _   , _        -> -1
  | _        , Nadd _   ->  1
  | N2n n1   , N2n n2   -> compare_nexps n1 n2
  | N2n _    , _        -> -1
  | _        , N2n _    ->  1
  | Nneg n1  , Nneg n2  -> compare_nexps n1 n2

let rec two_pow n =
  match n with 
  | 0 -> 1
  | n -> 2*(two_pow (n-1))

(* eval an nexp as much as possible *)
let rec eval_nexp n =
  (*let _ = Printf.printf "eval_nexp of %s\n" (n_to_string n) in*)
  match n.nexp with
    | Nconst i -> n
    | Nmult(n1,n2) ->
      let n1',n2' = (eval_nexp n1),(eval_nexp n2) in
      (match n1'.nexp,n2'.nexp with
	| Nconst i1, Nconst i2 -> {nexp=Nconst (i1*i2)}
        | Nconst 0,n | n,Nconst 0 -> {nexp = Nconst 0}
	| (Nconst _ as c),Nmult(nl,nr) | Nmult(nl,nr),(Nconst _ as c) -> 
	  {nexp = Nmult(eval_nexp {nexp = Nmult({nexp = c},nl)},eval_nexp {nexp = Nmult({nexp=c},nr)})}
	| (Nconst _ as c),Nadd(nl,nr) | Nadd(nl,nr),(Nconst _ as c) ->
	  {nexp = Nadd(eval_nexp {nexp =Nmult({nexp=c},nl)},eval_nexp {nexp = Nmult({nexp=c},nr)})}
	| N2n n1, N2n n2 -> {nexp = N2n( eval_nexp {nexp = Nadd(n1,n2)} ) }
	| _,_ -> {nexp = Nmult(n1',n2') })
    | Nadd(n1,n2) ->
      let n1',n2' = (eval_nexp n1),(eval_nexp n2) in      
      (match n1'.nexp,n2'.nexp with
	| Nconst i1, Nconst i2 -> {nexp=Nconst (i1+i2)}
	| (Nconst i as c),Nadd(nl,nr) | Nadd(nl,nr),(Nconst i as c) ->
          if i = 0 then {nexp = Nadd(nl,nr)}
	  else 
            {nexp = Nadd(eval_nexp {nexp =Nadd({nexp=c},nl)},nr)}
        | Nconst 0,n | n,Nconst 0 -> {nexp = n}
        | (Nconst _ as c),n | n,(Nconst _ as c) -> {nexp=Nadd({nexp=c},{nexp=n})} 
	| _,_ -> {nexp = Nadd(n1',n2') })
    | Nneg n1 ->
      let n1' = eval_nexp n1 in
      (match n1'.nexp with
	| Nconst i -> {nexp = Nconst(i * -1)}
	| _ -> {nexp = Nneg n1'})
    | N2n n1 ->
      let n1' = eval_nexp n1 in
      (match n1'.nexp with
	| Nconst i ->
	  {nexp = Nconst(two_pow i)}
	| _ -> {nexp = N2n n1'})
    | Nvar _ | Nuvar _ -> n

let rec get_var n =
  match n.nexp with
  | Nvar _ | Nuvar _ -> Some n
  | Nneg n -> get_var n
  | Nmult (_,n1) -> get_var n1
  | _ -> None

let get_factor n =
  match n.nexp with
  | Nvar _ | Nuvar _ -> {nexp = Nconst 1}
  | Nmult (n1,_) | Nneg n1 -> n1
  | _ -> assert false

let increment_factor n i =
  match n.nexp with
  | Nvar _ | Nuvar _ -> 
    (match i.nexp with
    | Nconst i -> {nexp = Nmult({nexp = Nconst (i + 1)},n)}
    | _ -> {nexp = Nmult({nexp = Nadd(i,{nexp = Nconst 1})},n)})
  | Nmult(n1,n2) ->
    (match n1.nexp,i.nexp with
    | Nconst i2,Nconst i -> { nexp = Nmult({nexp = Nconst (i + i2)},n2)}
    | _ -> { nexp = Nmult({ nexp = Nadd(n1,i)},n2)})
  | _ -> assert false

let negate n = {nexp = Nmult ({nexp = Nconst (-1)},n)}

let rec normalize_nexp n =
  match n.nexp with
  | Nconst _ | Nvar _ | Nuvar _ -> n
  | Nneg n -> 
    let n',to_recur,add_neg = (match n.nexp with
      | Nconst i -> {nexp = Nconst (i*(-1))},false,false
      | Nadd(n1,n2) -> {nexp = Nadd(negate n1,negate n2)},true,false
      | Nneg n -> normalize_nexp n,false,false
      | _ -> n,true,true) in
    if to_recur 
    then begin
      let n' = normalize_nexp n' in
        match n'.nexp,add_neg with
        | Nconst i,true -> {nexp = Nconst (i*(-1))}
        | _,false -> n'
        | _,true -> negate n'
    end
    else n'
  | N2n n -> 
    let n' = normalize_nexp n in
    (match n'.nexp with
    | Nconst i -> {nexp = Nconst (two_pow i)}
    | _ -> {nexp = N2n n'})
  | Nadd(n1,n2) ->
    let n1',n2' = normalize_nexp n1, normalize_nexp n2 in
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 -> {nexp = Nconst (i1+i2)}
    | Nconst _, Nvar _ | Nconst _, Nuvar _ | Nconst _, N2n _ | Nconst _, Nneg _ | Nconst _, Nmult _ -> {nexp = Nadd(n2',n1') }
    | Nvar _, Nconst _ | Nuvar _, Nconst _ | Nmult _, Nconst _ | N2n _, Nconst _ -> {nexp = Nadd(n1',n2')}
    | Nvar _, Nuvar _ | Nvar _, N2n _ -> {nexp = Nadd (n2',n1')}
    | Nadd(n11,n12), Nadd(n21,n22) ->
      (match compare_nexps n11 n21 with
      | -1 | 0 -> normalize_nexp {nexp = Nadd(n11, {nexp = Nadd(n12,n2')})}
      | _ -> normalize_nexp {nexp = Nadd(n21, { nexp = Nadd(n22,n1') })})      
    | Nadd(n11,n12), Nconst _ -> {nexp = Nadd(n11,{nexp = Nadd(n12,n2')}) }
    | Nconst _, Nadd(n21,n22) -> {nexp = Nadd(n21,{nexp = Nadd(n22,n1')})}
    | N2n n1, N2n n2 -> 
      (match compare_nexps n1 n2 with
      | -1 | 0 -> {nexp = Nadd (n2',n1')}
      | _ -> { nexp = Nadd (n1',n2')})
    | _ ->
      match get_var n1', get_var n2' with
      | Some(nv1),Some(nv2) ->
        (match compare_nexps nv1 nv2 with
        | -1 -> {nexp = Nadd (n2',n1')}
        | 0 -> increment_factor n1' (get_factor n2')
        |  _ -> {nexp = Nadd (n1',n2')})
      | _ -> assert false)
  | Nmult(n1,n2) ->
    let n1',n2' = normalize_nexp n1, normalize_nexp n2 in
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 -> {nexp = Nconst (i1*i2)}
    | Nconst 2, N2n n2 | N2n n2, Nconst 2 -> {nexp =N2n (normalize_nexp {nexp = Nadd(n2, {nexp = Nconst 1})})}
    | Nconst _, Nvar _ | Nconst _, Nuvar _ | Nconst _, N2n _ | Nvar _, N2n _ -> { nexp = Nmult(n1',n2') }
    | Nvar _, Nconst _ | Nuvar _, Nconst _ | N2n _, Nconst _ | Nvar _, Nmult _ | Nvar _, Nuvar _ -> { nexp = Nmult(n2',n1') }
    | N2n n1, N2n n2 -> {nexp = N2n (normalize_nexp {nexp = Nadd(n1,n2)})}
    | N2n _, Nvar _ | N2n _, Nuvar _ | N2n _, Nmult _ | Nuvar _, N2n _ | Nuvar _, Nmult _ -> {nexp =Nmult(n2',n1')}
    | Nuvar {nindex = i1}, Nuvar {nindex = i2} ->
      (match compare i1 i2 with
      | 0 | 1 -> {nexp = Nmult(n1',n2')}
      | _ -> {nexp = Nmult(n2',n1')})
    | Nvar i1, Nvar i2 ->
      (match compare i1 i2 with
      | 0 | 1 -> {nexp = Nmult(n1',n2')}
      | _ -> {nexp = Nmult(n2',n1')})
    | Nconst _, Nadd(n21,n22) | Nvar _,Nadd(n21,n22) | Nuvar _,Nadd(n21,n22) | N2n _, Nadd(n21,n22) | Nmult _, Nadd(n21,n22) ->
      normalize_nexp {nexp = Nadd( {nexp = Nmult(n1',n21)}, {nexp = Nmult(n1',n21)})}
    | Nadd(n11,n12),Nconst _ | Nadd(n11,n12),Nvar _ | Nadd(n11,n12), Nuvar _ | Nadd(n11,n12), N2n _ | Nadd(n11,n12), Nmult _->
      normalize_nexp {nexp = Nadd( {nexp = Nmult(n11,n2')}, {nexp = Nmult(n12,n2')})}
    | Nadd(n11,n12),Nadd(n21,n22) ->
      {nexp = Nadd( {nexp = Nmult(n11,n21)},
                    {nexp = Nadd ({nexp = Nmult(n11,n22)},
                                  {nexp = Nadd({nexp = Nmult(n12,n21)},
                                               {nexp = Nmult(n12,n22)})})})}
    | Nuvar _, Nvar _ | Nmult _, Nvar _| Nmult _, Nuvar _ | Nmult _, N2n _-> {nexp = Nmult (n1',n2')} 
    | Nmult(n11,n12), Nconst _ -> {nexp = Nmult({nexp = Nmult(n11,n2')},{nexp = Nmult(n12,n2')})}
    | Nmult _ ,Nmult(n21,n22) | Nconst _, Nmult(n21,n22) -> {nexp = Nmult({nexp = Nmult(n21,n1')},{nexp = Nmult(n22,n1')})}
    | Nneg _,_ | _,Nneg _ -> assert false (* If things are normal, neg should be gone. *)
    )
    
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
  { nexp = Nuvar { nindex = i; nsubst = None ; nin = false}}
let new_o _ = 
  let i = !o_count in
  o_count := i + 1;
  { order = Ouvar { oindex = i; osubst = None }}
let new_e _ =
  let i = !e_count in
  e_count := i + 1;
  { effect = Euvar { eindex = i; esubst = None }}

exception Occurs_exn of t_arg
let rec resolve_tsubst (t : t) : t = 
  (*let _ = Printf.printf "resolve_tsubst on %s\n" (t_to_string t) in*)
  match t.t with
  | Tuvar({ subst=Some(t') } as u) ->
    let t'' = resolve_tsubst t' in
    (match t''.t with
    | Tuvar(_) -> u.subst <- Some(t''); t''
    | x -> t.t <- x; t)
  | _ -> t
let rec resolve_nsubst (n : nexp) : nexp = match n.nexp with
  | Nuvar({ nsubst=Some(n') } as u) ->
    let n'' = resolve_nsubst n' in
    (match n''.nexp with
    | Nuvar(m) -> if u.nin then m.nin <- true else (); u.nsubst <- Some(n''); n''
    | x -> n.nexp <- x; n)
  | _ -> n
let rec resolve_osubst (o : order) : order = match o.order with
  | Ouvar({ osubst=Some(o') } as u) ->
    let o'' = resolve_osubst o' in
    (match o''.order with
    | Ouvar(_) -> u.osubst <- Some(o''); o''
    | x -> o.order <- x; o)
  | _ -> o
let rec resolve_esubst (e : effect) : effect = match e.effect with
  | Euvar({ esubst=Some(e') } as u) ->
    let e'' = resolve_esubst e' in
    (match e''.effect with
    | Euvar(_) -> u.esubst <- Some(e''); e''
    | x -> e.effect <- x; e)
  | _ -> e

let rec occurs_check_t (t_box : t) (t : t) : unit =
  let t = resolve_tsubst t in
  if t_box == t then
    raise (Occurs_exn (TA_typ t))
  else
    match t.t with
    | Tfn(t1,t2,_) ->
      occurs_check_t t_box t1;
      occurs_check_t t_box t2
    | Ttup(ts) ->
      List.iter (occurs_check_t t_box) ts
    | Tapp(_,targs) -> List.iter (occurs_check_ta (TA_typ t_box)) targs
    | Tabbrev(t,ta) -> occurs_check_t t_box t; occurs_check_t t_box ta
    | _ -> ()
and occurs_check_ta (ta_box : t_arg) (ta : t_arg) : unit =
  match ta_box,ta with
  | TA_typ tbox,TA_typ t -> occurs_check_t tbox t
  | TA_nexp nbox, TA_nexp n -> occurs_check_n nbox n
  | TA_ord obox, TA_ord o -> occurs_check_o obox o
  | TA_eft ebox, TA_eft e -> occurs_check_e ebox e
  | _,_ -> ()
and occurs_check_n (n_box : nexp) (n : nexp) : unit =
  let n = resolve_nsubst n in
  if n_box == n then
    raise (Occurs_exn (TA_nexp n))
  else
    match n.nexp with
    | Nadd(n1,n2) | Nmult(n1,n2) -> occurs_check_n n_box n1; occurs_check_n n_box n2
    | N2n n | Nneg n -> occurs_check_n n_box n
    | _ -> ()
and occurs_check_o (o_box : order) (o : order) : unit =
  let o = resolve_osubst o in
  if o_box == o then
    raise (Occurs_exn (TA_ord o))
  else ()
and occurs_check_e (e_box : effect) (e : effect) : unit =
  let e = resolve_esubst e in
  if e_box == e then
    raise (Occurs_exn (TA_eft e))
  else ()

 
let equate_t (t_box : t) (t : t) : unit =
  let t = resolve_tsubst t in
  if t_box == t then ()
  else
    (occurs_check_t t_box t;
     match t.t with
     | Tuvar(_) ->
       (match t_box.t with
       | Tuvar(u) ->
         u.subst <- Some(t)
       | _ -> assert false)
     | _ ->
       t_box.t <- t.t)
let equate_n (n_box : nexp) (n : nexp) : unit =
  let n = resolve_nsubst n in
  if n_box == n then ()
  else
    (occurs_check_n n_box n;
     match n.nexp with
     | Nuvar(_) ->
       (match n_box.nexp with
       | Nuvar(u) ->
         u.nsubst <- Some(n)
       | _ -> assert false)
     | _ ->
       n_box.nexp <- n.nexp)
let equate_o (o_box : order) (o : order) : unit =
  let o = resolve_osubst o in
  if o_box == o then ()
  else
    (occurs_check_o o_box o;
     match o.order with
     | Ouvar(_) ->
       (match o_box.order with
       | Ouvar(u) ->
         u.osubst <- Some(o)
       | _ -> assert false)
     | _ ->
       o_box.order <- o.order)
let equate_e (e_box : effect) (e : effect) : unit =
  let e = resolve_esubst e in
  if e_box == e then ()
  else
    (occurs_check_e e_box e;
     match e.effect with
     | Euvar(_) ->
       (match e_box.effect with
       | Euvar(u) ->
         u.esubst <- Some(e)
       | _ -> assert false)
     | _ ->
       e_box.effect <- e.effect)

let rec fresh_var i mkr bindings =
  let v = "'v" ^ (string_of_int i) in
  match Envmap.apply bindings v with
  | Some _ -> fresh_var (i+1) mkr bindings
  | None -> mkr v

let rec fresh_tvar bindings t =
  match t.t with
  | Tuvar { index = i;subst = None } -> 
    fresh_var i (fun v -> equate_t t {t=Tvar v};Some (v,{k=K_Typ})) bindings
  | Tuvar { index = i; subst = Some ({t = Tuvar _} as t') } ->
    let kv = fresh_tvar bindings t' in
    equate_t t t';
    kv
  | Tuvar { index = i; subst = Some t' } ->
    t.t <- t'.t;
    None
  | _ -> None
let rec fresh_nvar bindings n =
  match n.nexp with
    | Nuvar { nindex = i;nsubst = None } -> 
      fresh_var i (fun v -> equate_n n {nexp = (Nvar v)}; Some(v,{k=K_Nat})) bindings
    | Nuvar { nindex = i; nsubst = Some({nexp=Nuvar _} as n')} ->
      let kv = fresh_nvar bindings n' in
      equate_n n n';
      kv
    | Nuvar { nindex = i; nsubst = Some n' } ->
      n.nexp <- n'.nexp;
      None
    | _ -> None
let rec fresh_ovar bindings o =
  match o.order with
    | Ouvar { oindex = i;osubst = None } -> 
      fresh_var i (fun v -> equate_o o {order = (Ovar v)}; Some(v,{k=K_Nat})) bindings
    | Ouvar { oindex = i; osubst = Some({order=Ouvar _} as o')} ->
      let kv = fresh_ovar bindings o' in
      equate_o o o';
      kv
    | Ouvar { oindex = i; osubst = Some o' } ->
      o.order <- o'.order;
      None
    | _ -> None
let rec fresh_evar bindings e =
  match e.effect with
    | Euvar { eindex = i;esubst = None } -> 
      fresh_var i (fun v -> equate_e e {effect = (Evar v)}; Some(v,{k=K_Nat})) bindings
    | Euvar { eindex = i; esubst = Some({effect=Euvar _} as e')} ->
      let kv = fresh_evar bindings e' in
      equate_e e e';
      kv
    | Euvar { eindex = i; esubst = Some e' } ->
      e.effect <- e'.effect;
      None
    | _ -> None

let nat_t = {t = Tapp("range",[TA_nexp{nexp= Nconst 0};TA_nexp{nexp = Nconst max_int};])}
let unit_t = { t = Tid "unit" }
let bit_t = {t = Tid "bit" }
let bool_t = {t = Tid "bool" }
let nat_typ = {t=Tid "nat"}
let pure_e = {effect=Eset []}

let is_nat_typ t =
  if t == nat_typ || t == nat_t then true
  else match t.t with
    | Tid "nat" -> true
    | Tapp("range",[TA_nexp{nexp = Nconst 0};TA_nexp{nexp = Nconst i}]) -> i == max_int
    | _ -> false

let initial_kind_env = 
  Envmap.from_list [ 
    ("bool", {k = K_Typ});
    ("nat", {k = K_Typ});
    ("unit", {k = K_Typ});
    ("bit", {k = K_Typ});
    ("list", {k = K_Lam( [{k = K_Typ}], {k = K_Typ})});
    ("reg", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("register", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("range", {k = K_Lam( [ {k = K_Nat}; {k= K_Nat}], {k = K_Typ}) });
    ("vector", {k = K_Lam( [ {k = K_Nat}; {k = K_Nat}; {k= K_Ord} ; {k=K_Typ}], {k=K_Typ}) } )
  ]

let mk_nat_params l = List.map (fun i -> (i,{k=K_Nat})) l
let mk_typ_params l = List.map (fun i -> (i,{k=K_Typ})) l
let mk_ord_params l = List.map (fun i -> (i,{k=K_Ord})) l

let mk_tup ts = {t = Ttup ts }
let mk_pure_fun arg ret = {t = Tfn (arg,ret,pure_e)}

let mk_nv v = {nexp = Nvar v}
let mk_add n1 n2 = {nexp = Nadd (n1,n2) }
let mk_sub n1 n2 = {nexp = Nadd (n1, {nexp = Nneg n2})}

let mk_range n1 n2 = {t=Tapp("range",[TA_nexp n1;TA_nexp n2])}
let mk_vector typ order start size = {t=Tapp("vector",[TA_nexp {nexp=start}; TA_nexp {nexp=size}; TA_ord {order}; TA_typ typ])}
let mk_bitwise_op name symb arity =
  (* XXX should be Ovar "o" but will not work currently *)
  let ovar = (*Oinc*) Ovar "o"  in
  let vec_typ = mk_vector bit_t ovar (Nconst 0) (Nvar "n") in
  let args = Array.to_list (Array.make arity vec_typ) in
  let arg = if ((List.length args) = 1) then List.hd args else mk_tup args in
  (symb,Base((["n",{k=K_Nat}; "o",{k=K_Ord}], mk_pure_fun arg vec_typ),External (Some name),[],pure_e))

let initial_typ_env =
  Envmap.from_list [
    ("ignore",Base(([("a",{k=K_Typ});("b",{k=K_Efct})],mk_pure_fun {t=Tvar "a"} unit_t),External None,[],pure_e));
    ("+",Overload(Base(((mk_typ_params ["a";"b";"c"]),
                        (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})),External (Some "add"),[],pure_e),
                  [Base(((mk_nat_params ["n";"m";"o";"p"]),
                         (mk_pure_fun (mk_tup [mk_range (mk_nv "n") (mk_nv "m"); mk_range (mk_nv "o") (mk_nv "p")])
		                      (mk_range (mk_add (mk_nv "n") (mk_nv "o")) (mk_add (mk_nv "m") (mk_nv "p"))))),
		        External (Some "add"),[],pure_e);
                   Base(((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                         (mk_pure_fun (mk_tup [mk_vector bit_t (Ovar "ord") (Nvar "o") (Nvar "n");
                                               mk_vector bit_t (Ovar "ord") (Nvar "p") (Nvar "n")])
                                      (mk_vector bit_t (Ovar "ord") (Nvar "o") (Nvar "n")))), External (Some "add_vec"),[],pure_e);
                   Base(((mk_nat_params ["n";"m";"o";"p"])@(mk_ord_params ["ord"]),
                        (mk_pure_fun (mk_tup [mk_vector bit_t (Ovar "ord") (Nvar "n") (Nvar "m");
                                              mk_range (mk_nv "o") (mk_nv "p")])
                                     (mk_range (mk_nv "o") (mk_add (mk_nv "p") {nexp = N2n (mk_nv "m")})))),
                        External (Some "add_vec_range"),
                        [LtEq(Specc(Parse_ast.Int("+",None)),mk_add (mk_nv "o") (mk_nv "p"),{nexp=N2n (mk_nv "m")})],pure_e);
                   Base(((mk_nat_params ["n";"m";"o";"p"])@(mk_ord_params ["ord"]),
                         (mk_pure_fun (mk_tup [mk_range (mk_nv "o") (mk_nv "p");
                                               mk_vector bit_t (Ovar "ord") (Nvar "n") (Nvar "m");])
                                      (mk_range (mk_nv "o") {nexp = N2n (mk_nv "m")}))),
                        External (Some "add_range_vec"),
                       [],pure_e); ]));
    ("*",Base(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "multiply"),[],pure_e));
    ("-",Base(([("n",{k=K_Nat});("m",{k=K_Nat});("o",{k=K_Nat});("p",{k=K_Nat})],
               {t= Tfn({t=Ttup([mk_range (mk_nv "n") (mk_nv "m");
                                mk_range (mk_nv "o") (mk_nv "p")])},
		       (mk_range (mk_sub (mk_nv "n") (mk_nv "o")) (mk_sub (mk_nv "m") (mk_nv "p"))),
		       pure_e)}),External (Some "minus"),
              [GtEq(Specc(Parse_ast.Int("-",None)),{nexp=Nvar "n"},{nexp=Nvar "o"});
               GtEq(Specc(Parse_ast.Int("-",None)),{nexp=Nadd({nexp=Nvar "n"},{nexp=Nvar "m"})},{nexp=Nvar "o"})],pure_e));
    ("mod",Base(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "mod"),[],pure_e));
    ("quot",Base(([],{t= Tfn ({t=Ttup([nat_typ;nat_typ])},nat_typ,pure_e)}),External (Some "quot"),[],pure_e));
    (*Type incomplete*)
    (":",Base(([("a",{k=K_Typ});("b",{k=K_Typ});("c",{k=K_Typ})],
	       {t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "b"}])},{t=Tvar "c"},pure_e)}),External (Some "vec_concat"),[],pure_e));
    ("to_num_inc",Base(([("a",{k=K_Typ})],{t= Tfn ({t=Tvar "a"},nat_typ,pure_e)}),External None,[],pure_e));
    ("to_num_dec",Base(([("a",{k=K_Typ})],{t= Tfn ({t=Tvar "a"},nat_typ,pure_e)}),External None,[],pure_e));
    ("to_vec_inc",Base(([("a",{k=K_Typ})],{t= Tfn (nat_typ,{t=Tvar "a"},pure_e)}),External None,[],pure_e));
    ("to_vec_dec",Base(([("a",{k=K_Typ})],{t= Tfn (nat_typ,{t=Tvar "a"},pure_e)}),External None,[],pure_e));
    ("==",
     Overload( Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "eq"),[],pure_e),
     [Base(([("n",{k=K_Nat});("m",{k=K_Nat});("o",{k=K_Nat});("p",{k=K_Nat})],
	    {t = Tfn({t=Ttup([mk_range (mk_nv "n") (mk_nv "m");mk_range (mk_nv "o") (mk_nv "p")])},bit_t,pure_e)}), External (Some "eq"),
	   [Eq(Specc(Parse_ast.Int("==",None)),
	       {nexp=Nadd({nexp=Nvar "n"},{nexp=Nvar "m"})},
	       {nexp=Nadd({nexp=Nvar "o"},{nexp=Nvar "p"})})],pure_e);
      Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "eq"),[],pure_e)]));
    ("!=",Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "neq"),[],pure_e));
    ("<",
     Overload(Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "lt"),[],pure_e),
     [Base(([("n",{k=K_Nat});("m",{k=K_Nat});("o",{k=K_Nat});("p",{k=K_Nat})],
	    {t = Tfn({t=Ttup([mk_range (mk_nv "n") (mk_nv "m");mk_range (mk_nv "o") (mk_nv "p")])},bit_t,pure_e)}), External (Some "lt_vec"),
	   [LtEq(Specc(Parse_ast.Int("<",None)),
	       {nexp=Nadd({nexp=Nadd({nexp=Nvar "n"},{nexp=Nvar "m"})},{nexp=Nconst 1})},
	       {nexp=Nadd({nexp=Nvar "o"},{nexp=Nvar "p"})})],pure_e);
      Base(([("n",{k=K_Nat});("o",{k=K_Nat});("p",{k=K_Nat});("ord",{k=K_Ord})],
            {t = Tfn({t=Ttup([mk_vector bit_t (Ovar "ord") (Nvar "o") (Nvar "n");
                              mk_vector bit_t (Ovar "ord") (Nvar "p") (Nvar "n")])},bit_t,pure_e)}), External (Some "lt"),[],pure_e);]));
    (">",
     Overload(Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "gt"),[],pure_e),
     [Base(([("n",{k=K_Nat});("m",{k=K_Nat});("o",{k=K_Nat});("p",{k=K_Nat})],
	    {t = Tfn({t=Ttup([mk_range (mk_nv "n") (mk_nv "m");mk_range (mk_nv "o") (mk_nv "p")])},bit_t,pure_e)}), External (Some "gt_vec"),
	   [GtEq(Specc(Parse_ast.Int(">",None)),
		 {nexp=Nadd({nexp=Nvar "n"},{nexp=Nvar "m"})},
		 {nexp=Nadd({nexp=Nadd({nexp=Nvar "o"},{nexp=Nvar "p"})},{nexp=Nconst 1})})],pure_e);
      Base(([("n",{k=K_Nat});("o",{k=K_Nat});("p",{k=K_Nat});("ord",{k=K_Ord})],
            {t = Tfn({t=Ttup([mk_vector bit_t (Ovar "ord") (Nvar "o") (Nvar "n");
                              mk_vector bit_t (Ovar "ord") (Nvar "p") (Nvar "n")])},bit_t,pure_e)}), External (Some "lt"),[],pure_e);]));
    ("<_u",Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "ltu"),[],pure_e));
    (">_u",Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};{t=Tvar "a"}])},bit_t,pure_e)}),External (Some "gtu"),[],pure_e));
    ("is_one",Base(([],{t= Tfn (bit_t,bool_t,pure_e)}),External (Some "is_one"),[],pure_e));
    mk_bitwise_op "bitwise_not" "~" 1;
    mk_bitwise_op  "bitwise_or" "|" 2;
    mk_bitwise_op  "bitwise_xor" "^" 2;
    mk_bitwise_op  "bitwise_and" "&" 2;
    ("^^",Base(([("n",{k=K_Nat});("m",{k=K_Nat})],
                {t= Tfn ({t=Ttup([bit_t;mk_range (mk_nv "n") (mk_nv "m")])},
                mk_vector bit_t Oinc (Nconst 0) (Nadd({nexp=Nvar "n"},{nexp=Nvar "m"})),
                pure_e)}),External (Some "duplicate"),[],pure_e));
    ("<<<",Base((["a",{k=K_Typ}],{t= Tfn ({t=Ttup([{t=Tvar "a"};nat_typ])},{t=Tvar "a"},pure_e)}),External (Some "bitwise_leftshift"),[],pure_e));
  ]

let initial_abbrev_env =
  Envmap.from_list [
    ("nat",Base(([],nat_t),Emp_global,[],pure_e));
  ]

let rec t_subst s_env t =
  match t.t with
  | Tvar i -> (match Envmap.apply s_env i with
               | Some(TA_typ t1) -> t1
               | _ -> t)
  | Tuvar _  -> new_t()
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
  | Nuvar _ -> new_n()
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
    | In(l,s,ns)::cs -> 
      let nexp = n_subst t_env {nexp=Nvar s} in
      (match nexp.nexp with
      | Nuvar urec -> urec.nin <- true
      | _ -> ()); 
      InS(l,nexp,ns)::(cs_subst t_env cs)
    | InS(l,n,ns)::cs -> InS(l,n_subst t_env n,ns)::(cs_subst t_env cs)
    | CondCons(l,cs_p,cs_e)::cs -> CondCons(l,cs_subst t_env cs_p,cs_subst t_env cs_e)::(cs_subst t_env cs)
    | BranchCons(l,bs)::cs -> BranchCons(l,cs_subst t_env bs)::(cs_subst t_env cs)

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
  | Tuvar _ -> (match fresh_tvar s_env t with
      | Some ks -> Envmap.insert s_env ks
      | None -> s_env)
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
  | Nuvar _ -> (match fresh_nvar s_env n with
      | Some ks -> Envmap.insert s_env ks
      | None -> s_env)
  | N2n n1 | Nneg n1 -> (n_remove_unifications s_env n1)
  | Nadd(n1,n2) | Nmult(n1,n2) -> (n_remove_unifications (n_remove_unifications s_env n1) n2)
and o_remove_unifications s_env o =
  match o.order with
  | Ouvar _ -> (match fresh_ovar s_env o with
      | Some ks -> Envmap.insert s_env ks
      | None -> s_env)
  | _ -> s_env
and e_remove_unifications s_env e =
  match e.effect with
  | Euvar _ -> (match fresh_evar s_env e with
      | Some ks -> Envmap.insert s_env ks
      | None -> s_env)
  | _ -> s_env

      
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


let rec t_to_typ t =
  match t.t with
    | Tid i -> Typ_aux(Typ_id (Id_aux((Id i), Parse_ast.Unknown)),Parse_ast.Unknown)
    | Tvar i -> Typ_aux(Typ_var (Kid_aux((Var i),Parse_ast.Unknown)),Parse_ast.Unknown) 
    | Tfn(t1,t2,e) -> Typ_aux(Typ_fn (t_to_typ t1, t_to_typ t2, e_to_ef e),Parse_ast.Unknown)
    | Ttup ts -> Typ_aux(Typ_tup(List.map t_to_typ ts),Parse_ast.Unknown)
    | Tapp(i,args) -> Typ_aux(Typ_app(Id_aux((Id i), Parse_ast.Unknown),List.map targ_to_typ_arg args),Parse_ast.Unknown)
    | Tabbrev(t,_) -> t_to_typ t
    | Tuvar _ -> Typ_aux(Typ_var (Kid_aux((Var "fresh"),Parse_ast.Unknown)),Parse_ast.Unknown)
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
    | Nneg n -> Nexp_neg (n_to_nexp n)
    | Nuvar _ -> Nexp_var (Kid_aux((Var "fresh"),Parse_ast.Unknown))), Parse_ast.Unknown)
and e_to_ef ef =
 Effect_aux( 
  (match ef.effect with
    | Evar i -> Effect_var (Kid_aux((Var i),Parse_ast.Unknown)) 
    | Eset effects -> Effect_set effects
    | Euvar _ -> assert false), Parse_ast.Unknown)
and o_to_order o =
 Ord_aux( 
  (match o.order with
    | Ovar i -> Ord_var (Kid_aux((Var i),Parse_ast.Unknown)) 
    | Oinc -> Ord_inc 
    | Odec -> Ord_dec
    | Ouvar _ -> Ord_var (Kid_aux((Var "fresh"),Parse_ast.Unknown))), Parse_ast.Unknown)


let rec get_abbrev d_env t =
  match t.t with
    | Tid i ->
      (match Envmap.apply d_env.abbrevs i with
	| Some(Base((params,ta),tag,cs,efct)) ->
          let ta,cs,_ = subst params ta cs efct in
          let ta,cs' = get_abbrev d_env ta in
          (match ta.t with
          | Tabbrev(t',ta) -> ({t=Tabbrev({t=Tabbrev(t,t')},ta)},cs@cs')
          | _ -> ({t = Tabbrev(t,ta)},cs))
	| _ -> t,[])
    | Tapp(i,args) ->
      (match Envmap.apply d_env.abbrevs i with
	| Some(Base((params,ta),tag,cs,efct)) ->
	  let env = Envmap.from_list2 (List.map fst params) args in
          let ta,cs' = get_abbrev d_env (t_subst env ta) in
          (match ta.t with
          | Tabbrev(t',ta) -> ({t=Tabbrev({t=Tabbrev(t,t')},ta)},cs_subst env (cs@cs'))
          | _ -> ({t = Tabbrev(t,ta)},cs_subst env cs))
	| _ -> t,[])
    | _ -> t,[]

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
let order_eq co o1 o2 = 
  let l = get_c_loc co in
  match (o1.order,o2.order) with 
  | (Oinc,Oinc) | (Odec,Odec) | (Oinc,Ovar _) | (Odec,Ovar _) -> o2
  | (Ouvar i,_) -> equate_o o1 o2; o2
  | (_,Ouvar i) -> equate_o o2 o1; o2
  | (Ovar v1,Ovar v2) -> if v1=v2 then o2 else eq_error l ("Order variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | (Oinc,Odec) | (Odec,Oinc) -> eq_error l "Order mismatch of inc and dec"
  | (Ovar v1,Oinc) -> eq_error l ("Polymorphic order " ^ v1 ^ " cannot be used where inc is expected")
  | (Ovar v1,Odec) -> eq_error l ("Polymorhpic order " ^ v1 ^ " cannot be used where dec is expected")

(*Similarly to above.*)
let effects_eq co e1 e2 =
  let l = get_c_loc co in
  match e1.effect,e2.effect with
  | Eset _ , Evar _ -> e2
  | Euvar i,_ -> equate_e e1 e2; e2
  | _,Euvar i -> equate_e e2 e1; e2
  | Eset es1,Eset es2 -> if ( effect_sort es1 = effect_sort es2 ) then e2 else eq_error l ("Effects must be the same") (*Print out both effect lists?*)
  | Evar v1, Evar v2 -> if v1 = v2 then e2 else eq_error l ("Effect variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Evar v1, Eset _ -> eq_error l ("Effect variable " ^ v1 ^ " cannot be used where a concrete set of effects is specified")

(* Is checking for structural equality only, other forms of equality will be handeled by constraints *)
let rec nexp_eq_check n1 n2 =
  match n1.nexp,n2.nexp with
  | Nvar v1,Nvar v2 -> v1=v2
  | Nconst n1,Nconst n2 -> n1=n2
  | Nadd(nl1,nl2), Nadd(nr1,nr2) | Nmult(nl1,nl2), Nmult(nr1,nr2) -> nexp_eq_check nl1 nr1 && nexp_eq_check nl2 nr2
  | N2n n,N2n n2 -> nexp_eq_check n n2
  | Nneg n,Nneg n2 -> nexp_eq_check n n2
  | Nuvar {nindex =i1},Nuvar {nindex = i2} -> i1 = i2
  | _,_ -> false

let nexp_eq n1 n2 =
  nexp_eq_check (eval_nexp n1) (eval_nexp n2)

(*Is checking for structural equality amongst the types, building constraints for kind Nat. 
  When considering two range type applications, will check for consistency instead of equality*)
let rec type_consistent_internal co d_env t1 cs1 t2 cs2 = 
  (*let _ = Printf.printf "type_consistent_internal called with %s and %s\n" (t_to_string t1) (t_to_string t2) in*)
  let l = get_c_loc co in
  let t1,cs1' = get_abbrev d_env t1 in
  let t2,cs2' = get_abbrev d_env t2 in
  let cs1,cs2 = cs1@cs1',cs2@cs2' in
  let csp = cs1@cs2 in
  match t1.t,t2.t with
  | Tabbrev(_,t1),Tabbrev(_,t2) -> type_consistent_internal co d_env t1 cs1 t2 cs2
  | Tabbrev(_,t1),_ -> type_consistent_internal co d_env t1 cs1 t2 cs2
  | _,Tabbrev(_,t2) -> type_consistent_internal co d_env t1 cs1 t2 cs2
  | Tvar v1,Tvar v2 -> 
    if v1 = v2 then (t2,csp) 
    else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Tid v1,Tid v2 -> 
    if v1 = v2 then (t2,csp) 
    else eq_error l ("Types " ^ v1 ^ " and " ^ v2 ^ " do not match")
  | Tapp("range",[TA_nexp b1;TA_nexp r1;]),Tapp("range",[TA_nexp b2;TA_nexp r2;]) -> 
    if (nexp_eq b1 b2)&&(nexp_eq r1 r2) 
    then (t2,csp)
    else (t2, csp@[GtEq(co,b1,b2);LtEq(co,r1,r2)])
  | Tapp(id1,args1), Tapp(id2,args2) ->
    let la1,la2 = List.length args1, List.length args2 in
    if id1=id2 && la1 = la2 
    then (t2,csp@(List.flatten (List.map2 (type_arg_eq co d_env) args1 args2)))
    else eq_error l ("Type application of " ^ (t_to_string t1) ^ " and " ^ (t_to_string t2) ^ " must match")
  | Tfn(tin1,tout1,effect1),Tfn(tin2,tout2,effect2) -> 
    let (tin,cin) = type_consistent co d_env tin1 tin2 in
    let (tout,cout) = type_consistent co d_env tout1 tout2 in
    let effect = effects_eq co effect1 effect2 in
    (t2,csp@cin@cout)
  | Ttup t1s, Ttup t2s ->
    (t2,csp@(List.flatten (List.map snd (List.map2 (type_consistent co d_env) t1s t2s))))
  | Tuvar _, t -> equate_t t1 t2; (t1,csp)
  | Tapp("range",[TA_nexp b;TA_nexp r]),Tuvar _ ->
    if is_nat_typ t1 then
      begin equate_t t2 t1; (t2,csp) end
    else 
      let b2,r2 = new_n (), new_n () in
      let t2' = {t=Tapp("range",[TA_nexp b2;TA_nexp r2])} in
      equate_t t2 t2';
      (t2,csp@[GtEq(co,b,b2);LtEq(co,r,r2)]) (*This and above should maybe be In constraints when co is patt and tuvar is an in*)
  | t,Tuvar _ -> equate_t t2 t1; (t1,csp)
  | _,_ -> eq_error l ("Type mismatch found " ^ (t_to_string t1) ^ " but expected a " ^ (t_to_string t2))

and type_arg_eq co d_env ta1 ta2 = 
  match ta1,ta2 with
  | TA_typ t1,TA_typ t2 -> snd (type_consistent co d_env t1 t2)
  | TA_nexp n1,TA_nexp n2 -> if nexp_eq n1 n2 then [] else [Eq(co,n1,n2)]
  | TA_eft e1,TA_eft e2 -> (ignore(effects_eq co e1 e2);[])
  | TA_ord o1,TA_ord o2 -> (ignore(order_eq co o1 o2);[])
  | _,_ -> eq_error (get_c_loc co) "Type arguments must be of the same kind" 

and type_consistent co d_env t1 t2 =
  type_consistent_internal co d_env t1 [] t2 []

let rec type_coerce_internal co d_env t1 cs1 e t2 cs2 = 
  let l = get_c_loc co in
  let t1,cs1' = get_abbrev d_env t1 in
  let t2,cs2' = get_abbrev d_env t2 in
  let cs1,cs2 = cs1@cs1',cs2@cs2' in
  let csp = cs1@cs2 in
  match t1.t,t2.t with
  | Tabbrev(_,t1),Tabbrev(_,t2) -> type_coerce_internal co d_env t1 cs1 e t2 cs2
  | Tabbrev(_,t1),_ -> type_coerce_internal co d_env t1 cs1 e t2 cs2
  | _,Tabbrev(_,t2) -> type_coerce_internal co d_env t1 cs1 e t2 cs2
  | Ttup t1s, Ttup t2s ->
    let tl1,tl2 = List.length t1s,List.length t2s in
    if tl1=tl2 then 
      let ids = List.map (fun _ -> Id_aux(Id (new_id ()),l)) t1s in
      let vars = List.map2 (fun i t -> E_aux(E_id(i),(l,Base(([],t),Emp_local,[],pure_e)))) ids t1s in
      let (coerced_ts,cs,coerced_vars) = 
        List.fold_right2 (fun v (t1,t2) (ts,cs,es) -> let (t',c',e') = type_coerce co d_env t1 v t2 in
                                                      ((t'::ts),c'@cs,(e'::es)))
          vars (List.combine t1s t2s) ([],[],[]) in
      if vars = coerced_vars then (t2,cs,e)
      else let e' = E_aux(E_case(e,[(Pat_aux(Pat_exp(P_aux(P_tup (List.map2 
								    (fun i t -> P_aux(P_id i,(l,(Base(([],t),Emp_local,[],pure_e)))))
								    ids t1s),(l,Base(([],t1),Emp_local,[],pure_e))),
						     E_aux(E_tuple coerced_vars,(l,Base(([],t2),Emp_local,cs,pure_e)))),
                                             (l,Base(([],t2),Emp_local,[],pure_e))))]),
                          (l,(Base(([],t2),Emp_local,[],pure_e)))) in
           (t2,csp@cs,e')
    else eq_error l ("Found a tuple of length " ^ (string_of_int tl1) ^ " but expected a tuple of length " ^ (string_of_int tl2))
  | Tapp(id1,args1),Tapp(id2,args2) ->
    if id1=id2 && (id1 <> "vector")
    then let t',cs' = type_consistent co d_env t1 t2 in (t',cs',e)
    else (match id1,id2 with
    | "vector","vector" ->
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord o1;TA_typ t1i],
        [TA_nexp b2;TA_nexp r2;TA_ord o2;TA_typ t2i] ->
        (match o1.order,o2.order with
        | Oinc,Oinc | Odec,Odec -> ()
        | Oinc,Ouvar _ | Odec,Ouvar _ -> equate_o o2 o1;
        | Ouvar _,Oinc | Ouvar _, Odec -> equate_o o1 o2;
        | _,_ -> equate_o o1 o2); 
        let cs = csp@[Eq(co,r1,r2)] in
        let t',cs' = type_consistent co d_env t1i t2i in
        let tannot = Base(([],t2),Emp_local,cs@cs',pure_e) in
        let e' = E_aux(E_internal_cast ((l,(Base(([],t2),Emp_local,[],pure_e))),e),(l,tannot)) in
        (t2,cs@cs',e'))
    | "vector","range" -> 
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(co,b2,{nexp=Nconst 0});GtEq(co,{nexp=Nadd(b2,r2)},{nexp=N2n r1})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_num_inc",l)),[e]),(l,Base(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [Eq(co,b2,{nexp=Nconst 0});GtEq(co,{nexp=Nadd(b2,r2)},{nexp=N2n r1})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_num_dec",l)),[e]),(l,Base(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
	eq_error l "Cannot convert a vector to an range without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert non-bit vector into an range"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or range is not properly kinded"))
    | "range","vector" -> 
      (match args2,args1 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [LtEq(co,{nexp=Nadd(b2,r2)},{nexp=N2n r1})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_vec_inc",l)),[e]),(l,Base(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
	let cs = [LtEq(co,{nexp=Nadd(b2,r2)},{nexp=N2n r1})] in
	(t2,cs,E_aux(E_app((Id_aux(Id "to_vec_dec",l)),[e]),(l,Base(([],t2),External None,cs,pure_e))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
	eq_error l "Cannot convert an range to a vector without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert an range into a non-bit vector"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or range is not properly kinded"))
    | "register",_ ->
      (match args1 with
	| [TA_typ t] ->
          (*TODO Should this be an internal cast? Probably, make sure it doesn't interfere with the other internal cast and get removed *)
          (*let _ = Printf.printf "Adding cast to remove register read\n" in*)
          let new_e = E_aux(E_cast(t_to_typ unit_t,e),(l,Base(([],t),External None,[],(add_effect (BE_aux(BE_rreg, l)) pure_e)))) in
	  type_coerce co d_env t new_e t2
	| _ -> raise (Reporting_basic.err_unreachable l "register is not properly kinded"))
    | _,_ -> 
      let t',cs' = type_consistent co d_env t1 t2 in (t',cs',e))
  | Tid("bit"),Tapp("vector",[TA_nexp {nexp=Nconst i};TA_nexp r1;TA_ord o;TA_typ {t=Tid "bit"}]) ->
    let cs = [Eq(co,r1,{nexp = Nconst 1})] in
    let t2' = {t = Tapp("vector",[TA_nexp {nexp=Nconst i};TA_nexp {nexp=Nconst 1};TA_ord o;TA_typ {t=Tid "bit"}])} in
    (t2',cs,E_aux(E_vector_indexed([(i,e)],Def_val_aux(Def_val_empty,(l,NoTyp))) ,(l,Base(([],t2),Emp_local,cs,pure_e))))
  | Tapp("vector",[TA_nexp ({nexp=Nconst i} as b1);TA_nexp r1;TA_ord o;TA_typ {t=Tid "bit"}]),Tid("bit") ->
    let cs = [Eq(co,r1,{nexp = Nconst 1})] in
    (t2,cs,E_aux((E_vector_access (e,(E_aux(E_lit(L_aux(L_num i,l)),
					   (l,Base(([],{t=Tapp("range",[TA_nexp b1;TA_nexp {nexp=Nconst 0}])}),Emp_local,cs,pure_e)))))),
                 (l,Base(([],t2),Emp_local,cs,pure_e))))
  | Tid("bit"),Tapp("range",[TA_nexp b1;TA_nexp r1]) ->
    let t',cs'= type_consistent co d_env {t=Tapp("range",[TA_nexp{nexp=Nconst 0};TA_nexp{nexp=Nconst 1}])} t2 in
    (t2,cs',E_aux(E_case (e,[Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_zero,l)),(l,Base(([],t1),Emp_local,[],pure_e))),
					     E_aux(E_lit(L_aux(L_num 0,l)),(l,Base(([],t2),Emp_local,[],pure_e)))),
				     (l,Base(([],t2),Emp_local,[],pure_e)));
			     Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_one,l)),(l,Base(([],t1),Emp_local,[],pure_e))),
					     E_aux(E_lit(L_aux(L_num 1,l)),(l,Base(([],t2),Emp_local,[],pure_e)))),
				     (l,Base(([],t2),Emp_local,[],pure_e)));]),
		  (l,Base(([],t2),Emp_local,[],pure_e))))    
  | Tapp("range",[TA_nexp b1;TA_nexp r1;]),Tid("bit") ->
    let t',cs'= type_consistent co d_env t1 {t=Tapp("range",[TA_nexp{nexp=Nconst 0};TA_nexp{nexp=Nconst 1}])} 
    in (t2,cs',E_aux(E_if(E_aux(E_app(Id_aux(Id "is_one",l),[e]),(l,Base(([],bool_t),External None,[],pure_e))),
			  E_aux(E_lit(L_aux(L_one,l)),(l,Base(([],bit_t),Emp_local,[],pure_e))),
			  E_aux(E_lit(L_aux(L_zero,l)),(l,Base(([],bit_t),Emp_local,[],pure_e)))),
		     (l,Base(([],bit_t),Emp_local,cs',pure_e))))
  | Tapp("range",[TA_nexp b1;TA_nexp r1;]),Tid(i) -> 
    (match Envmap.apply d_env.enum_env i with
    | Some(enums) -> 
      (t2,[GtEq(co,b1,{nexp=Nconst 0});LtEq(co,r1,{nexp=Nconst (List.length enums)})],
       E_aux(E_case(e,
		    List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_lit(L_aux((L_num i),l)),
								(l,Base(([],t1),Emp_local,[],pure_e))),
							  E_aux(E_id(Id_aux(Id a,l)),
								(l,Base(([],t2),Emp_local,[],pure_e)))),
						  (l,Base(([],t2),Emp_local,[],pure_e)))) enums),
	     (l,Base(([],t2),Emp_local,[],pure_e))))
    | None -> eq_error l ("Type mismatch: found a " ^ (t_to_string t1) ^ " but expected " ^ (t_to_string t2)))
  | Tid("bit"),Tid("bool") ->
    let e' = E_aux(E_app((Id_aux(Id "is_one",l)),[e]),(l,Base(([],bool_t),External None,[],pure_e))) in
    (t2,[],e')
  | Tid(i),Tapp("range",[TA_nexp b1;TA_nexp r1;]) -> 
    (match Envmap.apply d_env.enum_env i with
    | Some(enums) -> 
      (t2,[Eq(co,b1,{nexp=Nconst 0});GtEq(co,r1,{nexp=Nconst (List.length enums)})],
       E_aux(E_case(e,
		    List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_id(Id_aux(Id a,l)),
								(l,Base(([],t1),Emp_local,[],pure_e))),
							  E_aux(E_lit(L_aux((L_num i),l)),
								(l,Base(([],t2),Emp_local,[],pure_e)))),
						  (l,Base(([],t2),Emp_local,[],pure_e)))) enums),
	     (l,Base(([],t2),Emp_local,[],pure_e))))
    | None -> eq_error l ("Type mismatch: " ^ (t_to_string t1) ^ " , " ^ (t_to_string t2)))
  | _,_ -> let t',cs = type_consistent co d_env t1 t2 in (t',cs,e)

and type_coerce co d_env t1 e t2 = type_coerce_internal co d_env t1 [] e t2 [];;

let rec conforms_to_t spec actual =
  (*let _ = Printf.printf "conforms_to_t called with %s, %s\n" (t_to_string spec) (t_to_string actual) in*)
  match spec.t,actual.t with
    | Tuvar _,_ -> true
    | Ttup ss, Ttup acs -> (List.length ss = List.length acs) && List.for_all2 conforms_to_t ss acs
    | Tid is, Tid ia -> is = ia
    | Tapp(is,tas), Tapp("register",[TA_typ t]) ->
      if is = "register"
      then List.for_all2 conforms_to_ta tas [TA_typ t]
      else conforms_to_t spec t
    | Tapp(is,tas), Tapp(ia, taa) -> 
      (*let _ = Printf.printf "conforms to given two apps: %b, %b\n" (is = ia) (List.length tas = List.length taa) in*)
      (is = ia) && (List.length tas = List.length taa) && (List.for_all2 conforms_to_ta tas taa)
    | Tabbrev(_,s),a -> conforms_to_t s actual
    | s,Tabbrev(_,a) -> conforms_to_t spec a
    | _,_ -> false
and conforms_to_ta spec actual =
  (*let _ = Printf.printf "conforms_to_ta called with %s, %s\n" (targ_to_string spec) (targ_to_string actual) in*)
  match spec,actual with
    | TA_typ  s, TA_typ  a -> conforms_to_t s a
    | TA_nexp s, TA_nexp a -> conforms_to_n s a
    | TA_ord  s, TA_ord  a -> conforms_to_o s a
    | TA_eft  s, TA_eft  a -> conforms_to_e s a
and conforms_to_n spec actual =
  (*let _ = Printf.printf "conforms_to_n called with %s, %s\n" (n_to_string spec) (n_to_string actual) in*)
  match spec.nexp,actual.nexp with
    | Nuvar _,_ -> true
    | Nconst si,Nconst ai -> si==ai
    | _,_ -> false
and conforms_to_o spec actual =
  match spec.order,actual.order with
    | Ouvar _,_ | Oinc,Oinc | Odec,Odec -> true
    | _,_ -> false
and conforms_to_e spec actual =
  match spec.effect,actual.effect with
    | Euvar _,_ -> true
    | _,Euvar _ -> false
    | _,_ -> false

let rec select_overload_variant d_env variants actual_type =
  match variants with
    | [] -> NoTyp
    | NoTyp::variants | Overload _::variants -> select_overload_variant d_env variants actual_type
    | Base((parms,t),tag,cs,ef)::variants ->
      let t,cs,ef = subst parms t cs ef in
      let t,cs' = get_abbrev d_env t in
      (match t.t with
	| Tfn(a,r,e) ->
	  if conforms_to_t a actual_type 
	  then Base(([],t),tag,cs@cs',ef)
	  else select_overload_variant d_env variants actual_type
	| _ -> assert false (*Turn into unreachable error*))      

let rec in_constraint_env = function
  | [] -> []
  | InS(co,nexp,vals)::cs ->
    (nexp,(List.map (fun c -> {nexp = Nconst c}) vals))::(in_constraint_env cs)
  | In(co,i,vals)::cs -> 
    ({nexp = Nvar i},(List.map (fun c -> {nexp = Nconst c}) vals))::(in_constraint_env cs)
  | _::cs -> in_constraint_env cs

let rec contains_var nu n =
  match n.nexp with
  | Nvar _ | Nuvar _ -> nexp_eq_check nu n
  | Nconst _ -> false
  | Nadd(n1,n2) | Nmult(n1,n2) -> contains_var nu n1 || contains_var nu n2
  | Nneg n | N2n n -> contains_var nu n

let rec contains_in_vars in_env n =
  match in_env with
  | [] -> None
  | (ne,vals)::in_env -> 
    (match contains_in_vars in_env n with
    | None -> if contains_var ne n then Some [ne,vals] else None
    | Some(e_env) -> if contains_var ne n then Some((ne,vals)::e_env) else Some(e_env))

let rec subst_nuvars nu nc n =
  match n.nexp with
  | Nconst _ | Nvar _ -> n
  | Nuvar _ -> if nexp_eq_check nu n then nc else n
  | Nmult(n1,n2) -> {nexp=Nmult(subst_nuvars nu nc n1,subst_nuvars nu nc n2)}
  | Nadd(n1,n2) -> {nexp=Nadd(subst_nuvars nu nc n1,subst_nuvars nu nc n2)}
  | Nneg n -> {nexp= Nneg (subst_nuvars nu nc n)}
  | N2n n -> {nexp = N2n (subst_nuvars nu nc n)}

let rec get_nuvars n =
  match n.nexp with
    | Nconst _ | Nvar _ -> []
    | Nuvar _ -> [n]
    | Nmult(n1,n2) | Nadd(n1,n2) -> (get_nuvars n1)@(get_nuvars n2)
    | Nneg n | N2n n -> get_nuvars n

let freshen n = 
  let nuvars = get_nuvars n in
  let env_map = List.map (fun nu -> (nu,new_n ())) nuvars in
  let n = List.fold_right (fun (nu_orig,nu_fresh) n' -> subst_nuvars nu_orig nu_fresh n') env_map n in
  (n,env_map)


let rec simple_constraint_check in_env cs = 
  let check = simple_constraint_check in_env in
(*  let _ = Printf.printf "simple_constraint_check\n" in *)
  match cs with 
  | [] -> []
  | Eq(co,n1,n2)::cs -> 
    let check_eq ok_to_set n1 n2 = 
      (*let _ = Printf.printf "eq check, about to eval_nexp of %s, %s\n" (n_to_string n1) (n_to_string n2) in *)
      let n1',n2' = eval_nexp n1,eval_nexp n2 in
      (*let _ = Printf.printf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
      (match n1'.nexp,n2'.nexp with
      | Nconst i1, Nconst i2 -> 
        if i1==i2 then None
        else eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires " 
			              ^ string_of_int i1 ^ " to equal " ^ string_of_int i2)
      | Nconst i, Nuvar u ->
        if not(u.nin) && ok_to_set 
        then begin equate_n n2' n1'; None end
        else Some (Eq(co,n1',n2')) 
      | Nuvar u, Nconst i ->
        if not(u.nin) && ok_to_set
        then begin equate_n n1' n2'; None end
        else Some (Eq(co,n1',n2'))
      | Nuvar u1, Nuvar u2 ->
        if ok_to_set
        then begin resolve_nsubst n1; resolve_nsubst n2; equate_n n1' n2'; None end
        else Some(Eq(co,n1',n2'))
      | _,_ -> Some(Eq(co,n1',n2'))) in
    (match contains_in_vars in_env n1, contains_in_vars in_env n2 with
      | None,None ->	
	(match check_eq true n1 n2 with
	  | None -> (check cs)
	  | Some(c) -> c::(check cs))
      | _ -> (Eq(co,n1,n2)::(check cs)))
  | GtEq(co,n1,n2)::cs -> 
(*    let _ = Printf.printf ">= check, about to eval_nexp of %s, %s\n" (n_to_string n1) (n_to_string n2) in *)
    let n1',n2' = eval_nexp n1,eval_nexp n2 in
(*    let _ = Printf.printf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 -> 
      if i1>=i2 
      then check cs
      else eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires " 
			            ^ string_of_int i1 ^ " to be greater than or equal to " ^ string_of_int i2)
    | _,_ -> GtEq(co,n1',n2')::(check cs))
  | LtEq(co,n1,n2)::cs -> 
(*    let _ = Printf.printf "<= check, about to eval_nexp of %s, %s\n" (n_to_string n1) (n_to_string n2) in *)
    let n1',n2' = eval_nexp n1,eval_nexp n2 in
(*    let _ = Printf.printf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 -> 
      if i1<=i2 
      then check cs
      else eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires " 
			            ^ string_of_int i1 ^ " to be less than or equal to " ^ string_of_int i2)
    | _,_ -> LtEq(co,n1',n2')::(check cs))
  | CondCons(co,pats,exps):: cs ->
    let pats' = check pats in
    let exps' = check exps in
    (match pats',exps' with
      | [],[] -> check cs
      |  _,[] -> check cs
      | _     -> CondCons(co,pats',exps')::(check cs))
  | BranchCons(co,branches)::cs ->
    let b' = check branches in
    if []==b' 
    then check cs
    else BranchCons(co,b')::(check cs)
  | x::cs -> x::(check cs)

let rec resolve_in_constraints cs = cs
    
let do_resolve_constraints = ref true

let resolve_constraints cs = 
  if not !do_resolve_constraints
  then cs
  else
    let rec fix len cs =
(*      let _ = Printf.printf "Calling simple constraint check, fix check point is %i\n" len in *)
      let cs' = simple_constraint_check (in_constraint_env cs) cs in
      if len > (List.length cs') then fix (List.length cs') cs'
      else cs' in
    let complex_constraints = fix (List.length cs) cs in
    complex_constraints


let check_tannot l annot constraints efs = 
  match annot with
    | Base((params,t),tag,cs,e) -> 
      ignore(effects_eq (Specc l) efs e);
      let params = Envmap.to_list (t_remove_unifications (Envmap.from_list params) t) in
    (*let _ = Printf.printf "Checked tannot, t after removing uvars is %s\n" (t_to_string t) in *)
      Base((params,t),tag,cs,e)
    | NoTyp -> raise (Reporting_basic.err_unreachable l "check_tannot given the place holder annotation")
      

let tannot_merge co denv t_older t_newer = 
  match t_older,t_newer with
    | NoTyp,NoTyp -> NoTyp
    | NoTyp,_ -> t_newer
    | _,NoTyp -> t_older
    | Base((ps_o,t_o),tag_o,cs_o,ef_o),Base((ps_n,t_n),tag_n,cs_n,ef_n) -> 
      (match tag_o,tag_n with
	| Default,tag -> 
	  (match t_n.t with
	    | Tuvar _ -> let t_o,cs_o,ef_o = subst ps_o t_o cs_o ef_o in
			 let t,_ = type_consistent co denv t_n t_o in
			 Base(([],t),tag_n,cs_o,ef_o)
	    | _ -> t_newer)
	| Emp_local, Emp_local -> 
	  let t,cs_b = type_consistent co denv t_n t_o in
	  Base(([],t),Emp_local,cs_o@cs_n@cs_b,union_effects ef_o ef_n)
	| _,_ -> t_newer)
    | Overload _, Overload _ -> t_newer
