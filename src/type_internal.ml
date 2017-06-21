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

open Ast
open Util
open Big_int
module Envmap = Finite_map.Fmap_map(String)
module Nameset' = Set.Make(String)
module Nameset = struct
  include Nameset'
  let pp ppf nameset =
    Format.fprintf ppf "{@[%a@]}"
      (Pp.lst ",@ " Pp.pp_str)
      (Nameset'.elements nameset)
end

let zero = big_int_of_int 0
let one  = big_int_of_int 1
let two  = big_int_of_int 2

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
  | Tfn of t * t * implicit_parm * effect
  | Ttup of t list
  | Tapp of string * t_arg list
  | Tabbrev of t * t
  | Toptions of t * t option
  | Tuvar of t_uvar
and t_uvar = { index : int; mutable subst : t option ; mutable torig_name : string option}
and implicit_parm =
  | IP_none  | IP_length of nexp | IP_start of nexp | IP_user of nexp 
and nexp = { mutable nexp : nexp_aux; mutable imp_param : bool}
and nexp_aux =
  | Nvar of string
  | Nid of string * nexp (*First term is the name of this nid, second is the constant it represents*)
  | Nconst of big_int
  | Npos_inf
  | Nneg_inf
  | Nadd of nexp * nexp
  | Nsub of nexp * nexp
  | Nmult of nexp * nexp
  | N2n of nexp * big_int option
  | Npow of nexp * int (* nexp raised to the int *)
  | Nneg of nexp (* Unary minus for representing new vector sizes after vector slicing *)
  | Ninexact (*Result of +inf + -inf which is neither less than nor greater than other numbers really *)
  | Nuvar of n_uvar
and n_uvar =
  (*nindex is a counter; insubst are substitions 'inward'; outsubst are substitions 'outward'. Inward can be non nu
    nin is in an in clause; leave_var flags if we should try to stay a variable; orig_var out inwardmost, name to use
  *)
  { nindex : int; mutable insubst : nexp option; mutable outsubst : nexp option;
    mutable nin : bool; mutable leave_var : bool; mutable orig_var : string option ; mutable been_collapsed : bool }
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

type alias_inf =
  | Alias_field of string * string
  | Alias_extract of string * int * int
  | Alias_pair of string * string

type tag =
  | Emp_local
  | Emp_global
  | Emp_intro
  | Emp_set
  | Tuple_assign of tag list
  | External of string option
  | Default
  | Constructor of int
  | Enum of int
  | Alias of alias_inf
  | Spec

let rec compare_nexps n1 n2 =
  match n1.nexp,n2.nexp with 
  | Nneg_inf , Nneg_inf -> 0
  | Nneg_inf , _        -> -1
  | _        , Nneg_inf ->  1
  | Nconst n1, Nconst n2 -> compare_big_int n1 n2
  | Nconst _ , _        -> -1
  | _        , Nconst _ ->  1
  | Nid(i1,n1), Nid(i2,n2) ->
    (match compare i1 i2 with
     | 0 -> 0
     | _ -> compare_nexps n1 n2)
  | Nid _    , _        -> -1
  | _        , Nid _    ->  1
  | Nvar i1  , Nvar i2  ->  compare i1 i2
  | Nvar _   , _        -> -1
  | _        , Nvar _   ->  1 
  | Nuvar {nindex = n1}, Nuvar {nindex = n2} -> compare n1 n2
  | Nuvar _  , _        -> -1
  | _        , Nuvar _  ->  1
  | Nmult(n0,n1),Nmult(n2,n3) -> 
    (match compare_nexps n0 n2 with
      | 0 -> compare_nexps n1 n3
      | a -> a)
  | Nmult _  , _        -> -1
  | _        , Nmult _  ->  1
  | Nadd(n1,n12),Nadd(n2,n22) -> 
    (match compare_nexps n1 n2 with
      | 0 -> compare_nexps n12 n22 
      | a -> a)
  | Nadd _   , _        -> -1
  | _        , Nadd _   ->  1
  | Nsub(n1,n12),Nsub(n2,n22) ->
    (match compare_nexps n1 n2 with
      | 0 -> compare_nexps n12 n22
      | a -> a)
  | Nsub _   , _         -> -1
  | _        , Nsub _    -> 1
  | Npow(n1,_),Npow(n2,_)-> compare_nexps n1 n2
  | Npow _   , _        -> -1
  | _        , Npow _   ->  1
  | N2n(_,Some i1), N2n(_,Some i2) -> compare_big_int i1 i2
  | N2n(n1,_), N2n(n2,_) -> compare_nexps n1 n2
  | N2n _    , _        -> -1
  | _        , N2n _    ->  1
  | Nneg n1  , Nneg n2  -> compare_nexps n1 n2
  | Nneg _   , _        -> -1
  | _        , Nneg _   -> 1
  | Npos_inf , Npos_inf -> 0
  | Npos_inf , _        -> -1
  | _        , Npos_inf -> 1
  | Ninexact , Ninexact -> 0

module NexpM = 
 struct
 type t = nexp
 let compare = compare_nexps
end
module Var_set = Set.Make(NexpM) 
module Nexpmap = Finite_map.Fmap_map(NexpM)

type nexp_map = nexp Nexpmap.t

type constraint_origin =
  | Patt of Parse_ast.l
  | Expr of Parse_ast.l
  | Fun of Parse_ast.l
  | Specc of Parse_ast.l

type range_enforcement = Require | Guarantee 
type cond_kind = Positive | Negative | Solo | Switch
type 'a many = One of 'a | Two of 'a * 'a | Many of 'a list

(* Constraints for nexps, plus the location which added the constraint *)
type nexp_range =
  | LtEq of constraint_origin * range_enforcement * nexp * nexp
  | Lt of constraint_origin * range_enforcement * nexp * nexp
  | Eq of constraint_origin * nexp * nexp
  | NtEq of constraint_origin * nexp * nexp
  | GtEq of constraint_origin * range_enforcement * nexp * nexp
  | Gt of constraint_origin * range_enforcement * nexp * nexp
  | In of constraint_origin * string * int list
  | InS of constraint_origin * nexp * int list      
  | Predicate of constraint_origin * nexp_range * nexp_range 
  | CondCons of constraint_origin * cond_kind * (nexp Nexpmap.t) option * nexp_range list * nexp_range list
  | BranchCons of constraint_origin * ((nexp many) Nexpmap.t) option * nexp_range list

type variable_range =
  | VR_eq of string * nexp
  | VR_range of string * nexp_range list
  | VR_vec_eq of string * nexp
  | VR_vec_r of string * nexp_range list
  | VR_recheck of string * t (*For cases where inference hasn't yet determined the type of v*)

type bounds_env = 
  | No_bounds
  | Bounds of variable_range list * nexp_map option

type t_params = (string * kind) list
type tannot = 
  | NoTyp
  (*See .mli for purpose of attributes *)
  | Base of (t_params * t) * tag * nexp_range list * effect * effect * bounds_env
  (* First tannot is the most polymorphic version; the list includes all variants. All included t are Tfn *)
  | Overload of tannot * bool * tannot list    (* these tannot's should all be Base *)

type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type rec_env = (string * rec_kind * tannot * ((string * t) list))
type alias_kind = OneReg of string * tannot | TwoReg of string * string * tannot | MultiReg of (string list) * tannot
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap;
  nabbrevs: nexp emap;
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : rec_env list;
  alias_env : alias_kind emap;
  default_o : order;
 }

type triple = Yes | No | Maybe
let triple_negate = function
  | Yes   -> No
  | No    -> Yes
  | Maybe -> Maybe

type exp = tannot Ast.exp

type minmax = (constraint_origin * nexp) option
type constraints = nexp_range list

(*Nexpression Makers (as built so often)*)

let mk_nv s = {nexp = Nvar s; imp_param = false}
let mk_nid s n = {nexp = Nid(s,n); imp_param = false}
let mk_add n1 n2 = {nexp = Nadd(n1,n2); imp_param = false}
let mk_sub n1 n2 = {nexp = Nsub(n1,n2); imp_param = false}
let mk_mult n1 n2 = {nexp = Nmult(n1,n2); imp_param = false}
let mk_c i = {nexp = Nconst i; imp_param = false}
let mk_c_int i = mk_c (big_int_of_int i)
let mk_neg n = {nexp = Nneg n; imp_param = false}
let mk_2n n = {nexp = N2n(n, None); imp_param = false}
let mk_2nc n i = {nexp = N2n(n, Some i); imp_param = false}
let mk_pow n i = {nexp = Npow(n, i); imp_param = false}
let mk_p_inf () = {nexp = Npos_inf; imp_param = false}
let mk_n_inf () = {nexp = Nneg_inf; imp_param = false}
let mk_inexact () = {nexp = Ninexact; imp_param = false}

let merge_option_maps m1 m2 =
  match m1,m2 with
  | None,None -> None
  | None,m | m, None -> m
  | Some m1, Some m2 -> Some (Nexpmap.union m1 m2)

(*Getters*)

let get_index n =
 match n.nexp with
   | Nuvar {nindex = i} -> i
   | _ -> assert false

let get_c_loc = function
  | Patt l | Expr l | Specc l | Fun l -> l

let rec get_outer_most n = match n.nexp with
  | Nuvar {outsubst= Some n} -> get_outer_most n
  | _ -> n

let rec get_inner_most n = match n.nexp with
  | Nuvar {insubst=Some n} -> get_inner_most n
  | _ -> n

(*To string functions *)
let debug_mode = ref true;;

let rec kind_to_string kind = match kind.k with
  | K_Nat -> "Nat"
  | K_Typ -> "Type"
  | K_Ord -> "Order"
  | K_Efct -> "Effect"
  | K_infer -> "Infer"
  | K_Val -> "Val"
  | K_Lam (kinds,kind) -> "Lam [" ^ string_of_list ", " kind_to_string kinds ^ "] -> " ^ (kind_to_string kind)

let co_to_string = function
  | Patt l -> "Pattern " (*^ Reporting_basic.loc_to_string l *)
  | Expr l -> "Expression " (*^ Reporting_basic.loc_to_string l *)
  | Fun l -> "Function def " (*^ Reporting_basic.loc_to_string l *)
  | Specc l -> "Specification " (*^ Reporting_basic.loc_to_string l *)

let rec t_to_string t = 
  match t.t with
    | Tid i -> i
    | Tvar i -> i
    | Tfn(t1,t2,imp,e) -> 
      let implicit = match imp with 
        | IP_none -> "" 
        | IP_length n | IP_start n | IP_user n -> " with implicit parameter " ^ n_to_string n ^ " " in 
      (t_to_string t1) ^ " -> " ^ (t_to_string t2) ^ " effect " ^ e_to_string e ^ implicit
    | Ttup(tups) -> "(" ^ string_of_list ", " t_to_string tups ^ ")"
    | Tapp(i,args) -> i ^ "<" ^  string_of_list ", " targ_to_string args ^ ">"
    | Tabbrev(ti,ta) -> (t_to_string ti) ^ " : " ^ (t_to_string ta)
    | Toptions(t1,None) -> if !debug_mode then ("optionally " ^ (t_to_string t1)) else (t_to_string t1)
    | Toptions(t1,Some t2) -> if !debug_mode then ("(either "^ (t_to_string t1) ^ " or " ^ (t_to_string t2) ^ ")") else "_"
    | Tuvar({index = i;subst = a}) -> 
      if !debug_mode then "Tu_" ^ string_of_int i ^ "("^ (match a with | None -> "None" | Some t -> t_to_string t) ^")" else "_"
and targ_to_string = function
  | TA_typ t -> t_to_string t
  | TA_nexp n -> n_to_string n
  | TA_eft e -> e_to_string e
  | TA_ord o -> o_to_string o
and n_to_string n =
  match n.nexp with
  | Nid(i,n) -> i ^ "(*" ^ (n_to_string n) ^ "*)"
  | Nvar i -> i
  | Nconst i -> string_of_big_int i
  | Npos_inf -> "infinity"
  | Nneg_inf -> "-infinity"
  | Ninexact -> "infinity - infinity"
  | Nadd(n1,n2) -> "("^ (n_to_string n1) ^ " + " ^ (n_to_string n2) ^")"
  | Nsub(n1,n2) -> "("^ (n_to_string n1) ^ " - " ^ (n_to_string n2) ^ ")"
  | Nmult(n1,n2) -> "(" ^ (n_to_string n1) ^ " * " ^ (n_to_string n2) ^ ")"
  | N2n(n,None) -> "2**" ^ (n_to_string n)
  | N2n(n,Some i) -> "2**" ^ (n_to_string n) ^ "(*" ^ (string_of_big_int i) ^ "*)"
  | Npow(n, i) -> "(" ^ (n_to_string n) ^ ")**" ^ (string_of_int i)
  | Nneg n -> "-" ^ (n_to_string n)
  | Nuvar _ ->
    if !debug_mode
    then
      let rec show_nuvar n = match n.nexp with
        | Nuvar{insubst=None; nindex = i; orig_var = Some s} -> s^ "()"
        | Nuvar{insubst=Some n; nindex = i; orig_var = Some s} -> s ^ "(" ^ show_nuvar n ^ ")"
        | Nuvar{insubst=None; nindex = i;} -> "Nu_" ^ string_of_int i ^ "()" 
        | Nuvar{insubst=Some n; nindex =i;} -> "Nu_" ^ string_of_int i ^ "(" ^ show_nuvar n ^ ")"
        | _ -> n_to_string n in
      show_nuvar (get_outer_most n)
    else "_"
and ef_to_string (Ast.BE_aux(b,l)) =
    match b with
      | Ast.BE_rreg  -> "rreg"
      | Ast.BE_wreg  -> "wreg"
      | Ast.BE_rmem  -> "rmem"
      | Ast.BE_rmemt -> "rmemt"
      | Ast.BE_wmem  -> "wmem"
      | Ast.BE_wmv   -> "wmv"
      | Ast.BE_wmvt  -> "wmvt"
      | Ast.BE_eamem -> "eamem"
      | Ast.BE_exmem -> "exmem"
      | Ast.BE_barr  -> "barr"
      | Ast.BE_undef -> "undef"
      | Ast.BE_depend -> "depend"
      | Ast.BE_unspec-> "unspec"
      | Ast.BE_nondet-> "nondet"
      | Ast.BE_lset  -> "lset"
      | Ast.BE_lret  -> "lret"
      | Ast.BE_escape -> "escape" 
and efs_to_string es = 
  match es with
    | [] -> ""
    | [ef] -> ef_to_string ef
    | ef::es -> ef_to_string ef ^ ", " ^ efs_to_string es
and e_to_string e = 
  match e.effect with
  | Evar i -> "'" ^ i
  | Eset es -> if []=es then "pure" else "{" ^ (efs_to_string es) ^"}"
  | Euvar({eindex=i;esubst=a}) -> if !debug_mode then string_of_int i ^ "()" else "_"
and o_to_string o = 
  match o.order with
  | Ovar i -> "'" ^ i
  | Oinc -> "inc"
  | Odec -> "dec"
  | Ouvar({oindex=i;osubst=a}) -> if !debug_mode then string_of_int i ^ "()" else "_"

let rec tag_to_string = function
  | Emp_local -> "Emp_local"
  | Emp_global -> "Emp_global"
  | Emp_intro -> "Emp_intro"
  | Emp_set -> "Emp_set"
  | Tuple_assign tags -> "Tuple_assign (" ^ string_of_list ", " tag_to_string tags ^ ")"
  | External None -> "External" 
  | External (Some s) -> "External " ^ s
  | Default -> "Default"
  | Constructor _ -> "Constructor"
  | Enum _ -> "Enum"
  | Alias _ -> "Alias"
  | Spec -> "Spec"
    
let enforce_to_string = function
  | Require -> "require"
  | Guarantee -> "guarantee"

let cond_kind_to_string = function
  | Positive -> "positive"
  | Negative -> "negative"
  | Solo -> "solo"
  | Switch -> "switch"

let rec constraint_to_string = function
  | LtEq (co,enforce,nexp1,nexp2) ->
    "LtEq(" ^ co_to_string co ^ ", " ^ enforce_to_string enforce ^ ", " ^ 
      n_to_string nexp1 ^ ", " ^ n_to_string nexp2 ^ ")"
  | Lt (co,enforce,nexp1, nexp2) ->
    "Lt(" ^ co_to_string co ^ ", " ^ enforce_to_string enforce ^ ", " ^ 
      n_to_string nexp1 ^ ", " ^ n_to_string nexp2 ^ ")"
  | Eq (co,nexp1,nexp2) ->
    "Eq(" ^ co_to_string co ^ ", " ^ n_to_string nexp1 ^ ", " ^ n_to_string nexp2 ^ ")"
  | NtEq(co,nexp1,nexp2) ->
    "NtEq(" ^ co_to_string co ^ ", " ^ n_to_string nexp1 ^ ", " ^ n_to_string nexp2 ^ ")"
  | GtEq (co,enforce,nexp1,nexp2) ->
    "GtEq(" ^ co_to_string co ^ ", " ^ enforce_to_string enforce ^ ", " ^
      n_to_string nexp1 ^ ", " ^ n_to_string nexp2 ^ ")"
  | Gt (co,enforce,nexp1,nexp2) ->
    "Gt(" ^ co_to_string co ^ ", " ^ enforce_to_string enforce ^ ", " ^
      n_to_string nexp1 ^ ", " ^ n_to_string nexp2 ^ ")"
  | In(co,var,ints) -> "In of " ^ var
  | InS(co,n,ints) -> "InS of " ^ n_to_string n
  | Predicate(co,cp,cn) -> 
    "Pred(" ^ co_to_string co ^ ", " ^ constraint_to_string cp ^", " ^ constraint_to_string cn ^  ")"
  | CondCons(co,kind,_,pats,exps) ->
    "CondCons(" ^ co_to_string co ^ ", " ^ cond_kind_to_string kind ^
    ", [" ^ constraints_to_string pats ^ "], [" ^ constraints_to_string exps ^ "])"
  | BranchCons(co,_,consts) ->
    "BranchCons(" ^ co_to_string co ^ ", [" ^ constraints_to_string consts ^ "])"
and constraints_to_string l = string_of_list "; " constraint_to_string l

let variable_range_to_string v = match v with
  | VR_eq (s,n) -> "vr_eq(" ^ s ^ ", " ^ n_to_string n ^ ")"
  | VR_range (s,cs) -> "vr_range(" ^ s ^ ", " ^ constraints_to_string cs ^ ")"
  | VR_vec_eq (s,n) -> "vr_vec_eq(" ^ s ^ ", " ^ n_to_string n ^ ")"
  | VR_vec_r (s,cs) -> "vr_vec_r(" ^ s ^ ", "^ constraints_to_string cs ^ ")"
  | VR_recheck (s,t) -> "vr_recheck(" ^ s ^ ", "^ t_to_string t ^ ")"

let bounds_to_string b = match b with
  | No_bounds -> "Nobounds"
  | Bounds(vs,map)-> "Bounds(" ^ string_of_list "; " variable_range_to_string vs ^ ")"

let rec tannot_to_string = function
  | NoTyp -> "No tannot"
  | Base((vars,t),tag,ncs,ef_l,ef_r,bv) ->
    "Tannot: type = " ^ (t_to_string t) ^ " tag = " ^ tag_to_string tag ^ " constraints = " ^
    constraints_to_string ncs ^ " effect_l = " ^ e_to_string ef_l ^ " effect_r = " ^ e_to_string ef_r ^
    "boundv = " ^ bounds_to_string bv
  | Overload(poly,_,variants) ->
    "Overloaded: poly = " ^ tannot_to_string poly

(* nexp constants, commonly used*)
let n_zero = mk_c zero
let n_one = mk_c one
let n_two = mk_c two

(*effect functions*)
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
  | Evar s,_ | _,Evar s -> 
    raise (Reporting_basic.err_unreachable Parse_ast.Unknown "union_effects given var(s) instead of uvar(s)")
  | Euvar _,_ -> e1.effect <- e2.effect; e2
  | _,Euvar _ -> e2.effect <- e1.effect; e2
  | Eset b1, Eset b2 -> 
    (*let _ = Printf.eprintf "union effects of length %s and %s\n" (e_to_string e1) (e_to_string e2) in*)
    {effect= Eset (effect_remove_dups (b1@b2))}  

let remove_local_effects ef = match ef.effect with
  | Evar _ | Euvar _ | Eset [] -> ef
  | Eset effects ->
    {effect = Eset (List.filter (fun (BE_aux(be,l)) -> (match be with | BE_lset | BE_lret -> false | _ -> true))
                                (effect_remove_dups effects)) }

let rec lookup_record_typ (typ : string) (env : rec_env list) : rec_env option =
  match env with
    | [] -> None
    | ((id,_,_,_) as r)::env -> 
      if typ = id then Some(r) else lookup_record_typ typ env

let rec fields_match f1 f2 =
  match f1 with
    | [] -> true
    | f::fs -> (List.mem_assoc f f2) && fields_match fs f2

let rec lookup_record_fields (fields : string list) (env : rec_env list) : rec_env option =
  match env with
    | [] -> None
    | ((id,r,t,fs) as re)::env ->
      if ((List.length fields) = (List.length fs)) &&
         (fields_match fields fs) then
        Some re
      else lookup_record_fields fields env

let rec lookup_possible_records (fields : string list) (env : rec_env list) : rec_env list =
  match env with
    | [] -> []
    | ((id,r,t,fs) as re)::env ->
      if (((List.length fields) <= (List.length fs)) &&
          (fields_match fields fs))
      then re::(lookup_possible_records fields env)
      else lookup_possible_records fields env

let lookup_field_type (field: string) ((id,r_kind,tannot,fields) : rec_env) : t option =
  if List.mem_assoc field fields
  then Some(List.assoc field fields)
  else None

let rec pow_i i n =
  match n with 
  | 0 -> one
  | n -> mult_int_big_int i (pow_i i (n-1))
let two_pow = pow_i 2

(* predicate to determine if pushing a constant in for addition or multiplication could change the form *)
let rec contains_const n =
  match n.nexp with
  | Nvar _ | Nuvar _ | Npow _ | N2n _ | Npos_inf | Nneg_inf | Ninexact -> false
  | Nconst _ | Nid _ -> true
  | Nneg n -> contains_const n
  | Nmult(n1,n2) | Nadd(n1,n2) | Nsub(n1,n2) -> (contains_const n1) || (contains_const n2)

let rec is_all_nuvar n =
  match n.nexp with
  | Nuvar { insubst = None } -> true
  | Nuvar { insubst = Some n } -> is_all_nuvar n
  | _ -> false

let rec first_non_nu n =
  match n.nexp with
  | Nuvar {insubst = None } -> None
  | Nuvar { insubst = Some n} -> first_non_nu n
  | _ -> Some n

(*Adds new_base to inner most position of n, when that is None 
  Report whether mutation happened*)
let add_to_nuvar_tail n new_base =
  if n.nexp == new_base.nexp
  then false
  else 
    let n' = get_inner_most n in
    let new_base' = get_outer_most new_base in
    match n'.nexp,new_base'.nexp with
    | Nuvar ({insubst = None} as nmu), Nuvar(nbmu) ->
      nmu.insubst <- Some new_base';
      nbmu.outsubst <- Some n'; true
    | Nuvar({insubst = None} as nmu),_ ->
      if new_base.nexp == new_base'.nexp
      then begin nmu.insubst <- Some new_base; true end
      else false
    | _ -> false

let rec get_var n =
  match n.nexp with
  | Nvar _ | Nuvar _ | N2n _ -> Some n
  | Nneg n -> get_var n
  | Nmult (_,n1) -> get_var n1
  | _ -> None

let rec get_all_nvar n = 
  match n.nexp with
    | Nvar v -> [v]
    | Nneg n | N2n(n,_) | Npow(n,_) -> get_all_nvar n
    | Nmult(n1,n2) | Nadd(n1,n2) | Nsub(n1,n2) -> (get_all_nvar n1)@(get_all_nvar n2)
    | _ -> []

let get_factor n =
  match n.nexp with
  | Nvar _ | Nuvar _ -> n_one
  | Nmult (n1,_)  -> n1
  | _ -> assert false

let increment_factor n i =
  match n.nexp with
  | Nvar _ | Nuvar _ | N2n _-> 
    (match i.nexp with
    | Nconst i -> 
      let ni = add_big_int i one in
      if eq_big_int ni zero 
      then n_zero
      else mk_mult (mk_c ni) n
    | _ -> mk_mult (mk_add i n_one) n)
  | Nmult(n1,n2) ->
    (match n1.nexp,i.nexp with
    | Nconst i2,Nconst i -> 
      let ni = add_big_int i i2 in
      if eq_big_int ni zero 
      then n_zero
      else mk_mult (mk_c(add_big_int i i2)) n2
    | _ -> mk_mult (mk_add n1 i) n2)
  | _ -> let _ = Printf.eprintf "increment_factor failed with %s by %s\n" (n_to_string n) (n_to_string i) in assert false

let negate n = match n.nexp with
  | Nconst i -> mk_c (mult_int_big_int (-1) i)
  | _ -> mk_mult (mk_c_int (-1)) n

let odd n = (n mod 2) = 1

(*Expects a normalized nexp*)
let rec nexp_negative n =
  match n.nexp with
    | Nconst i -> if lt_big_int i zero then Yes else No
    | Nneg_inf -> Yes
    | Npos_inf | N2n  _ | Nvar _ | Nuvar _ -> No
    | Nmult(n1,n2) -> (match nexp_negative n1, nexp_negative n2 with
        | Yes,Yes | No, No -> No
        | No, Yes | Yes, No -> Yes
        | Maybe,_ | _, Maybe -> Maybe)
    | Nadd(n1,n2) -> (match nexp_negative n1, nexp_negative n2 with
        | Yes,Yes -> Yes
        | No, No -> No
        | _ -> Maybe)
    | Npow(n1,i) ->
      (match nexp_negative n1 with
        | Yes -> if odd i then Yes else No
        | No -> No
        | Maybe -> if odd i then Maybe else No)
    | _ -> Maybe

let rec normalize_n_rec recur_ok n =
  (*let _ = Printf.eprintf "Working on normalizing %s\n" (n_to_string n) in *)
  match n.nexp with
  | Nid(_,n) -> normalize_n_rec true n
  | Nuvar _ ->
    (match first_non_nu (get_outer_most n) with
     | None -> n
     | Some n' -> n')
  | Nconst _ | Nvar _ | Npos_inf | Nneg_inf | Ninexact -> n
  | Nneg n -> 
    let n',to_recur,add_neg = (match n.nexp with
      | Nconst i -> negate n,false,false
      | Nadd(n1,n2) -> mk_add (negate n1) (negate n2),true,false
      | Nsub(n1,n2) -> mk_sub n2 n1,true,false
      | Nneg n -> n,true,false
      | _ -> n,true,true) in
    if to_recur 
    then (let n' = normalize_n_rec true n' in
          if add_neg 
          then negate n'
          else n')
    else n'
  | Npow(n,i) -> 
    let n' = normalize_n_rec true n in
    (match n'.nexp with
      | Nconst n -> mk_c (pow_i i (int_of_big_int n))
      | _ -> mk_pow n' i)
  | N2n(n', Some i) -> n (*Because there is a value for Some, we know this is normalized and n' is constant*)
  | N2n(n, None)    -> 
    let n' = normalize_n_rec true n in
    (match n'.nexp with
    | Nconst i -> mk_2nc n' (two_pow (int_of_big_int i))
    | _ -> mk_2n n')
  | Nadd(n1,n2) ->
    let n1',n2' = normalize_n_rec true n1, normalize_n_rec true n2 in
    (match n1'.nexp,n2'.nexp, recur_ok with
    | Nneg_inf, Npos_inf,_ | Npos_inf, Nneg_inf,_ -> mk_inexact()
    | Npos_inf, _,_ | _, Npos_inf, _ -> mk_p_inf()
    | Nneg_inf, _,_ | _, Nneg_inf, _ -> mk_n_inf() 
    | Nconst i1, Nconst i2,_ | Nconst i1, N2n(_,Some i2),_ 
    | N2n(_,Some i2), Nconst i1,_ | N2n(_,Some i1),N2n(_,Some i2),_
      -> mk_c (add_big_int i1 i2)
    | Nadd(n11,n12), Nconst i, true -> 
      if (eq_big_int i zero) then n1' 
      else normalize_n_rec false (mk_add n11 (normalize_n_rec false (mk_add n12 n2')))
    | Nadd(n11,n12), Nconst i, false ->
      if (eq_big_int i zero) then n1'
      else mk_add n11 (normalize_n_rec false (mk_add n12 n2'))
    | Nconst i, Nadd(n21,n22), true -> 
      if (eq_big_int i zero) then n2' 
      else normalize_n_rec false (mk_add n21 (normalize_n_rec false (mk_add n22 n1')))
    | Nconst i, Nadd(n21,n22), false ->
      if (eq_big_int i zero) then n2'
      else mk_add n21 (normalize_n_rec false (mk_add n22 n1'))
    | Nconst i, _,_ -> if (eq_big_int i zero) then n2' else mk_add n2' n1'
    | _, Nconst i,_ -> if (eq_big_int i zero) then n1' else mk_add n1' n2'
    | Nvar _, Nuvar _,_ | Nvar _, N2n _,_ | Nuvar _, Npow _,_ | Nuvar _, N2n _,_ -> mk_add n2' n1'
    | Nadd(n11,n12), Nadd(n21,n22), true ->
      (match compare_nexps n11 n21 with
      | -1 -> normalize_n_rec false (mk_add n11 (normalize_n_rec false (mk_add n12 n2')))
      | 0  -> 
        (match compare_nexps n12 n22 with
          | -1 -> normalize_n_rec true (mk_add (mk_mult n_two n11) (mk_add n22 n12))
          | 0 -> normalize_n_rec true (mk_add (mk_mult n_two n11) (mk_mult n_two n12))
          | _ -> normalize_n_rec true (mk_add (mk_mult n_two n11) (mk_add n12 n22)))
      | _  -> normalize_n_rec false (mk_add n21 (normalize_n_rec false (mk_add n22 n1'))))
    | Nadd(n11,n12), Nadd(n21,n22), false ->
      (match compare_nexps n11 n21 with
      | -1 -> mk_add n11 (normalize_n_rec false (mk_add n12 n2'))
      | 0  -> 
        (match compare_nexps n12 n22 with
          | -1 -> normalize_n_rec true (mk_add (mk_mult n_two n11) (mk_add n22 n12))
          | 0 -> normalize_n_rec true (mk_add (mk_mult n_two n11) (mk_mult n_two n12))
          | _ -> normalize_n_rec true (mk_add (mk_mult n_two n11) (mk_add n12 n22)))
      | _  -> mk_add n21 (normalize_n_rec false (mk_add n22 n1')))
    | N2n(n11,_), N2n(n21,_),_ -> 
      (match compare_nexps n11 n21 with
      | -1 -> mk_add n2' n1'
      |  0 -> mk_2n (normalize_n_rec true (mk_add n11 n_one))
      |  _ -> mk_add  n1' n2')
    | Npow(n11,i1), Npow (n21,i2),_ ->
      (match compare_nexps n11 n21, compare i1 i2 with
        | -1,-1 | 0,-1 -> mk_add n2' n1'
        |  0,0 -> mk_mult n_two n1'
        |  _ -> mk_add n1' n2')
    | N2n(n11,Some i),Nadd(n21,n22),_ ->
      normalize_n_rec true (mk_add n21 (mk_add n22 (mk_c i)))
    | Nadd(n11,n12), N2n(n21,Some i),_ ->
      normalize_n_rec true (mk_add n11 (mk_add n12 (mk_c i)))
    | N2n(n11,None),Nadd(n21,n22),_ ->
      (match n21.nexp with
        | N2n(n211,_) ->
          (match compare_nexps n11 n211 with
            | -1 -> mk_add n1' n2'
            | 0 -> mk_add (mk_2n (normalize_n_rec true (mk_add n11 n_one))) n22
            | _ -> mk_add n21 (normalize_n_rec true (mk_add n11 n22)))
        | _ -> mk_add n1' n2')
    | Nadd(n11,n12),N2n(n21,None),_ ->
      (match n11.nexp with
        | N2n(n111,_) ->
          (match compare_nexps n111 n21 with
            | -1 -> mk_add n11 (normalize_n_rec true (mk_add n2' n12))
            | 0 -> mk_add (mk_2n (normalize_n_rec true (mk_add n111 n_one))) n12
            | _ -> mk_add n2' n1')
        | _ -> mk_add n2' n1')
    | _ -> 
      (match get_var n1', get_var n2' with
      | Some(nv1),Some(nv2) ->
        (match compare_nexps nv1 nv2 with
        | -1 -> mk_add n2' n1'
        | 0 -> increment_factor n1' (get_factor n2')
        |  _ -> mk_add  n1' n2')
      | Some(nv1),None -> mk_add n2' n1'
      | None,Some(nv2) -> mk_add n1' n2'
      | _ -> (match n1'.nexp,n2'.nexp with
          | Nadd(n11',n12'), _ -> 
            (match compare_nexps n11' n2' with
              | -1 -> mk_add n2' n1'
              |  1 -> mk_add n11' (normalize_n_rec true (mk_add n12' n2'))
              | _ -> let _ = Printf.eprintf "Neither term has var but are the same? %s %s\n" 
                       (n_to_string n1') (n_to_string n2') in assert false)
          | (_, Nadd(n21',n22')) ->
            (match compare_nexps n1' n21' with
              | -1 -> mk_add n21' (normalize_n_rec true (mk_add n1' n22'))
              | 1 -> mk_add n1' n2'
              | _ -> let _ = Printf.eprintf "pattern didn't match unexpextedly here %s %s\n" 
                       (n_to_string n1') (n_to_string n2') in assert false)
          | _ -> 
            (match compare_nexps n1' n2' with
              | -1 -> mk_add n2' n1'
              | 0 -> normalize_n_rec true (mk_mult n_two n1')
              | _ -> mk_add n1' n2'))))
  | Nsub(n1,n2) ->
    let n1',n2' = normalize_n_rec true n1, normalize_n_rec true n2 in
    (*let _ = Printf.eprintf "Normalizing subtraction of %s - %s \n" (n_to_string n1') (n_to_string n2') in*)
    (match n1'.nexp,n2'.nexp with
    | Nneg_inf, Npos_inf | Npos_inf, Nneg_inf -> mk_inexact()
    | Npos_inf, _ | _,Nneg_inf -> mk_p_inf()
    | Nneg_inf, _ | _,Npos_inf -> mk_n_inf() 
    | Nconst i1, Nconst i2 | Nconst i1, N2n(_,Some i2) | N2n(_,Some i1), Nconst i2 | N2n(_,Some i1), N2n(_,Some i2)-> 
      (*let _ = Printf.eprintf "constant subtraction of %s - %s gives %s" (Big_int.string_of_big_int i1) (Big_int.string_of_big_int i2) (Big_int.string_of_big_int (sub_big_int i1 i2)) in*)
      mk_c (sub_big_int i1 i2)
    | Nconst i, _ -> 
      if (eq_big_int i zero) 
      then normalize_n_rec true (negate n2') 
      else normalize_n_rec true (mk_add (negate n2') n1')
    | _, Nconst i -> 
      if (eq_big_int i zero) 
      then n1' 
      else normalize_n_rec true (mk_add n1' (mk_c (mult_int_big_int (-1) i)))
    | _,_ -> 
      (match compare_nexps n1 n2 with
      |  0 -> n_zero
      |  -1 -> mk_add (negate n2') n1'
      | _ -> mk_add n1' (negate n2')))
  | Nmult(n1,n2) ->
    let n1',n2' = normalize_n_rec true n1, normalize_n_rec true n2 in
    (match n1'.nexp,n2'.nexp with
    | Nneg_inf,Nneg_inf -> mk_p_inf()
    | Npos_inf, Nconst i | Nconst i, Npos_inf ->
      if eq_big_int i zero then n_zero else mk_p_inf()
    | Nneg_inf, Nconst i | Nconst i, Nneg_inf ->
      if eq_big_int i zero then n_zero 
      else if lt_big_int i zero then mk_p_inf()
      else mk_n_inf()
    | Nneg_inf, _ | _, Nneg_inf -> 
      (match nexp_negative n1, nexp_negative n2 with
        | Yes, Yes -> mk_p_inf()
        | _ ->  mk_n_inf())
    | Npos_inf, _ | _, Npos_inf -> 
      (match nexp_negative n1, nexp_negative n2 with
        | Yes, Yes -> assert false (*One of them must be Npos_inf, so nexp_negative horribly broken*)
        | No, Yes | Yes, No -> mk_n_inf()
        | _ -> mk_p_inf())
    | Ninexact, _ | _, Ninexact -> mk_inexact()
    | Nconst i1, Nconst i2 -> mk_c (mult_big_int i1 i2)
    | Nconst i1, N2n(n,Some i2) | N2n(n,Some i2),Nconst i1 ->
      if eq_big_int i1 two 
      then mk_2nc (normalize_n_rec true (mk_add n n_one)) (mult_big_int i1 i2)
      else mk_c (mult_big_int i1 i2)
    | Nconst i1, N2n(n,None) | N2n(n,None),Nconst i1 ->
      if eq_big_int i1 two
      then mk_2n (normalize_n_rec true (mk_add n n_one))
      else mk_mult (mk_c i1) (mk_2n n)
    | (Nmult (_, _), (Nvar _|Npow (_, _)|Nuvar _)) -> mk_mult n1' n2'
    | Nvar _, Nuvar _ -> mk_mult n2' n1'
    | N2n(n1,Some i1),N2n(n2,Some i2) -> mk_2nc (normalize_n_rec true (mk_add n1 n2)) (mult_big_int i1 i2)
    | N2n(n1,_), N2n(n2,_) -> mk_2n (normalize_n_rec true (mk_add n1 n2))
    | N2n _, Nvar _ | N2n _, Nuvar _ | N2n _, Nmult _ | Nuvar _, N2n _   -> mk_mult n2' n1'
    | Nuvar _, Nuvar _ | Nvar _, Nvar _ ->
      (match compare n1' n2' with
      | 0 -> mk_pow n1' 2
      | 1 -> mk_mult n1' n2'
      | _ -> mk_mult n2' n1')
    | Npow(n1,i1),Npow(n2,i2) ->
      (match compare_nexps n1 n2 with
        | 0  -> mk_pow n1 (i1+i2)
        | -1 -> mk_mult n2' n1'
        | _  -> mk_mult n1' n2')
    | Nconst _, Nadd(n21,n22) | Nvar _,Nadd(n21,n22) | Nuvar _,Nadd(n21,n22) | N2n _, Nadd(n21,n22) 
    | Npow _,Nadd(n21,n22) | Nmult _, Nadd(n21,n22) ->
      normalize_n_rec true (mk_add (mk_mult n1' n21) (mk_mult n1' n21))
    | Nadd(n11,n12),Nconst _ | Nadd(n11,n12),Nvar _ | Nadd(n11,n12), Nuvar _ | Nadd(n11,n12), N2n _ 
    | Nadd(n11,n12),Npow _ | Nadd(n11,n12), Nmult _->
      normalize_n_rec true (mk_add (mk_mult n11 n2') (mk_mult n12 n2'))
    | Nmult(n11,n12), Nconst _ -> mk_mult (mk_mult n11 n2') (mk_mult n12 n2')
    | Nconst i1, _ ->
      if (eq_big_int i1 zero) then n1'
      else if (eq_big_int i1 one) then n2'
      else mk_mult n1' n2'
    | _, Nconst i1 ->
      if (eq_big_int i1 zero) then n2'
      else if (eq_big_int i1 one) then n1'
      else mk_mult n2' n1'
    | Nadd(n11,n12),Nadd(n21,n22) ->
      normalize_n_rec true (mk_add (mk_mult n11 n21)
                             (mk_add (mk_mult n11 n22)
                                (mk_add (mk_mult n12 n21) (mk_mult n12 n22))))
    | Nuvar _, Nvar _ | Nmult _, N2n _-> mk_mult n1' n2' 
    | Nuvar _, Nmult(n1,n2) | Nvar _, Nmult(n1,n2) -> (*TODO What's happend to n1'*)
      (match get_var n1, get_var n2 with
        | Some(nv1),Some(nv2) ->
          (match compare_nexps nv1 nv2, n2.nexp with
            | 0, Nuvar _ | 0, Nvar _    -> mk_mult n1 (mk_pow nv1 2)
            | 0, Npow(n2',i)            -> mk_mult n1 (mk_pow n2' (i+1))
            | -1, Nuvar _ | -1, Nvar _  -> mk_mult n2' n1'
            | _,_ -> mk_mult (normalize_n_rec true (mk_mult n1 n1')) n2)
        | _ -> mk_mult (normalize_n_rec true (mk_mult n1 n1')) n2)
    | (Npow (n1, i), (Nvar _ | Nuvar _)) -> 
      (match compare_nexps n1 n2' with
      | 0 -> mk_pow n1 (i+1)
      | _ -> mk_mult n1' n2')
    | (Npow (_, _), N2n (_, _)) | (Nvar _, (N2n (_, _)|Npow (_, _))) | (Nuvar _, Npow (_, _)) -> mk_mult n2' n1'
    | (N2n (_, _), Npow (_, _)) -> mk_mult n1' n2'
    | Npow(n1,i),Nmult(n21,n22) -> 
      (match get_var n1, get_var n2 with
        | Some(nv1),Some(nv2) -> 
          (match compare_nexps nv1 nv2,n22.nexp with
            | 0, Nuvar _ | 0, Nvar _ -> mk_mult n21 (mk_pow n1 (i+1))
            | 0, Npow(_,i2)          -> mk_mult n21 (mk_pow n1 (i+i2))
            | 1,Npow _ -> mk_mult (normalize_n_rec true (mk_mult n21 n1')) n22
            | _ -> mk_mult n2' n1')
        | _ -> mk_mult (normalize_n_rec true (mk_mult n1' n21)) n22)
    | Nmult _ ,Nmult(n21,n22) -> mk_mult (mk_mult n21 n1') (mk_mult n22 n1')
    | Nsub _, _ | _, Nsub _ -> 
      let _ = Printf.eprintf "nsub case still around %s\n" (n_to_string n) in assert false
    | Nneg _,_ | _,Nneg _ -> 
      let _ = Printf.eprintf "neg case still around %s\n" (n_to_string n) in assert false
    | Nid _, _ | _, Nid _ ->
      let _ = Printf.eprintf "nid case still around %s\n" (n_to_string n) in assert false
    (* If things are normal, neg should be gone. *)
    )
    
let normalize_nexp = normalize_n_rec true

let rec normalize_t t = match t.t with
  | Tfn (t1,t2,i,eff) -> {t = Tfn (normalize_t t1,normalize_t t2,i,eff)}
  | Ttup ts -> {t = Ttup (List.map normalize_t ts)}
  | Tapp (c,args) -> {t = Tapp (c, List.map normalize_t_arg args)}
  | Tabbrev (_,t') -> t'
  | _ -> t
and normalize_t_arg targ = match targ with
  | TA_typ t -> TA_typ (normalize_t t)
  | TA_nexp nexp -> TA_nexp (normalize_nexp nexp)
  | _ -> targ

let int_to_nexp = mk_c_int

let rec is_bit_vector t = match t.t with
  | Tapp("vector", [_;_;_; TA_typ t]) ->
    (match t.t with
     | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) | Tapp("register",[TA_typ {t=Tid "bit"}]) -> true
     | _ -> false)
  | Tapp("register", [TA_typ t']) -> is_bit_vector t'
  | Tabbrev(_,t') -> is_bit_vector t'
  | _ -> false

let rec has_const_vector_length t = match t.t with
  | Tapp("vector", [_;TA_nexp m;_;_]) ->
    (match (normalize_nexp m).nexp with
      | Nconst i -> Some i
      | _ -> None)
  | Tapp("register", [TA_typ t']) -> has_const_vector_length t'
  | Tabbrev(_,t') -> has_const_vector_length t'
  | _ -> None

let v_count = ref 0
let t_count = ref 0
let tuvars = ref []
let n_count = ref 0
let nuvars = ref []
let o_count = ref 0
let ouvars = ref []
let e_count = ref 0
let euvars = ref []

let reset_fresh _ = 
  begin v_count := 0;
        t_count := 0;
        tuvars  := [];
        n_count := 0;
        nuvars  := [];
        o_count := 0;
        ouvars  := [];
        e_count := 0;
        euvars  := [];
  end
let new_id _ =
  let i = !v_count in
  v_count := i+1;
  (string_of_int i) ^ "v"
let new_t _ = 
  let i = !t_count in
  t_count := i + 1;
  let t = {t = Tuvar { index = i; subst = None ; torig_name = None}} in
  tuvars := t::!tuvars;
  t
let new_tv rv = 
  let i = !t_count in
  t_count := i + 1;
  let t = {t = Tuvar { index = i; subst = None ; torig_name = Some rv}} in
  tuvars := t::!tuvars;
  t
let new_n _ = 
  let i = !n_count in
  n_count := i + 1;
  let n = { nexp = Nuvar { nindex = i; insubst = None; outsubst = None;
                           nin = false ; leave_var = false; orig_var = None; been_collapsed = false};
            imp_param = false} in
  nuvars := n::!nuvars;
  n
let new_nv s =
  let i = !n_count in
  n_count := i + 1;
  let n = { nexp = Nuvar { nindex = i; insubst = None ; outsubst = None;
                           nin = false ; leave_var = false ; orig_var = Some s; been_collapsed = false};
            imp_param = false} in
  nuvars := n::!nuvars;
  n
let leave_nuvar n = match n.nexp with
  | Nuvar u -> u.leave_var <- true; n
  | _ -> n
let set_imp_param n = 
  match n.nexp with
    | Nconst _ | Ninexact | Npos_inf | Nneg_inf -> ()
    | _ -> n.imp_param <- true

let new_o _ = 
  let i = !o_count in
  o_count := i + 1;
  let o = { order = Ouvar { oindex = i; osubst = None }} in
  ouvars := o::!ouvars;
  o
let new_e _ =
  let i = !e_count in
  e_count := i + 1;
  let e = { effect = Euvar { eindex = i; esubst = None }} in
  euvars := e::!euvars;
  e

exception Occurs_exn of t_arg
let rec resolve_tsubst (t : t) : t = 
  (*let _ = Printf.eprintf "resolve_tsubst on %s\n" (t_to_string t) in*)
  match t.t with
  | Tuvar({ subst=Some(t') } as u) ->
    let t'' = resolve_tsubst t' in
    (match t''.t with
    | Tuvar(_) -> u.subst <- Some(t''); t''
    | x -> t.t <- x; t)
  | _ -> t
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
    | Tfn(t1,t2,_,_) ->
      occurs_check_t t_box t1;
      occurs_check_t t_box t2
    | Ttup(ts) ->
      List.iter (occurs_check_t t_box) ts
    | Tapp(_,targs) -> List.iter (occurs_check_ta (TA_typ t_box)) targs
    | Tabbrev(t,ta) -> occurs_check_t t_box t; occurs_check_t t_box ta
    | Toptions(t1,None) -> occurs_check_t t_box t1
    | Toptions(t1,Some t2) -> occurs_check_t t_box t1; occurs_check_t t_box t2
    | _ -> ()
and occurs_check_ta (ta_box : t_arg) (ta : t_arg) : unit =
  match ta_box,ta with
  | TA_typ tbox,TA_typ t -> occurs_check_t tbox t
  | TA_nexp nbox, TA_nexp n -> occurs_check_n nbox n
  | TA_ord obox, TA_ord o -> occurs_check_o obox o
  | TA_eft ebox, TA_eft e -> occurs_check_e ebox e
  | _,_ -> ()
(*light-weight occurs check, does not look within nuvar chains*)
and occurs_check_n (n_box : nexp) (n : nexp) : unit =
  if n_box.nexp == n.nexp then
    raise (Occurs_exn (TA_nexp n))
  else
    match n.nexp with
    | Nadd(n1,n2) | Nmult(n1,n2) | Nsub(n1,n2) -> occurs_check_n n_box n1; occurs_check_n n_box n2
    | N2n(n,_) | Nneg n | Npow(n,_) -> occurs_check_n n_box n
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

(* Is checking for structural equality only, other forms of equality will be handeled by constraints *)
let rec nexp_eq_check n1 n2 =
  match n1.nexp,n2.nexp with
  | Npos_inf,Npos_inf | Nneg_inf,Nneg_inf | Ninexact,Ninexact -> true 
  | Nvar v1,Nvar v2 -> v1=v2
  | Nconst n1,Nconst n2 -> eq_big_int n1 n2
  | Nadd(nl1,nl2), Nadd(nr1,nr2) | Nmult(nl1,nl2), Nmult(nr1,nr2) | Nsub(nl1,nl2),Nsub(nr1,nr2) 
    -> nexp_eq_check nl1 nr1 && nexp_eq_check nl2 nr2
  | N2n(n,Some i),N2n(n2,Some i2) -> eq_big_int i i2
  | N2n(n,_),N2n(n2,_) -> nexp_eq_check n n2
  | Nneg n,Nneg n2 -> nexp_eq_check n n2
  | Npow(n1,i1),Npow(n2,i2) -> i1=i2 && nexp_eq_check n1 n2
  | Nuvar _,Nuvar _ ->
    let n1_in,n2_in = get_inner_most n1, get_inner_most n2 in
    (match n1_in.nexp, n2_in.nexp with
     | Nuvar{insubst=None; nindex=i1},Nuvar{insubst=None; nindex=i2} -> i1 = i2
     | _ -> nexp_eq_check n1_in n2_in)
  | _,_ -> false

let nexp_eq n1 n2 =
(*  let _ = Printf.eprintf "comparing nexps %s and %s\n" (n_to_string n1) (n_to_string n2) in*)
  let b = nexp_eq_check (normalize_nexp n1) (normalize_nexp n2) in
(*  let _ = Printf.eprintf "compared nexps %s\n" (string_of_bool b) in*)
  b


(*determine if ne is divisble without remainder by n,
  for now considering easily checked divisibility: 
    i.e. if ne is 2^n, where we otherwhere assume n>0 we just check for 2,
         not for numbers 2^m where n >= m
*)
let divisible_by ne n =
  let num,var,uvar,immediate_answer = match n.nexp with
    | Nconst i | N2n(_,Some i)->
      if eq_big_int i unit_big_int || eq_big_int i (minus_big_int unit_big_int)
      then None,None,None,Some true
      else Some i,None,None,None
    | Nvar v -> None, Some(v), None, None
    | Nuvar _ -> None, None, Some(get_index n), None
    | _ -> None, None, None, Some(false)
  in
  match immediate_answer with
  | Some answer -> answer
  | None ->
    let rec walk_nexp n = match n.nexp with
      | Npos_inf | Nneg_inf -> true
      | Ninexact -> false
      | Nvar v ->
        (match var with
        | Some v' -> v = v'
        | _ -> false)
      | Nuvar _ ->
        (match uvar with
         | Some n' ->  (get_index n) = n'
         | _ -> false)
      | Nconst i | N2n(_,Some i) ->
        (match num with
         | Some i' -> eq_big_int (mod_big_int i i') zero_big_int
         | _ -> false)
      | N2n(n,_) ->
        (match num with
         | Some i -> eq_big_int i (big_int_of_int 2)
         | _ -> false)
      | Npow(n,_) | Nneg n | Nid(_,n) -> walk_nexp n
      | Nmult(n1,n2) -> walk_nexp n1 || walk_nexp n2
      | Nadd(n1,n2) | Nsub(n1,n2) -> walk_nexp n1 && walk_nexp n2        
    in walk_nexp ne

(*divide ne by n, only gives correct answer when divisible_by is true*)
let divide_by ne n =
  let num,var,uvar,immediate_answer = match n.nexp with
    | Nconst i | N2n(_,Some i)->
      if eq_big_int i unit_big_int
      then None,None,None,Some n
      else if eq_big_int i (minus_big_int unit_big_int)
      then None,None,None,Some (mk_neg n)
      else Some i,None,None,None
    | Nvar v -> None, Some(v), None, None
    | Nuvar _ -> None, None, Some(get_index n), None
    | _ -> None, None, None, Some n
  in
  match immediate_answer with
  | Some answer -> answer
  | None ->
    let rec walk_nexp n = match n.nexp with
      | Nid(_,n) -> walk_nexp n
      | Npos_inf ->
        (match num with
        | Some(i) -> if lt_big_int i zero_big_int then mk_n_inf() else n
        | _ -> n)
      | Nneg_inf ->
        (match num with
         | Some(i) -> if lt_big_int i zero_big_int then mk_p_inf() else n
         | _ -> n)
      | Ninexact -> n
      | Nvar v ->
        (match var with
        | Some v' -> if v = v' then n_one else n
        | _ -> n)
      | Nuvar _ ->
        (match uvar with
         | Some n' ->  if (get_index n) = n' then n_one else n
         | _ -> n)
      | Nconst i | N2n(_,Some i) ->
        (match num with
         | Some i' -> mk_c (div_big_int i i')
         | _ -> n)
      | N2n(n1,_) ->
        (match num with
         | Some i -> if eq_big_int i (big_int_of_int 2) then mk_2n (mk_sub n1 n_one) else n
         | _ -> n)
      | Npow(nv,i) ->
        (match nv.nexp,var,uvar with
         | Nvar v, Some v', None -> if v = v' then mk_pow nv (i-1) else n
         | Nuvar _,None, Some i -> if (get_index nv) = i then mk_pow nv (i-1) else n
         | _ -> n)
      | Nneg n -> mk_neg (walk_nexp n)
      | Nmult(n1,n2) -> mk_mult (walk_nexp n1) (walk_nexp n2)
      | Nadd(n1,n2) -> mk_add (walk_nexp n1) (walk_nexp n2)
      | Nsub(n1,n2) -> mk_sub (walk_nexp n1) (walk_nexp n2)
    in walk_nexp ne  

(*Remove nv (assumed to be either a nuvar or an nvar) from ne as much as possible.
  Due to requiring integral values only, as well as variables multiplied by others, 
  there might be some non-removable factors
  Returns the variable with any non-removable factors, and the rest of the expression
*)
let isolate_nexp nv ne =
  let normal_ne = normalize_nexp ne in
  let var,uvar = match nv.nexp with
    | Nvar v -> Some v, None
    | Nuvar _ -> None, Some (get_index nv)
    | _ -> None, None in
  (* returns isolated_nexp, 
   option nv plus any factors, 
   option factors other than 1, 
   bool whether factors need to be divided from other terms*)
  let rec remove_from ne = match ne.nexp with
    | Nid(_,n) -> remove_from n
    | Npos_inf | Nneg_inf | Ninexact | Nconst _ | N2n(_,Some _)-> ne,None,None,false
    | Nvar v ->
      (match var with
       | Some v' -> if v = v' then (n_zero,Some ne,None,false) else (ne,None,None,false)
       | _ -> (ne,None,None,false))
    | Nuvar _ ->
      (match uvar with
       | Some n' ->  if (get_index ne) = n' then n_zero,Some ne,None,false else ne,None,None,false
       | _ -> ne,None,None,false)
    | N2n(n1,_) | Npow(n1,_)->
      (match remove_from n1 with
       | (_, None,_,_) -> ne,None,None,false
       | (_,Some _,_,_) -> (n_zero,Some ne,Some ne,false))
    | Nneg n -> assert false (*Normal forms shouldn't have nneg*)
    | Nmult(n1,n2) ->
      (match (remove_from n1, remove_from n2) with
       | (_, None,_,_),(_,None,_,_) -> (ne,None,None,false)
       | (_, None,_,_),(nv,Some n,None,false) ->
         if nexp_eq n1 n_one
         then (nv,Some n, None, false)
         else (n_zero, Some n, Some n1, true)
       | (_, None,_,_),(nv, Some n, Some nf, true) ->
         (nv, Some(mk_mult n1 n2), Some  (mk_mult n1 nf), true)
       | (_, None,_,_), (nv, Some n, Some nf, false) ->
         (nv, Some (mk_mult n1 n2), Some (mk_mult n1 n2), false)
       | _ -> (n_zero, Some ne, Some ne, false))
    | Nadd(n1,n2) ->
      (match (remove_from n1, remove_from n2) with
       | (_,None,_,_),(_,None,_,_) -> ne,None,None,false
       | (new_n1,Some nv,factor,try_factor),(_,None,_,_) -> (mk_add new_n1 n2, Some nv,factor,try_factor)
       | (_, None,_,_),(new_n2,Some nv,factor,try_factor) -> (mk_add n1 new_n2, Some nv,factor, try_factor)
       | (nn1, Some nv1,Some f1,true), (nn2, Some nv2,Some f2,true) ->
         if nexp_eq nv1 nv2
         then (mk_add nn1 nn2, Some nv1, Some (mk_add f1 f2), true)
         else (mk_add nn1 nn2, Some (mk_add nv1 nv2), Some (mk_add f1 f2), false)
       | (nn1, _,_,_),(nn2,_,_,_) ->
         (mk_add nn1 nn2, Some ne, Some ne, false) (*It's all gone horribly wrong, punt*))
    | Nsub(n1,n2) -> assert false in (*Normal forms shouldn't have nsub*)
  let (new_ne,new_nv,new_factor,attempt_factor) = remove_from normal_ne in
  let new_ne = normalize_nexp new_ne in
  match new_nv with
  | None -> None,None, new_ne
  | Some n_nv ->
    (match n_nv.nexp,new_factor,attempt_factor with
     | Nvar _, None, _ | Nuvar _, None, _ -> (Some n_nv,None,new_ne)
     | Nvar _, Some f, true | Nuvar _, Some f, true ->
       if divisible_by new_ne f
       then (Some n_nv, Some f, normalize_nexp (divide_by new_ne f))
       else (Some (mk_mult f n_nv), None, new_ne)
     | Nconst _,_,_ | Ninexact,_,_ | Npos_inf,_,_ | Nneg_inf,_,_ | Nid _,_,_ -> assert false (*double oh my*)
     | N2n _,_,_ | Npow _,_,_ | Nadd _,_,_ | Nneg _,_,_ | Nsub _,_,_ | Nvar _,_,false | Nuvar _,_,false
       -> (Some n_nv,None, new_ne)
     | Nmult(n1,n2),_,_ ->
       if nexp_eq n1 n_nv
       then if divisible_by new_ne n2
         then (Some n1, Some n2, normalize_nexp (divide_by new_ne n2))
         else (Some n_nv, None, new_ne)
       else if nexp_eq n2 n_nv
       then if divisible_by new_ne n1
         then (Some n2, Some n1, normalize_nexp (divide_by new_ne n1))
         else (Some n_nv, None, new_ne)
       else assert false (*really bad*))

let nexp_one_more_than n1 n2 =
  let n1,n2 = (normalize_nexp (normalize_nexp n1)), (normalize_nexp (normalize_nexp n2)) in
  match n1.nexp,n2.nexp with
    | Nconst i, Nconst j -> (int_of_big_int i) = (int_of_big_int j)+1
    | _, Nsub(n2',{nexp = Nconst i}) ->
      if (int_of_big_int i) = 1 then nexp_eq n1 n2' else false
    | _, Nadd(n2',{nexp = Nconst i}) ->
      if (int_of_big_int i) = -1 then nexp_eq n1 n2' else false
    | Nadd(n1',{nexp = Nconst i}),_ ->
      if (int_of_big_int i) = 1 then nexp_eq n1' n2 else false
    | _ -> false 
 

let rec nexp_gt_compare eq_ok n1 n2 = 
  let n1,n2 = (normalize_nexp (get_inner_most n1), normalize_nexp (get_inner_most n2)) in
  let ge_test = if eq_ok then ge_big_int else gt_big_int in
  let is_eq = nexp_eq n1 n2 in
  if eq_ok && is_eq
  then Yes
  else if (not eq_ok) && is_eq then No
  else
    match n1.nexp,n2.nexp with
      | Nconst i, Nconst j | N2n(_,Some i), N2n(_,Some j)-> if ge_test i j then Yes else No
      | Npos_inf, _ | _, Nneg_inf -> Yes
      | Nuvar _, Npos_inf | Nneg_inf, Nuvar _ -> if eq_ok then Maybe else No
      | Nneg_inf, _ | _, Npos_inf -> No
      | Ninexact, _ | _, Ninexact -> Maybe
      | N2n(n1,_), N2n(n2,_) -> nexp_gt_compare eq_ok n1 n2
      | Nmult(n11,n12), Nmult(n21,n22) ->
        if nexp_eq n12 n22
        then nexp_gt_compare eq_ok n11 n21
        else Maybe
      | Nmult(n11,n12), _ -> 
        if nexp_eq n12 n2 
        then triple_negate (nexp_negative n11)
        else Maybe
      | _, Nmult(n21,n22) ->
        if nexp_eq n1 n22 
        then nexp_negative n21 
        else Maybe
      | Nadd(n11,n12),Nadd(n21,n22) ->
        (match (nexp_gt_compare eq_ok n11 n21, nexp_gt_compare eq_ok n12 n22, 
                (nexp_negative n11, nexp_negative n12, nexp_negative n21, nexp_negative n22)) with
          | Yes, Yes, (No, No, No, No) -> Yes
          | No, No, (No, No, No, No) -> No
          | _ -> Maybe)
      | Nadd(n11,n12), _ ->
        if nexp_eq n11 n2 
        then triple_negate (nexp_negative n12)
        else if nexp_eq n12 n2 
        then triple_negate (nexp_negative n11)
        else Maybe
      | _ , Nadd(n21,n22) ->
        if nexp_eq n1 n21
        then nexp_negative n22
        else if nexp_eq n1 n22
        then nexp_negative n21
        else Maybe
      | Npow(n11,i1), Npow(n21, i2) ->
        if nexp_eq n11 n21
        then if i1 >= i2 then Yes else No
        else Maybe
      | Npow(n11,i1), _ ->
        if nexp_eq n11 n2
        then if i1 = 0 then No else Yes
        else Maybe
      | _, Npow(n21,i2) ->
        if nexp_eq n1 n21
        then if i2 = 0 then Yes else No
        else Maybe
      | _ -> Maybe

let nexp_ge = nexp_gt_compare true
let nexp_gt = nexp_gt_compare false
let nexp_le n1 n2 = nexp_gt_compare true n2 n1
let nexp_lt n1 n2 = nexp_gt_compare false n2 n1

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

(*Assumes that both are nuvar, and both set initially on outermost of chain *)
let rec occurs_in_nuvar_chain n_box n : bool =
  n_box.nexp == n.nexp || (*if both are at outermost and they are the same, then n occurs in n_box *)
  let n_box' = get_inner_most n_box in
  match n_box'.nexp with
  | Nuvar( { insubst= None }) -> false
  | Nuvar( { insubst= Some(n_box') }) -> occurs_in_nexp n_box' n
  | _ -> occurs_in_nexp n_box' n

(*Heavy-weight occurs check, including nuvar chains. Assumes second argument always a nuvar*)
and occurs_in_nexp n_box nuvar : bool =
(*  let _ = Printf.eprintf "occurs_in_nexp given n_box %s nuvar %s eq? %b\n" 
    (n_to_string n_box) (n_to_string nuvar) (n_box.nexp == nuvar.nexp) in*)
  if n_box.nexp == nuvar.nexp then true
  else match n_box.nexp with
    | Nuvar _ -> occurs_in_nuvar_chain (get_outer_most n_box) (get_outer_most nuvar)
    | Nadd (nb1,nb2) | Nsub(nb1,nb2)| Nmult (nb1,nb2) -> occurs_in_nexp nb1 nuvar || occurs_in_nexp nb2 nuvar
    | Nneg nb | N2n(nb,None) | Npow(nb,_) -> occurs_in_nexp nb nuvar
    | _ -> false

(*Assumes that n is set to it's outermost n*)
let collapse_nuvar_chain n =
  let rec collapse n = 
      match n.nexp with
      | Nuvar { insubst = None } -> (n,[n])
      | Nuvar ({insubst = Some ni } as u) ->
        (*let _ = Printf.eprintf "Collapsing %s, about to collapse it's insubst\n" (n_to_string n) in*)
        let _,internals = collapse ni in
        (*let _ = Printf.eprintf "Collapsed %s, with inner %s\n" (n_to_string n) (n_to_string ni) in*)
        (match ni.nexp with
         | Nuvar nim ->
           u.leave_var <- u.leave_var || nim.leave_var;
           u.nin <- u.nin || nim.nin;
           u.orig_var <- (match u.orig_var,nim.orig_var with
               | None, None -> None
               | Some i, Some j -> if i = j then Some i else None
               | Some i,_ | _, Some i -> Some i);
           u.insubst <- None;
           u.outsubst <- None;
           u.been_collapsed <- true;
           (*Shouldn't need this but Somewhere somethings going wonky*)
           (*nim.nindex <- u.nindex; *)
           (n,n::internals) 
         | _ -> if u.leave_var then u.insubst <- Some ni else n.nexp <- ni.nexp; (n,[n]))
      | _ -> (n,[n])
  in
  let rec set_nexp n_from n_to_s = match n_to_s with
    | [] -> n_from
    | n_to::n_to_s -> n_to.nexp <- n_from.nexp; set_nexp n_from n_to_s in
  let (n,all) = collapse n in
  set_nexp n (List.tl all)

(*assumes called on outermost*)
let rec leave_nu_as_var n = 
  match n.nexp with
    | Nuvar nu ->
      (match nu.insubst with
        | None -> nu.leave_var
        | Some(nexp) -> nu.leave_var || leave_nu_as_var nexp)
    | _ -> false

let equate_n (n_box : nexp) (n : nexp) : bool =
  (*let _ = Printf.eprintf "equate_n given n_box %s and n %s\n" (n_to_string n_box) (n_to_string n) in*)
  let n_box = get_outer_most n_box in
  let n = get_outer_most n in
  if n_box.nexp == n.nexp then true
  else
    let occur_nbox_n = occurs_in_nexp n_box n in
    let occur_n_nbox = occurs_in_nexp n n_box in
    match (occur_nbox_n,occur_n_nbox) with
    | true,true -> false
    | true,false | false,true -> true
    | false,false ->
      (*let _ = Printf.eprintf "equate_n has does not occur in %s and %s\n" (n_to_string n_box) (n_to_string n) in*)
      (*If one is empty, set the empty one into the bottom of the other one if you can, but put it in the chain
        If neither are empty, merge but make sure to set the nexp to be the same (not yet being done)
      *)
      match n_box.nexp,n.nexp with
      | Nuvar _, Nuvar _ | Nuvar _, _ | _, Nuvar _ -> add_to_nuvar_tail n_box n
      | _ -> false
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
       | _ -> o.order <- o_box.order)
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

let fresh_var just_use_base varbase i mkr bindings =
  let v = if just_use_base then varbase else "'" ^ varbase ^ (string_of_int i) in
  match Envmap.apply bindings v with
  | Some _ -> mkr v false
  | None -> mkr v true

let rec fresh_tvar bindings t =
  match t.t with
  | Tuvar { index = i;subst = None } -> 
    fresh_var false "tv" i (fun v add -> equate_t t {t=Tvar v}; if add then Some (v,{k=K_Typ}) else None) bindings
  | Tuvar { index = i; subst = Some ({t = Tuvar _} as t') } ->
    let kv = fresh_tvar bindings t' in
    equate_t t t';
    kv
  | Tuvar { index = i; subst = Some t' } ->
    t.t <- t'.t;
    None
  | _ -> None
let rec fresh_nvar bindings n =
  (*let _ = Printf.eprintf "fresh_nvar for %s\n" (n_to_string n) in*)
  match n.nexp with
    | Nuvar { nindex = i;insubst = None ; orig_var = None } -> 
      fresh_var false "nv" i (fun v add -> n.nexp <- (Nvar v); 
                         (*(Printf.eprintf "fresh nvar set %i to %s : %s\n" i v (n_to_string n));*)
                         if add then Some(v,{k=K_Nat}) else None) bindings
    | Nuvar { nindex = i;insubst = None ; orig_var = Some v } -> 
      fresh_var true v 0 (fun v add -> n.nexp <- (Nvar v); 
                      (*(Printf.eprintf "fresh nvar set %i to %s : %s\n" i v (n_to_string n));*)
                      if add then Some(v,{k=K_Nat}) else None) bindings        
    | Nuvar { nindex = i; insubst = Some n' } ->
      n.nexp <- n'.nexp;
      None
    | _ -> None
let rec fresh_ovar bindings o =
  match o.order with
    | Ouvar { oindex = i;osubst = None } -> 
      fresh_var false "ov" i (fun v add -> equate_o o {order = (Ovar v)};
                               if add then Some(v,{k=K_Nat}) else None) bindings
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
      fresh_var false "ev" i (fun v add -> equate_e e {effect = (Evar v)};
                               if add then Some(v,{k=K_Nat}) else None) bindings
    | Euvar { eindex = i; esubst = Some({effect=Euvar _} as e')} ->
      let kv = fresh_evar bindings e' in
      equate_e e e';
      kv
    | Euvar { eindex = i; esubst = Some e' } ->
      e.effect <- e'.effect;
      None
    | _ -> None

let contains_nuvar_nexp n ne = 
  let compare_to i = match n.nexp with
    | Nuvar {nindex = i2} -> i = i2
    | _ -> false in
  let rec search ne = 
    match ne.nexp with
      | Nuvar {nindex =i}-> compare_to i
      | Nadd(n1,n2) | Nmult(n1,n2) | Nsub(n1,n2) -> search n1 || search n2
      | N2n(n,_) | Nneg n | Npow(n,_) -> search n
      | _ -> false in
  search ne

let contains_nvar_nexp n ne =
  let compare_to v = match n.nexp with
    | Nvar v' -> v = v'
    | _ -> false in
  let rec search ne =
    match ne.nexp with
    | Nvar v-> compare_to v
    | Nadd(n1,n2) | Nmult(n1,n2) | Nsub(n1,n2) -> search n1 || search n2
    | N2n(n,_) | Nneg n | Npow(n,_) -> search n
    | _ -> false in
  search ne

let rec contains_n nexp_contains n cs =
  let contains = contains_n nexp_contains in
  match cs with
  | [] -> []
  | ((LtEq(_,_,nl,nr) | Lt(_,_,nl,nr) | GtEq(_,_,nl,nr) | Gt(_,_,nl,nr) | Eq(_,nl,nr) | NtEq(_,nl,nr)) as co)::cs ->
    if (nexp_contains n nl || nexp_contains n nr)
    then co::(contains n cs)
    else contains n cs
  | CondCons(so,kind,_,conds,exps)::cs -> 
    let conds' = contains n conds in
    let exps' = contains n exps in
    (match conds',exps' with
      | [],[] -> contains n cs
      | _ -> CondCons(so,kind,None,conds',exps')::contains n cs)
  | BranchCons(so,_,b_cs)::cs ->
    (match contains n b_cs with
      | [] -> contains n cs
      | b -> BranchCons(so,None,b)::contains n cs)
  | (Predicate(so,cp,cn) as co)::cs ->
    (match contains n [cp;cn] with
      | [] -> contains n cs
      | _ -> co::contains n cs)
  | _::cs -> contains n cs
  
let contains_nuvar = contains_n contains_nuvar_nexp
let contains_nvar = contains_n contains_nvar_nexp

let rec refine_guarantees check_nvar max_lt min_gt id cs =
  match cs with
    | [] -> 
      (match max_lt,min_gt with
        | None,None -> []
        | Some(c,i),None -> [LtEq(c,Guarantee,id,i)]
        | None,Some(c,i) -> [GtEq(c,Guarantee,id,i)]
        | Some(cl,il),Some(cg,ig) -> [LtEq(cl,Guarantee,id,il);GtEq(cg,Guarantee,id,ig)]), max_lt, min_gt
    | (LtEq(c,Guarantee,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_guarantees check_nvar max_lt min_gt id cs in
        curr::cs,max,min in
      (*let _ = Printf.eprintf "refine_guarantee %s\n" (constraints_to_string [curr]) in*)
      (match nes.nexp,neb.nexp,check_nvar,max_lt,min_gt with
       | Nuvar _ , _, false, None, _ | Nvar _, _, true, None, _ ->
         (*let _ = Printf.eprintf "in var nill case of <=\n" in *)
         if nexp_eq id nes 
         then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar (Some(c,neb)) min_gt id cs (*new max*)
         else no_match ()
       | _ , Nuvar _, false, _, None | _,Nvar _, true, _, None ->
         (*let _ = Printf.eprintf "in var nill case of <=\n" in *)
         if nexp_eq id neb 
         then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar max_lt (Some(c,nes)) id cs (*new min*)
         else no_match ()
       | Nuvar _, _, false, Some(cm, omax), _ | Nvar _, _, true,Some(cm, omax), _ ->
         (*let _ = Printf.eprintf "in var case of <=\n" in *)
         if nexp_eq id nes
         then match nexp_ge neb omax with
           | Yes -> refine_guarantees check_nvar (Some(c,neb)) min_gt id cs (*replace old max*)
           | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint *)
           | Maybe -> no_match ()              
         else no_match ()
       | _, Nuvar _, false, _, Some(cm, omin) | _, Nvar _, true,_, Some(cm, omin) ->
         (*let _ = Printf.eprintf "in var case of <=\n" in *)
         if nexp_eq id neb
         then match nexp_le nes omin with
           | Yes -> refine_guarantees check_nvar max_lt (Some(c,nes)) id cs (*replace old min*)
           | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint *)
           | Maybe -> no_match ()              
         else no_match ()
       | _ -> no_match ())
    | (Lt(c,Guarantee,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_guarantees check_nvar max_lt min_gt id cs in
        curr::cs,max,min in
            (*let _ = Printf.eprintf "refine_guarantee %s\n" (constraints_to_string [curr]) in*)
      (match nes.nexp,neb.nexp,check_nvar,max_lt,min_gt with
       | Nuvar _, _, false, None, _ | Nvar _, _, true, None, _->
         (*let _ = Printf.eprintf "in var, nil case of <\n" in *)
          if nexp_eq id nes 
          then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar (Some(c,neb)) min_gt id cs (*new max*)
          else no_match ()
       | _, Nuvar _, false, _, None | _, Nvar _, true, _, None->
         (*let _ = Printf.eprintf "in var, nil case of <\n" in *)
          if nexp_eq id neb 
          then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar max_lt (Some(c,nes)) id cs (*new max*)
          else no_match ()
       | Nuvar _, _, false, Some(cm, omax), _ | Nvar _, _, true, Some(cm, omax), _ ->
         (*let _ = Printf.eprintf "in var case of <\n" in *)
          if nexp_eq id nes
          then match nexp_gt neb omax with
            | Yes -> refine_guarantees check_nvar (Some(c,neb)) min_gt id cs (*replace old max*)
            | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
       | _, Nuvar _, false, _, Some(cm, omin) | _, Nvar _, true, _, Some(cm, omin) ->
         (*let _ = Printf.eprintf "in var case of <\n" in *)
          if nexp_eq id neb
          then match nexp_lt nes omin with
            | Yes -> refine_guarantees check_nvar max_lt (Some(c,nes)) id cs (*replace old min*)
            | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
        | _ -> no_match ())
    | (GtEq(c,Guarantee,nes,neb) as curr)::cs ->
      (*let _ = Printf.eprintf "refine_guarantee %s\n" (constraints_to_string [curr]) in*)
      let no_match _ =
        let (cs,max,min) = refine_guarantees check_nvar max_lt min_gt id cs in
        curr::cs,max,min in
      (match nes.nexp,neb.nexp,check_nvar,min_gt,max_lt with
       | Nuvar _, _, false, None, _ | Nvar _, _, true, None, _->
         (*let _ = Printf.eprintf "in var, nil case of >=\n" in *)
         if nexp_eq id nes 
         then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar max_lt (Some(c,neb)) id cs (*new min*)
         else no_match ()
       | _, Nuvar _, false, _, None | _, Nvar _, true, _, None->
         (*let _ = Printf.eprintf "in var, nil case of >=\n" in *)
         if nexp_eq id neb
         then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar (Some(c,nes)) min_gt id cs (*new max*)
         else no_match ()
       | Nuvar _, _, false, Some(cm, omin), _ | Nvar _, _, true, Some(cm, omin), _ ->
         (*let _ = Printf.eprintf "in var case of >=\n" in *)
         if nexp_eq id nes
         then match nexp_le neb omin with
           | Yes ->  refine_guarantees check_nvar max_lt (Some(c,neb)) id cs (*replace old min*)
           | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint*)
           | Maybe -> no_match ()
         else no_match ()
       | _, Nuvar _, false, _, Some(cm, omax) | _, Nvar _, true, _, Some(cm, omax) ->
         (*let _ = Printf.eprintf "in var case of >=\n" in *)
         if nexp_eq id neb
         then match nexp_ge nes omax with
           | Yes ->  refine_guarantees check_nvar (Some(c,nes)) min_gt id cs (*replace old max*)
           | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint*)
           | Maybe -> no_match ()
         else no_match ()
       | _ -> no_match ())
    | (Gt(c,Guarantee,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_guarantees check_nvar max_lt min_gt id cs in
        curr::cs,max,min in
           (* let _ = Printf.eprintf "refine_guarantee %s\n" (constraints_to_string [curr]) in*)
      (match nes.nexp,neb.nexp,check_nvar,min_gt,max_lt with
       | Nuvar _,_, false, None,_ | Nvar _, _, true, None,_->
         (*let _ = Printf.eprintf "in var, nil case of >\n" in *)
          if nexp_eq id nes 
          then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar max_lt (Some(c,neb)) id cs (*new min*)
          else no_match ()
       | _, Nuvar _, false, _, None | _, Nvar _, true, _, None ->
         (*let _ = Printf.eprintf "in var, nil case of >\n" in *)
         if nexp_eq id neb 
          then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_guarantees check_nvar (Some(c,nes)) min_gt id cs (*new max*)
          else no_match ()
       | Nuvar _, _, false, Some(cm, omin), _ | Nvar _, _, true, Some(cm, omin), _ ->
         (*let _ = Printf.eprintf "in var case of >\n" in *)
          if nexp_eq id nes
          then match nexp_lt neb omin with
            | Yes -> refine_guarantees check_nvar max_lt (Some(c,neb)) id cs (*replace old min*)
            | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
       | _, Nuvar _, false, _, Some(cm, omax) | _, Nvar _, true, _, Some(cm, omax) ->
         (*let _ = Printf.eprintf "in var case of >\n" in *)
         if nexp_eq id neb
         then match nexp_gt nes omax with
           | Yes -> refine_guarantees check_nvar (Some(c,nes)) min_gt id cs (*replace old min*)
           | No -> refine_guarantees check_nvar max_lt min_gt id cs (*remove redundant constraint*)
           | Maybe -> no_match ()
         else no_match ()
       | _ -> no_match ())
    | c::cs ->
      (*let _ = Printf.eprintf "refine_guarantee %s\n" (constraints_to_string [c]) in*)
      let (cs,max,min) = refine_guarantees check_nvar max_lt min_gt id cs in
      c::cs,max,min

let rec refine_requires check_nvar min_lt max_gt id cs =
  match cs with
    | [] -> 
      (match min_lt,max_gt with
        | None,None -> []
        | Some(c,i),None -> [LtEq(c,Require,id,i)]
        | None,Some(c,i) -> [GtEq(c,Require,id,i)]
        | Some(cl,il),Some(cg,ig) -> [LtEq(cl,Require,id,il);GtEq(cg,Require,id,ig)]), min_lt,max_gt
    | (LtEq(c,Require,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_requires check_nvar min_lt max_gt id cs in
        curr::cs,max,min in
      (match nes.nexp,neb.nexp,check_nvar,min_lt,max_gt with
       | Nuvar _, _, false, None, _ | Nvar _, _, true, None, _ ->
         if nexp_eq id nes 
         then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar (Some(c,neb)) max_gt id cs (*new min*)
         else no_match ()
       | _, Nuvar _, false, _, None | _, Nvar _, true, _, None ->
         if nexp_eq id neb 
         then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar min_lt (Some(c,neb)) id cs (*new max*)
         else no_match ()
       | Nuvar _, _, false, Some(cm, omin), _ | Nvar _, _, true, Some(cm, omin), _ ->
         if nexp_eq id nes
         then match nexp_le neb omin with
           | Yes -> refine_requires check_nvar (Some(c,neb)) max_gt id cs (*replace old min*)
           | No -> refine_requires check_nvar min_lt max_gt id cs (*remove redundant constraint*)
           | Maybe -> no_match ()
         else no_match()
       | _, Nuvar _, false, _, Some(cm, omax) | _, Nvar _, true, _, Some(cm, omax) ->
         if nexp_eq id neb
         then match nexp_ge nes omax with
           | Yes -> refine_requires check_nvar min_lt (Some(c,nes)) id cs (*replace old max*)
           | No -> refine_requires check_nvar min_lt max_gt id cs (*remove redundant constraint*)
           | Maybe -> no_match ()
         else no_match()
        | _ -> no_match())
    | (Lt(c,Require,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_requires check_nvar min_lt max_gt id cs in
        curr::cs,max,min in
      (match nes.nexp,neb.nexp,check_nvar,min_lt,max_gt with
        | Nuvar _, _, false, None, _ | Nvar _, _, true, None, _->
          if nexp_eq id nes 
          then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar(Some(c,neb)) max_gt id cs (*new min*)
          else no_match ()
        | _, Nuvar _, false, _, None | _, Nvar _, true, _, None->
          if nexp_eq id neb 
          then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar min_lt (Some(c,nes)) id cs (*new max*)
          else no_match ()
        | Nuvar _, _, false, Some(cm, omin), _ | Nvar _, _, true, Some(cm, omin), _ ->
          if nexp_eq id nes
          then match nexp_lt neb omin with
            | Yes -> refine_requires check_nvar (Some(c,neb)) max_gt id cs (*replace old min*)
            | No  -> refine_requires check_nvar min_lt max_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
        | _, Nuvar _, false, _, Some(cm, omax) | _, Nvar _,true, _, Some(cm, omax) ->
          if nexp_eq id neb
          then match nexp_gt nes omax with
            | Yes -> refine_requires check_nvar min_lt (Some(c,nes)) id cs (*replace old max*)
            | No  -> refine_requires check_nvar min_lt max_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
        | _ -> no_match())
    | (GtEq(c,Require,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_requires check_nvar min_lt max_gt id cs in
        curr::cs,max,min in
      (match nes.nexp,neb.nexp,check_nvar,max_gt,min_lt with
        | Nuvar _, _, false, None, _ | Nvar _, _, true, None, _ ->
          if nexp_eq id nes 
          then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar min_lt (Some(c,neb)) id cs (*new max*)
          else no_match ()
        | _, Nuvar _, false, _, None | _, Nvar _, true, _, None ->
          if nexp_eq id neb 
          then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar (Some(c,nes)) max_gt id cs (*new min*)
          else no_match ()
        | Nuvar _, _, false, Some(cm, omax), _ | Nvar _, _, true, Some(cm, omax), _ ->
          if nexp_eq id nes
          then match nexp_ge neb omax with
            | Yes -> refine_requires check_nvar min_lt (Some(c,neb)) id cs (*replace old max*)
            | No  -> refine_requires check_nvar min_lt max_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
        | _, Nuvar _, false, _, Some(cm, omin) | _, Nvar _, true, _, Some(cm, omin) ->
          if nexp_eq id neb
          then match nexp_le nes omin with
            | Yes -> refine_requires check_nvar (Some(c,neb)) max_gt id cs (*replace old min*)
            | No  -> refine_requires check_nvar min_lt max_gt id cs (*remove redundant constraint*)
            | Maybe -> no_match ()
          else no_match ()
        | _ -> no_match ())
    | (Gt(c,Require,nes,neb) as curr)::cs ->
      let no_match _ =
        let (cs,max,min) = refine_requires check_nvar min_lt max_gt id cs in
        curr::cs,max,min in
      (match nes.nexp,neb.nexp,check_nvar,max_gt,min_lt with
        | Nuvar _, _, true, None, _ | Nvar _, _, false, None, _ ->
          if nexp_eq id nes 
          then match neb.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar min_lt (Some(c,neb)) id cs (*new max*)
          else refine_requires check_nvar min_lt max_gt id cs
        | _, Nuvar _, true, _, None | _, Nvar _, false, _, None->
          if nexp_eq id neb 
          then match nes.nexp with
           | Nuvar _ | Nvar _ -> no_match () (*Don't set a variable to a max/min*)
           | _ -> refine_requires check_nvar (Some(c,nes)) max_gt id cs (*new min*)
          else refine_requires check_nvar min_lt max_gt id cs
        | Nuvar _, _, false, Some(cm, omax), _ | Nvar _, _, true, Some(cm, omax), _ ->
          if nexp_eq id nes
          then match nexp_gt neb omax with
            | Yes -> refine_requires check_nvar min_lt (Some(c,neb)) id cs (*replace old max*)
            | No -> refine_requires check_nvar min_lt max_gt id cs (* remove redundant constraint *)
            | Maybe -> no_match ()
          else no_match ()
        | _, Nuvar _, false, _, Some(cm, omin) | _, Nvar _, true, _, Some(cm, omin) ->
          if nexp_eq id neb
          then match nexp_lt nes omin with
            | Yes -> refine_requires check_nvar (Some(c,nes)) max_gt id cs (*replace old min*)
            | No -> refine_requires check_nvar min_lt max_gt id cs (* remove redundant constraint *)
            | Maybe -> no_match ()
          else no_match ()
        | _ -> no_match())
    | c::cs ->
      let (cs,min,max) = refine_requires check_nvar min_lt max_gt id cs in
      c::cs,min_lt,max_gt

let nat_t = {t = Tapp("range",[TA_nexp n_zero;TA_nexp (mk_p_inf());])}
let int_t = {t = Tapp("range",[TA_nexp (mk_n_inf());TA_nexp (mk_p_inf());])}
let uint8_t = {t = Tapp("range",[TA_nexp n_zero; TA_nexp (mk_sub (mk_2nc (mk_c_int 8) (big_int_of_int 256)) n_one)])}
let uint16_t = {t = Tapp("range",[TA_nexp n_zero;
                                  TA_nexp (mk_sub (mk_2nc (mk_c_int 16) (big_int_of_int 65536)) n_one)])}
let uint32_t = {t = Tapp("range",[TA_nexp n_zero;
                                  TA_nexp (mk_sub (mk_2nc (mk_c_int 32) (big_int_of_string "4294967296")) n_one)])}
let uint64_t = {t = Tapp("range",[TA_nexp n_zero;
                                  TA_nexp (mk_sub (mk_2nc (mk_c_int 64) (big_int_of_string "18446744073709551616"))
                                             (mk_c_int 1))
                                 ])}

let int8_t = {t = Tapp("range", [TA_nexp (mk_neg (mk_2nc (mk_c_int 7) (big_int_of_int 128))) ;
                                 TA_nexp (mk_c_int 127)])}
let int16_t = {t = Tapp("range", [TA_nexp (mk_neg (mk_2nc (mk_c_int 15) (big_int_of_int 32768)));
                                  TA_nexp (mk_c_int 32767)])}
let int32_t = {t = Tapp("range", [TA_nexp (mk_neg (mk_2nc (mk_c_int 31) (big_int_of_int 2147483648))) ;
                                  TA_nexp (mk_c_int 2147483647)])}
let int64_t = {t = Tapp("range", [TA_nexp (mk_neg (mk_2nc (mk_c_int 63) (big_int_of_string "9223372036854775808")));
                                  TA_nexp (mk_c (big_int_of_string "9223372036854775807"))])}

let unit_t = { t = Tid "unit" }
let bit_t = {t = Tid "bit" }
let bool_t = {t = Tid "bool" }
let nat_typ = {t=Tid "nat"}
let string_t = {t = Tid "string"}
let pure_e = {effect=Eset []}
let nob = No_bounds

let rec get_cummulative_effects = function
  | NoTyp -> pure_e
  | Base(_,_,_,_,efr,_) -> efr
  | _ -> pure_e

let get_eannot (E_aux(_,(l,annot))) = annot

let initial_kind_env = 
  Envmap.from_list [ 
    ("bool", {k = K_Typ});
    ("nat", {k = K_Typ});
    ("int", {k = K_Typ});
    ("uint8", {k = K_Typ});
    ("uint16", {k= K_Typ});
    ("uint32", {k=K_Typ});
    ("uint64", {k=K_Typ});
    ("unit", {k = K_Typ});
    ("bit", {k = K_Typ});
    ("string", {k = K_Typ});
    ("list", {k = K_Lam( [{k = K_Typ}], {k = K_Typ})});
    ("reg", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("register", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("range", {k = K_Lam( [ {k = K_Nat}; {k= K_Nat}], {k = K_Typ}) });
    ("vector", {k = K_Lam( [ {k = K_Nat}; {k = K_Nat}; {k= K_Ord} ; {k=K_Typ}], {k=K_Typ}) } );
    ("atom", {k = K_Lam( [ {k=K_Nat} ], {k=K_Typ})});
    ("option", { k = K_Lam( [{k=K_Typ}], {k=K_Typ}) });
    ("implicit", {k = K_Lam( [{k = K_Nat}], {k=K_Typ})} );
  ]

let simple_annot t = Base(([],t),Emp_local,[],pure_e,pure_e,nob)
let simple_annot_efr t efr = Base(([],t),Emp_local,[],pure_e,efr,nob)
let global_annot t = Base(([],t),Emp_global,[],pure_e,pure_e,nob)
let tag_annot t tag = Base(([],t),tag,[],pure_e,pure_e,nob)
let tag_annot_efr t tag efr = Base(([],t),tag,[],pure_e,efr,nob)
let constrained_annot t cs = Base(([],t),Emp_local,cs,pure_e,pure_e,nob)
let constrained_annot_efr t cs efr = Base(([],t),Emp_local,cs,pure_e,efr,nob)
let bounds_annot t bs = Base(([],t),Emp_local,[],pure_e,pure_e,bs)
let bounds_annot_efr t bs efr = Base(([],t),Emp_local,[],pure_e,efr,bs)
let cons_tag_annot t tag cs = Base(([],t),tag,cs,pure_e,pure_e,nob)
let cons_tag_annot_efr t tag cs efr = Base(([],t),tag,cs,pure_e,efr,nob)
let cons_efl_annot t cs ef = Base(([],t),Emp_local,cs,ef,pure_e,nob)
let cons_efs_annot t cs efl efr = Base(([],t),Emp_local,cs,efl,efr,nob)
let efs_annot t efl efr = Base(([],t),Emp_local,[],efl,efr,nob)
let tag_efs_annot t tag efl efr = Base(([],t),tag,[],efl,efr,nob)
let cons_bs_annot t cs bs = Base(([],t),Emp_local,cs,pure_e,pure_e,bs)
let cons_bs_annot_efr t cs bs efr = Base(([],t), Emp_local, cs, pure_e, efr, bs)

let initial_abbrev_env =
  Envmap.from_list [
    ("nat",global_annot nat_t);
    ("int",global_annot int_t);
    ("uint8",global_annot uint8_t);
    ("uint16",global_annot uint16_t);
    ("uint32",global_annot uint32_t);
    ("uint64",global_annot uint64_t);
    ("bool",global_annot bit_t);
  ]

let mk_nat_params l = List.map (fun i -> (i,{k=K_Nat})) l
let mk_typ_params l = List.map (fun i -> (i,{k=K_Typ})) l
let mk_ord_params l = List.map (fun i -> (i,{k=K_Ord})) l

let mk_tup ts = {t = Ttup ts }
let mk_pure_fun arg ret = {t = Tfn (arg,ret,IP_none,pure_e)}
let mk_pure_imp arg ret var = {t = Tfn (arg,ret,IP_length (mk_nv var),pure_e)}

let lib_tannot param_typs func cs =
  Base(param_typs, External func, cs, pure_e, pure_e, nob)

let mk_ovar s = {order = Ovar s}
let mk_range n1 n2 = {t=Tapp("range",[TA_nexp n1;TA_nexp n2])}
let mk_atom n1 = {t = Tapp("atom",[TA_nexp n1])}
let mk_vector typ order start size = {t=Tapp("vector",[TA_nexp start; TA_nexp size; TA_ord order; TA_typ typ])}
let mk_bitwise_op name symb arity =
  let ovar = mk_ovar "o"  in
  let vec_typ = mk_vector bit_t ovar (mk_nv "n") (mk_nv "m") in
  let single_bit_vec_typ = mk_vector bit_t ovar (mk_nv "n") n_one in
  let vec_args = Array.to_list (Array.make arity vec_typ) in
  let single_bit_vec_args = Array.to_list (Array.make arity single_bit_vec_typ) in
  let bit_args = Array.to_list (Array.make arity bit_t) in
  let gen_args = Array.to_list (Array.make arity {t = Tvar "a"}) in
  let svarg,varg,barg,garg = if (arity = 1) 
    then List.hd single_bit_vec_args,List.hd vec_args,List.hd bit_args,List.hd gen_args 
    else mk_tup single_bit_vec_args,mk_tup vec_args,mk_tup bit_args, mk_tup gen_args in
  (symb,
   Overload(lib_tannot ((mk_typ_params ["a"]),mk_pure_fun garg {t=Tvar "a"}) (Some name) [], true,
            [lib_tannot ((mk_nat_params ["n";"m"]@mk_ord_params["o"]), mk_pure_fun varg vec_typ) (Some name) [];
             (*lib_tannot (["n",{k=K_Nat};"o",{k=K_Ord}],mk_pure_fun svarg single_bit_vec_typ) (Some name) [];*)
             lib_tannot ([],mk_pure_fun barg bit_t) (Some (name ^ "_bit")) []]))

let initial_typ_env_list : (string * ((string * tannot) list)) list =
  
  [
   "bitwise logical operators", 
   [
    ("not",
     Base(([], mk_pure_fun bit_t bit_t), External (Some "bitwise_not_bit"), [],pure_e,pure_e,nob));
    mk_bitwise_op "bitwise_not" "~" 1;
    mk_bitwise_op  "bitwise_or" "|" 2;
    mk_bitwise_op  "bitwise_xor" "^" 2;
    mk_bitwise_op  "bitwise_and" "&" 2;
  ];
  "bitwise shifts and rotates",
   [
    ("<<",Base((((mk_nat_params ["n";"m"])@[("ord",{k=K_Ord})]),
                (mk_pure_fun (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"));
                                      (mk_range n_zero (mk_nv "m"))])
                             (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
               External (Some "bitwise_leftshift"),[],pure_e,pure_e,nob));
    (">>",Base((((mk_nat_params ["n";"m"])@[("ord",{k=K_Ord})]),
                (mk_pure_fun (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"));
                                      (mk_range n_zero (mk_nv "m"))])
                             (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
               External (Some "bitwise_rightshift"),[],pure_e,pure_e,nob));
    ("<<<",Base((((mk_nat_params ["n";"m"])@[("ord",{k=K_Ord})]),
                     (mk_pure_fun (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"));
                                           (mk_range n_zero (mk_nv "m"))])
                                  (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
                External (Some "bitwise_rotate"),[],pure_e,pure_e,nob));
  ];
   "bitvector duplicate, extension, and MSB",
   [
    ("^^",
     Overload(
       Base((mk_nat_params["n";"o";"p"]@[("a",{k=K_Typ})],
             (mk_pure_fun (mk_tup [{t=Tvar "a"}; mk_atom (mk_nv "n")])
                (mk_vector bit_t {order = Oinc} (mk_nv "o") (mk_nv "p")))),
            External (Some "duplicate"), [], pure_e, pure_e, nob),
       false,
       [Base((mk_nat_params ["n"],
              (mk_pure_fun (mk_tup [bit_t;mk_atom (mk_nv "n")])
                           (mk_vector bit_t {order=Oinc} (mk_c zero) (mk_nv "n")))),
             External (Some "duplicate"),[],pure_e,pure_e,nob);
        Base((mk_nat_params ["n";"m";"o"]@mk_ord_params["ord"],
              mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "m");
                                   mk_atom (mk_nv "n")])
                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_mult (mk_nv "m") (mk_nv "n")))),
             External (Some "duplicate_bits"),[],pure_e,pure_e,nob);]));
    ("EXTZ",Base((((mk_nat_params ["n";"m";"o";"p"])@["ord",{k=K_Ord}]),
                  (mk_pure_imp (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n"))
                     (mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "m")) "m")),
                 External (Some "extz"),[],pure_e,pure_e,nob));
    ("EXTS",Base((((mk_nat_params ["n";"m";"o";"p"])@["ord",{k=K_Ord}]),
                  (mk_pure_imp (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n"))
                     (mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "m")) "m")),
                 External (Some "exts"),[],pure_e,pure_e,nob));
    ("most_significant", lib_tannot ((mk_nat_params ["n";"m"]@(mk_ord_params ["ord"])),
                                     (mk_pure_fun (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")) bit_t))
                                    None []);
  ];  
   "arithmetic",
   [
    ("+",Overload(
      lib_tannot ((mk_typ_params ["a";"b";"c"]),
                  (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})) (Some "add") [],
      true,
      [lib_tannot ((mk_nat_params ["n";"m"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")])
                                (mk_atom (mk_add (mk_nv "n") (mk_nv "m")))))
                  (Some "add") [];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n"))))
                  (Some "add_vec") [];
       lib_tannot ((mk_nat_params ["n";"o";"p";"q"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_range (mk_nv "q") (mk_2n (mk_nv "n")))))
                  (Some "add_vec_vec_range") [];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "add_vec_range")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require, (mk_nv "o"),mk_sub (mk_2n (mk_nv "m")) n_one)];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n")); bit_t; bit_t])))
                  (Some "add_overflow_vec") [];
       lib_tannot ((mk_nat_params ["n";"m";"o";])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                  (Some "add_vec_range_range")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require,(mk_nv "o"),mk_sub (mk_2n (mk_nv "m")) n_one)];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "add_range_vec")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require,(mk_nv "o"),mk_sub (mk_2n (mk_nv "m")) n_one)];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_sub (mk_2n (mk_nv "m")) n_one)))))
                  (Some "add_range_vec_range")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require,(mk_nv "o"),mk_sub (mk_2n (mk_nv "m")) n_one)];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"); bit_t])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"))))
                   (Some "add_vec_bit") [];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [bit_t; mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"))))
                  (Some "add_bit_vec") [];
      ]));
    ("+_s",Overload(
      lib_tannot ((mk_typ_params ["a";"b";"c"]),
                  (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})) (Some "add") [],
      true,
      [lib_tannot ((mk_nat_params ["n";"m"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")])
                                (mk_atom (mk_add (mk_nv "n") (mk_nv "m")))))
                  (Some "add_signed") [];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                  (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                        mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                               (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n"))))
                  (Some "add_vec_signed") [];
       lib_tannot ((mk_nat_params ["n";"o";"p";"q"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_range (mk_nv "q") (mk_2n (mk_nv "n")))))
                  (Some "add_vec_vec_range_signed") [];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "add_vec_range_signed")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require,(mk_nv "o"),(mk_sub (mk_2n (mk_nv "m")) n_one))];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n")); bit_t; bit_t])))
                  (Some "add_overflow_vec_signed") [];
       lib_tannot ((mk_nat_params ["n";"m";"o";])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                   (Some "add_vec_range_range_signed")
                   [LtEq(Specc(Parse_ast.Int("+",None)),Require, (mk_nv "o"),mk_sub (mk_2n (mk_nv "m")) n_one)];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "add_range_vec_signed")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require,(mk_nv "o"),(mk_sub (mk_2n (mk_nv "m")) n_one))];
       lib_tannot ((mk_nat_params ["n";"m";"o";])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                  (Some "add_range_vec_range_signed")
                  [LtEq(Specc(Parse_ast.Int("+",None)),Require,(mk_nv "o"),(mk_sub (mk_2n (mk_nv "m")) n_one))];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"); bit_t])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"))))
                  (Some "add_vec_bit_signed") [];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"); bit_t])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p")); bit_t; bit_t])))
                  (Some "add_overflow_vec_bit_signed") [];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [bit_t; mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"))))
                  (Some "add_bit_vec_signed") [];
      ]));
    ("-",Overload(
      lib_tannot ((mk_typ_params ["a";"b";"c"]), (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"}))
                 (Some "minus") [],
      true,
      [lib_tannot ((mk_nat_params["n";"m"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")])
                                (mk_atom (mk_sub (mk_nv "n") (mk_nv "m")))))
                  (Some "minus") [];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n"))))
                  (Some "minus_vec") [];
       lib_tannot ((mk_nat_params ["m";"n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_atom (mk_nv "m")))) (Some "minus_vec_vec_range") [];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))) 
                  (Some "minus_vec_range") [];
       lib_tannot ((mk_nat_params ["n";"m";"o";])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                  (Some "minus_vec_range_range") [];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "minus_range_vec") []; 
       lib_tannot ((mk_nat_params ["n";"m";"o";])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                  (Some "minus_range_vec_range") [];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n")); bit_t; bit_t])))
                  (Some "minus_overflow_vec") [];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"); bit_t])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p")); bit_t; bit_t])))
                   (Some "minus_overflow_vec_bit") [];
      ]));
    ("-_s",Overload(
      lib_tannot ((mk_typ_params ["a";"b";"c"]), (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"}))
                 (Some "minus") [],
      true,
      [lib_tannot ((mk_nat_params["n";"m"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")])
                                (mk_atom (mk_sub (mk_nv "n") (mk_nv "m")))))
                  (Some "minus") [];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n"))))
                  (Some "minus_vec_signed") [];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "minus_vec_range_signed") [];
       lib_tannot ((mk_nat_params ["n";"m";"o";])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                         mk_atom (mk_nv "o")])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                  (Some "minus_vec_range_range_signed") [];
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))))
                  (Some "minus_range_vec_signed") []; 
       lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");])
                                (mk_range (mk_nv "o") (mk_add (mk_nv "o") (mk_2n (mk_nv "m"))))))
                  (Some "minus_range_vec_range_signed") [];
       lib_tannot ((mk_nat_params ["n";"o";"p"])@(mk_ord_params ["ord"]),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                         mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n")); bit_t; bit_t])))
                  (Some "minus_overflow_vec_signed") [];
       lib_tannot ((mk_nat_params ["o";"p"]@(mk_ord_params["ord"])),
                   (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p"); bit_t])
                                (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "p")); bit_t; bit_t])))
                  (Some "minus_overflow_vec_bit_signed") [];
      ]));
    ("*",Overload(
      lib_tannot ((mk_typ_params ["a";"b";"c"]),
                  (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]){t=Tvar "c"}))
                 (Some "multiply") [],
      true,
      [lib_tannot ((mk_nat_params["n";"m"]),
                   (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")])
                                (mk_atom (mk_mult (mk_nv "n") (mk_nv "m")))))
                  (Some "multiply") [];
       Base(((mk_nat_params ["n";"o";"p";"q"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                   mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                          (mk_vector bit_t (mk_ovar "ord") (mk_nv "q") (mk_add (mk_nv "n") (mk_nv "n"))))),
            (External (Some "multiply_vec")), [],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"m";"o";"p"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                   mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")])
                          (mk_vector bit_t (mk_ovar "ord") (mk_nv "q") (mk_add (mk_nv "m") (mk_nv "m"))))),
            (External (Some "mult_range_vec")),[],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"m";"o";"p"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                   mk_atom (mk_nv "o")])
                           (mk_vector bit_t (mk_ovar "ord") (mk_nv "q") (mk_add (mk_nv "m") (mk_nv "m"))))),
            (External (Some "mult_vec_range")),[],pure_e,pure_e,nob);
      ]));
    ("*_s",Overload(
      Base(((mk_typ_params ["a";"b";"c"]),
            (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]){t=Tvar "c"})),
           (External (Some "multiply")),[],pure_e,pure_e,nob),
      true,
      [Base(((mk_nat_params["n";"m";]),
             (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")])
                          (mk_atom (mk_mult (mk_nv "n") (mk_nv "m"))))),
            (External (Some "multiply_signed")), [],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"o";"p";"m"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                   mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                          (mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_add (mk_nv "n") (mk_nv "n"))))),
            (External (Some "multiply_vec_signed")), [],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"m";"o";"p"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                   mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")])
                          (mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_add (mk_nv "m") (mk_nv "m"))))),
            (External (Some "mult_range_vec_signed")),[],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"m";"o";"p"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                   mk_atom (mk_nv "o")])
                          (mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_add (mk_nv "m") (mk_nv "m"))))),
            (External (Some "mult_vec_range_signed")),[],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"o";"p";"m"])@(mk_ord_params ["ord"]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                   mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")])
                          (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_add (mk_nv "n") (mk_nv "n")));
                                   bit_t;bit_t]))),
            (External (Some "mult_overflow_vec_signed")), [],pure_e,pure_e,nob);
      ]));
    ("mod",
     Overload(
       Base(((mk_typ_params ["a";"b";"c"]),
             (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})),
            (External (Some "modulo")),[],pure_e,pure_e,nob),
       true,
       [Base(((mk_nat_params["n";"o";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n") ; mk_atom (mk_nv "o")])
                           (mk_range n_zero (mk_sub (mk_nv "o") n_one)))),
             (External (Some "modulo")),
             [GtEq(Specc(Parse_ast.Int("modulo",None)),Require,(mk_nv "o"),n_one)],pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m";"o"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_range n_one (mk_nv "o")])
                           (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
             (External (Some "mod_vec_range")),
             [GtEq(Specc(Parse_ast.Int("mod",None)),Require,(mk_nv "o"),n_one);],pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")])
                 (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
             (External (Some "mod_vec")),[],pure_e,pure_e,nob)]));
    ("mod_s",
     Overload(
       Base(((mk_typ_params ["a";"b";"c"]),
             (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})),
            (External (Some "mod_signed")),[],pure_e,pure_e,nob),
       true,
       [Base(((mk_nat_params["n";"o";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n") ; mk_atom (mk_nv "o")])
                           (mk_range n_zero (mk_sub (mk_nv "o") n_one)))),
             (External (Some "mod_signed")),
             [GtEq(Specc(Parse_ast.Int("modulo",None)),Require,(mk_nv "o"),n_one)],pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m";"o"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_range n_one (mk_nv "o")])
                           (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
             (External (Some "mod_signed_vec_range")),
             [GtEq(Specc(Parse_ast.Int("mod",None)),Require,(mk_nv "o"),n_one);],pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")])
                 (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
             (External (Some "mod_signed_vec")),[],pure_e,pure_e,nob)]));
    ("div",
     Base(((mk_nat_params["n";"m";"o";]),
           (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")])
                        (mk_atom (mk_nv "o")))),
          (*This should really be != to 0, as negative is just fine*)
          (External (Some "quot")),[(*GtEq(Specc(Parse_ast.Int("quot",None)),Require,(mk_nv "m"),n_one);*)
            LtEq(Specc(Parse_ast.Int("quot",None)),Guarantee,
                 (mk_mult (mk_nv "n") (mk_nv "o")),(mk_nv "m"))],
          pure_e,pure_e,nob));
    ("quot",
     Overload(
       Base(((mk_typ_params ["a";"b";"c"]),
             (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})),
            (External (Some "quot")),[],pure_e,pure_e,nob),
       true,
       [Base(((mk_nat_params["n";"m";"o";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")])
                 (mk_atom (mk_nv "o")))),
             (*This should really be != to 0, as negative is just fine*)
             (External (Some "quot")),[(*GtEq(Specc(Parse_ast.Int("quot",None)),Require,(mk_nv "m"),n_one);*)
                                     LtEq(Specc(Parse_ast.Int("quot",None)),Guarantee,
                                          (mk_mult (mk_nv "n") (mk_nv "o")),(mk_nv "m"))],
             pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m";"p";"q"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "q")])
                           (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
             (External (Some "quot_vec")),[GtEq(Specc(Parse_ast.Int("quot",None)),Require, mk_nv "m", mk_nv "q")],
             pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m";"p";"q"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "q")])
                           (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")); bit_t;bit_t]))),
             (External (Some "quot_overflow_vec")),
             [GtEq(Specc(Parse_ast.Int("quot",None)),Require, mk_nv "m", mk_nv "q")],
             pure_e,pure_e,nob)]));
    ("quot_s",
     Overload(
       Base(((mk_typ_params ["a";"b";"c"]), (mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) {t=Tvar "c"})),
            (External (Some "quot_signed")),[],pure_e,pure_e,nob),
       true,
       [Base(((mk_nat_params["n";"m";"o";"p";"q";"r"]),
              (mk_pure_fun (mk_tup [mk_range (mk_nv "n") (mk_nv "m"); mk_range (mk_nv "o") (mk_nv "p")])
                           (mk_range (mk_nv "q") (mk_nv "r")))),
             (External (Some "quot_signed")),
             [(*GtEq(Specc(Parse_ast.Int("quot",None)),Require,(mk_nv "o"),n_one);*)
              LtEq(Specc(Parse_ast.Int("quot",None)),Guarantee,(mk_mult (mk_nv "p") (mk_nv "r")),mk_nv "m")],
             pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m";"p";"q"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "q")])
                           (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")))),
             (External (Some "quot_vec_signed")),
             [GtEq(Specc(Parse_ast.Int("quot",None)),Require, mk_nv "m", mk_nv "q")],pure_e,pure_e,nob);
        Base(((mk_nat_params["n";"m";"p";"q"])@(mk_ord_params["ord"]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "q")])
                           (mk_tup [(mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")); bit_t;bit_t]))),
             (External (Some "quot_overflow_vec_signed")),
             [GtEq(Specc(Parse_ast.Int("quot",None)),Require, mk_nv "m", mk_nv "q")],pure_e,pure_e,nob);
       ]));
  ];
   "additional arithmetic on singleton ranges; vector length",
   [
    ("**",
     Base(((mk_nat_params ["o"]),
           (mk_pure_fun (mk_tup [(mk_atom n_two); (mk_atom (mk_nv "o"))])
                        (mk_atom (mk_2n (mk_nv "o"))))),
          (External (Some "power")), [],pure_e,pure_e,nob));

    ("abs",Base(((mk_nat_params ["n";"m";]),
                 (mk_pure_fun (mk_atom (mk_nv "n")) (mk_range n_zero (mk_nv "m")))),
                External (Some "abs"),[],pure_e,pure_e,nob));
    ("max",
     Base(((mk_nat_params ["n";"m";"o"]),
           (mk_pure_fun (mk_tup [(mk_atom (mk_nv "n"));(mk_atom (mk_nv "m"))])
                        (mk_atom (mk_nv "o")))),
          External (Some "max"),[],pure_e,pure_e,nob));
    ("min",
     Base(((mk_nat_params ["n";"m";"o"]),
           (mk_pure_fun (mk_tup [(mk_atom (mk_nv "n"));(mk_atom (mk_nv "m"))])
                        (mk_atom (mk_nv "o")))),
          External (Some "min"),[],pure_e,pure_e,nob));
    ("length", Base((["a",{k=K_Typ}]@(mk_nat_params["n";"m"])@(mk_ord_params["ord"]),
                     (mk_pure_fun (mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))
                                  (mk_atom (mk_nv "m")))),
                    (External (Some "length")),[],pure_e,pure_e,nob));
  ];

   "comparisons",
   [
    (*Correct types again*)
    ("==",
     Overload(
       (lib_tannot (mk_typ_params ["a";"b"],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t))
         (Some "eq") []),
       false,
       [(*== : 'a['m] * 'a['m] -> bit_t *)
         lib_tannot ((mk_nat_params["n";"m";"o"]@mk_typ_params["a"]@mk_ord_params["ord"]),
                    (mk_pure_fun (mk_tup [mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                          mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "o") (mk_nv "m")])
                       bit_t))
                   (Some "eq_vec")
                   [];
        (* == : bit['n] * [:'o:] -> bit_t *)
        lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                    (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                          mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")])
                                 bit_t))
                   (Some "eq_range_vec")
                   [];
        (* == : [:'o:] * bit['n] -> bit_t *)
        lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                    (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                          mk_atom (mk_nv "o")])
                                  bit_t))
                   (Some "eq_vec_range")
                   [];
        (* == : [:'n:] * [:'m:] -> bit_t *)
        lib_tannot ((mk_nat_params["n";"m";],
                     mk_pure_fun (mk_tup [mk_atom (mk_nv "n") ;mk_atom (mk_nv "m")]) bit_t))
                   (Some "eq_range")
                   [Predicate(Specc(Parse_ast.Int("==",None)),
                              Eq(Specc(Parse_ast.Int("==",None)), mk_nv "n", mk_nv "m"),
                              NtEq(Specc(Parse_ast.Int("==",None)), mk_nv "n", mk_nv "m"))];
        (* == : (bit_t,bit_t) -> bit_t *)
        lib_tannot ([], mk_pure_fun (mk_tup [bit_t;bit_t]) bit_t)
                   (Some "eq_bit")
                   [];
        lib_tannot (["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t))
                   (Some "eq") []]));
    ("!=",
     Overload(
       lib_tannot ((mk_typ_params ["a";"b"]),(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t))
         (Some "neq") [],
       false,
       [(*!= : 'a['m] * 'a['m] -> bit_t *)
         lib_tannot ((mk_nat_params["n";"m";"o"]@mk_typ_params["a"]@mk_ord_params["ord"]),
                    (mk_pure_fun (mk_tup [mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                          mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "o") (mk_nv "m")])
                       bit_t))
                   (Some "neq_vec")
                   [];
        (* != : bit['n] * [:'o:] -> bit_t *)
        lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                    (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                          mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")])
                                 bit_t))
                   (Some "neq_range_vec")
                   [];
        (* != : [:'o:] * bit['n] -> bit_t *)
        lib_tannot ((mk_nat_params ["n";"m";"o"])@(mk_ord_params ["ord"]),
                    (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                          mk_atom (mk_nv "o")])
                                  bit_t))
                   (Some "neq_vec_range")
                   [];
        (* != : [:'n:] * [:'m:] -> bit_t *)
        lib_tannot ((mk_nat_params["n";"m";],
                     mk_pure_fun (mk_tup [mk_atom (mk_nv "n") ;mk_atom (mk_nv "m")]) bit_t))
                   (Some "neq_range")
                   [Predicate(Specc(Parse_ast.Int("!=",None)),
                              Eq(Specc(Parse_ast.Int("!=",None)), mk_nv "n", mk_nv "m"),
                              NtEq(Specc(Parse_ast.Int("!=",None)), mk_nv "n", mk_nv "m"))];
        (* != : (bit_t,bit_t) -> bit_t *)
        lib_tannot ([], mk_pure_fun (mk_tup [bit_t;bit_t]) bit_t)
                   (Some "neq_bit")
                   [];
        lib_tannot (["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t))
                   (Some "neq") []]));
    ("<",
     Overload(
       Base((["a",{k=K_Typ};"b",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t)),
            (External (Some "lt")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n"; "m";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n") ;mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "lt")),
             [Predicate(Specc(Parse_ast.Int("<",None)),
                        Lt(Specc(Parse_ast.Int("<",None)),Guarantee, mk_nv "n", mk_nv "m"),
                        GtEq(Specc(Parse_ast.Int("<",None)),Guarantee, mk_nv "n", mk_nv "m"))],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)),
             (External (Some "lt_vec")),[],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"m";"o"]@["ord",{k=K_Ord}]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                   mk_atom (mk_nv "o")]) bit_t)),
            (External (Some "lt_vec_range")), [], pure_e,pure_e, nob);
       ]));
    ("<_u",
     Overload(
       Base((["a",{k=K_Typ};"b",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t)),
            (External (Some "lt")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n"; "m";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "lt_unsigned")),
             [Predicate(Specc(Parse_ast.Int("<",None)),
                        Lt(Specc(Parse_ast.Int("<_u",None)),Guarantee, mk_nv "n", mk_nv "m"),
                        GtEq(Specc(Parse_ast.Int("<_u",None)),Guarantee, mk_nv "n", mk_nv "m"))],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)),
             (External (Some "lt_vec_unsigned")),[],pure_e,pure_e,nob);
       ]));
    ("<_s",
     Overload(
       Base((["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t)),
            (External (Some "lt")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n"; "m";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "lt_signed")),
             [Predicate(Specc(Parse_ast.Int("<_s",None)),
                        Lt(Specc(Parse_ast.Int("<_s",None)),Guarantee, mk_nv "n", mk_nv "m"),
                        GtEq(Specc(Parse_ast.Int("<_s",None)),Guarantee, mk_nv "n", mk_nv "m"))],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)),
             (External (Some "lt_vec_signed")),[],pure_e,pure_e,nob);
       ]));
    (">",
     Overload(
       Base((["a",{k=K_Typ};"b",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t)),
            (External (Some "gt")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n";"m"]), 
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n"); mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "gt")),
             [Predicate(Specc(Parse_ast.Int(">",None)),
                        Gt(Specc(Parse_ast.Int(">",None)),Guarantee, mk_nv "n", mk_nv "m"),
                        LtEq(Specc(Parse_ast.Int(">",None)),Guarantee, mk_nv "n", mk_nv "m"))],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@[("ord",{k=K_Ord})]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)), 
             (External (Some "gt_vec")),[],pure_e,pure_e,nob);
       Base(((mk_nat_params ["n";"m";"o";]@["ord",{k=K_Ord}]),
             (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                   mk_atom (mk_nv "o")]) bit_t)),
            (External (Some "gt_vec_range")), [], pure_e,pure_e, nob);
       ]));
    (">_u",
     Overload(
       Base((["a",{k=K_Typ};"b",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t)),
            (External (Some "gt")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n";"m";]), 
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "gt_unsigned")),
             [Predicate(Specc(Parse_ast.Int(">_u",None)),
                        Gt(Specc(Parse_ast.Int(">_u",None)),Guarantee, mk_nv "n", mk_nv "m"),
                        LtEq(Specc(Parse_ast.Int(">_u",None)),Guarantee, mk_nv "n", mk_nv "n"))],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@[("ord",{k=K_Ord})]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)), 
             (External (Some "gt_vec_unsigned")),[],pure_e,pure_e,nob);
       ]));
    (">_s",
     Overload(
       Base((["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t)),
            (External (Some "gt")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n";"m";]), 
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "gt_signed")),
             [Predicate(Specc(Parse_ast.Int(">_s",None)),
                        Gt(Specc(Parse_ast.Int(">_s",None)),Guarantee, mk_nv "n", mk_nv "m"),
                        LtEq(Specc(Parse_ast.Int(">_s",None)),Guarantee, mk_nv "m", mk_nv "m"))],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@[("ord",{k=K_Ord})]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)), 
             (External (Some "gt_vec_signed")),[],pure_e,pure_e,nob);
       ]));
    ("<=",
     Overload(
       Base((["a",{k=K_Typ};"b",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "b"}]) bit_t)),
            (External (Some "lteq")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n"; "m";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "lteq")),
             [Predicate(Specc(Parse_ast.Int("<=",None)),
                        LtEq(Specc(Parse_ast.Int("<=",None)),Guarantee,mk_nv "n",mk_nv "m"),
                        Gt(Specc(Parse_ast.Int("<=",None)),Guarantee,mk_nv "n",mk_nv "m"))],
             pure_e,pure_e,nob);
        Base(((mk_nat_params ["n";"m";"o";]@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_atom (mk_nv "o")]) bit_t)),
             (External (Some "lteq_vec_range")), [], pure_e,pure_e, nob);
        Base(((mk_nat_params ["n";"m";"o";]@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")]) bit_t)),
             (External (Some "lteq_range_vec")), [], pure_e,pure_e, nob);
        Base((((mk_nat_params ["n";"o";"p"])@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)),
             (External (Some "lteq_vec")),[],pure_e,pure_e,nob);
       ]));
    ("<=_s",
     Overload(
       Base((["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t)),
            (External (Some "lteq")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n"; "m";]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "n");mk_atom (mk_nv "m")]) bit_t)),
             (External (Some "lteq_signed")),
             [LtEq(Specc(Parse_ast.Int("<=",None)),Guarantee,mk_nv "n",mk_nv "o");
              LtEq(Specc(Parse_ast.Int("<=",None)),Guarantee,mk_nv "m",mk_nv "p")],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)),
             (External (Some "lteq_vec_signed")),[],pure_e,pure_e,nob);
       ]));
    (">=",
     Overload(
       Base((["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t)),
            (External (Some "gteq")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n";"m";"o";"p"]), 
              (mk_pure_fun (mk_tup [mk_range (mk_nv "n") (mk_nv "m");mk_range (mk_nv "o") (mk_nv "p")]) bit_t)),
             (External (Some "gteq")),
             [GtEq(Specc(Parse_ast.Int(">=",None)),Guarantee, mk_nv "n", mk_nv "o");
              GtEq(Specc(Parse_ast.Int(">=",None)),Guarantee, mk_nv "m", mk_nv "p")],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@[("ord",{k=K_Ord})]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)), 
             (External (Some "gteq_vec")),[],pure_e,pure_e,nob);
        Base(((mk_nat_params ["n";"m";"o";]@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m");
                                    mk_atom (mk_nv "o")]) bit_t)),
             (External (Some "gteq_vec_range")), [], pure_e,pure_e, nob);
        Base(((mk_nat_params ["n";"m";"o";]@["ord",{k=K_Ord}]),
              (mk_pure_fun (mk_tup [mk_atom (mk_nv "o");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m")]) bit_t)),
             (External (Some "gteq_range_vec")), [], pure_e,pure_e, nob);
       ]));
    (">=_s",
     Overload(
       Base((["a",{k=K_Typ}],(mk_pure_fun (mk_tup [{t=Tvar "a"};{t=Tvar "a"}]) bit_t)),
            (External (Some "gteq")),[],pure_e,pure_e,nob),
       false,
       [Base(((mk_nat_params ["n";"m";"o";"p"]), 
              (mk_pure_fun (mk_tup [mk_range (mk_nv "n") (mk_nv "m");mk_range (mk_nv "o") (mk_nv "p")]) bit_t)),
             (External (Some "gteq_signed")),
             [GtEq(Specc(Parse_ast.Int(">=_s",None)),Guarantee, mk_nv "n", mk_nv "o");
              GtEq(Specc(Parse_ast.Int(">=_s",None)),Guarantee, mk_nv "m", mk_nv "p")],
             pure_e,pure_e,nob);
        Base((((mk_nat_params ["n";"o";"p"])@[("ord",{k=K_Ord})]),
              (mk_pure_fun (mk_tup [mk_vector bit_t (mk_ovar "ord") (mk_nv "o") (mk_nv "n");
                                    mk_vector bit_t (mk_ovar "ord") (mk_nv "p") (mk_nv "n")]) bit_t)), 
             (External (Some "gteq_vec_signed")),[],pure_e,pure_e,nob);
       ]));
  ];

(** ? *)
  "oddments",
   [
    ("is_one",Base(([],(mk_pure_fun bit_t bit_t)),(External (Some "is_one")),[],pure_e,pure_e,nob));
    ("signed",Base((mk_nat_params["n";"m";"o"]@[("ord",{k=K_Ord})],
                    (mk_pure_fun (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))
                                 (mk_atom (mk_nv "o")))),
                   External (Some "signed"), 
                  [(GtEq(Specc(Parse_ast.Int("signed",None)),Guarantee, 
                         mk_nv "o", mk_neg(mk_2n (mk_nv "m"))));
                   (LtEq(Specc(Parse_ast.Int("signed",None)),Guarantee,
                         mk_nv "o", mk_sub (mk_2n (mk_nv "m")) n_one));],pure_e,pure_e,nob));
    ("unsigned",Base((mk_nat_params["n";"m";"o"]@[("ord",{k=K_Ord})],
                    (mk_pure_fun (mk_vector bit_t (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))
                                 (mk_atom (mk_nv "o")))),
                   External (Some "unsigned"), 
                  [(GtEq(Specc(Parse_ast.Int("unsigned",None)),Guarantee, 
                         mk_nv "o", n_zero));
                   (LtEq(Specc(Parse_ast.Int("unsigned",None)),Guarantee,
                         mk_nv "o", mk_sub (mk_2n (mk_nv "m")) n_one));],pure_e,pure_e,nob));

    ("ignore",lib_tannot ([("a",{k=K_Typ})],mk_pure_fun {t=Tvar "a"} unit_t) None []);

    (* incorrect types for typechecking processed sail code; do we care? *)
    ("mask",Base(((mk_typ_params ["a"])@(mk_nat_params["n";"m";"o";"p"])@(mk_ord_params["ord"]),
                  (mk_pure_imp (mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "n") (mk_nv "m"))
                               (mk_vector {t=Tvar "a"} (mk_ovar "ord") (mk_nv "p") (mk_nv "o")) "o")),
                 (External (Some "mask")),
                 [GtEq(Specc(Parse_ast.Int("mask",None)),Guarantee, (mk_nv "m"), (mk_nv "o"))],pure_e,pure_e,nob));
    (*TODO These should be IP_start *)
    ("to_vec_inc",Base(([("a",{k=K_Typ})],{t=Tfn(nat_typ,{t=Tvar "a"},IP_none,pure_e)}),
                       (External None),[],pure_e,pure_e,nob));
    ("to_vec_dec",Base(([("a",{k=K_Typ})],{t=Tfn(nat_typ,{t=Tvar "a"},IP_none,pure_e)}),
                       (External None),[],pure_e,pure_e,nob));
 ];


"option type constructors", 
   [
    ("Some", Base((["a",{k=K_Typ}], mk_pure_fun {t=Tvar "a"} {t=Tapp("option", [TA_typ {t=Tvar "a"}])}),
                  Constructor 2,[],pure_e,pure_e,nob));
    ("None", Base((["a", {k=K_Typ}], mk_pure_fun unit_t {t=Tapp("option", [TA_typ {t=Tvar "a"}])}),
                  Constructor 2,[],pure_e,pure_e,nob));
  ];

"list operations",
 [
    ("append",
     lib_tannot
       (["a",{k=K_Typ}], mk_pure_fun (mk_tup [{t=Tapp("list", [TA_typ {t=Tvar "a"}])};
                                              {t=Tapp("list", [TA_typ {t=Tvar "a"}])}])
          {t=Tapp("list",[TA_typ {t=Tvar "a"}])})
       None []);                                                                                  
 ];

]


let initial_typ_env : tannot Envmap.t =
  Envmap.from_list (List.flatten (List.map snd initial_typ_env_list))

    

let rec typ_subst s_env leave_imp t =
  match t.t with
  | Tvar i -> (match Envmap.apply s_env i with
               | Some(TA_typ t1) -> t1
               | _ -> { t = Tvar i})
  | Tuvar _  -> new_t()
  | Tid i -> { t = Tid i}
  | Tfn(t1,t2,imp,e) -> 
    {t =Tfn((typ_subst s_env false t1),(typ_subst s_env false t2),(ip_subst s_env leave_imp imp),(e_subst s_env e)) }
  | Ttup(ts) -> { t= Ttup(List.map (typ_subst s_env leave_imp) ts) }
  | Tapp(i,args) -> {t= Tapp(i,List.map (ta_subst s_env leave_imp) args)}
  | Tabbrev(ti,ta) -> {t = Tabbrev(typ_subst s_env leave_imp ti,typ_subst s_env leave_imp ta) }
  | Toptions(t1,None) -> {t = Toptions(typ_subst s_env leave_imp t1,None)}
  | Toptions(t1,Some t2) -> {t = Toptions(typ_subst s_env leave_imp t1,Some (typ_subst s_env leave_imp t2)) }
and ip_subst s_env leave_imp ip =
  let leave_nu = if leave_imp then leave_nuvar else (fun i -> i) in
  match ip with
    | IP_none -> ip
    | IP_length n -> IP_length (leave_nu (n_subst s_env n))
    | IP_start n -> IP_start (leave_nu (n_subst s_env n))
    | IP_user n -> IP_user (leave_nu (n_subst s_env n))
and ta_subst s_env leave_imp ta =
  match ta with
  | TA_typ t -> TA_typ (typ_subst s_env leave_imp t)
  | TA_nexp n -> TA_nexp (n_subst s_env n)
  | TA_eft e -> TA_eft (e_subst s_env e)
  | TA_ord o -> TA_ord (o_subst s_env o)
and n_subst s_env n =
  match n.nexp with
  | Nvar i -> 
    (match Envmap.apply s_env i with
      | Some(TA_nexp n1) -> n1
      | _ -> mk_nv i)
  | Nid(i,n) -> n_subst s_env n
  | Nuvar _ -> new_n()
  | Nconst _ | Npos_inf | Nneg_inf | Ninexact -> n
  | N2n(n1,None) -> mk_2n (n_subst s_env n1) 
  | N2n(n1,Some(i)) -> mk_2nc (n_subst s_env n1) i
  | Npow(n1,i) -> mk_pow (n_subst s_env n1) i
  | Nneg n1 -> mk_neg (n_subst s_env n1)
  | Nadd(n1,n2) -> mk_add (n_subst s_env n1) (n_subst s_env n2)
  | Nsub(n1,n2) -> mk_sub (n_subst s_env n1) (n_subst s_env n2)
  | Nmult(n1,n2) -> mk_mult(n_subst s_env n1) (n_subst s_env n2)
and o_subst s_env o =
  match o.order with
  | Ovar i -> (match Envmap.apply s_env i with
               | Some(TA_ord o1) -> o1
               | _ -> { order = Ovar i })
  | Ouvar _ -> new_o ()
  | _ -> o
and e_subst s_env e =
  match e.effect with
  | Evar i -> (match Envmap.apply s_env i with
               | Some(TA_eft e1) -> e1
               | _ -> {effect = Evar i})
  | Euvar _ -> new_e ()
  | _ -> e

let rec cs_subst t_env cs =
  match cs with
    | [] -> []
    | Eq(l,n1,n2)::cs -> Eq(l,n_subst t_env n1,n_subst t_env n2)::(cs_subst t_env cs)
    | NtEq(l,n1,n2)::cs -> NtEq(l, n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | GtEq(l,enforce,n1,n2)::cs -> GtEq(l,enforce,n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | Gt(l,enforce,n1,n2)::cs -> Gt(l,enforce,n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | LtEq(l,enforce,n1,n2)::cs -> LtEq(l,enforce,n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | Lt(l,enforce,n1,n2)::cs -> Lt(l,enforce,n_subst t_env n1, n_subst t_env n2)::(cs_subst t_env cs)
    | In(l,s,ns)::cs -> 
      let nexp = n_subst t_env (mk_nv s) in
      (match nexp.nexp with
      | Nuvar urec -> urec.nin <- true
      | _ -> ()); 
      InS(l,nexp,ns)::(cs_subst t_env cs)
    | InS(l,n,ns)::cs -> InS(l,n_subst t_env n,ns)::(cs_subst t_env cs)
    | Predicate(l, cp,cn)::cs -> 
      Predicate(l, List.hd(cs_subst t_env [cp]), List.hd(cs_subst t_env [cn]))::(cs_subst t_env cs)
    | CondCons(l,kind,_,cs_p,cs_e)::cs -> 
      CondCons(l,kind,None,cs_subst t_env cs_p,cs_subst t_env cs_e)::(cs_subst t_env cs)
    | BranchCons(l,_,bs)::cs -> BranchCons(l,None,cs_subst t_env bs)::(cs_subst t_env cs)

let subst_with_env env leave_imp t cs e =
  (typ_subst env leave_imp t, cs_subst env cs, e_subst env e, env)

let subst_n_with_env = n_subst 

let subst (k_env : (Envmap.k * kind) list) (leave_imp:bool) (use_var:bool)
          (t : t) (cs : nexp_range list) (e : effect) : (t * nexp_range list * effect * t_arg emap) =
  let subst_env = Envmap.from_list
    (List.map (fun (id,k) -> (id, 
                              match k.k with
                              | K_Typ -> TA_typ (if use_var then (new_tv id) else (new_t ()))
                              | K_Nat -> TA_nexp (if use_var then (new_nv id) else (new_n ()))
                              | K_Ord -> TA_ord (new_o ())
                              | K_Efct -> TA_eft (new_e ())
                              | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown
                                              "substitution given an environment with a non-base-kind kind"))) k_env) 
  in
  subst_with_env subst_env leave_imp t cs e

let rec typ_param_eq l spec_param fun_param = 
  match (spec_param,fun_param) with
    | ([],[]) -> []
    | (_,[]) -> 
      raise (Reporting_basic.err_typ l "Specification type variables and function definition variables must match")
    | ([],_) -> 
      raise
        (Reporting_basic.err_typ l "Function definition declares more type variables than specification variables")
    | ((ids,tas)::spec_param,(idf,taf)::fun_param) ->
      if ids=idf
      then match (tas,taf) with
        | (TA_typ tas_t,TA_typ taf_t) -> (equate_t tas_t taf_t); typ_param_eq l spec_param fun_param
        | (TA_nexp tas_n, TA_nexp taf_n) -> Eq((Specc l),tas_n,taf_n)::typ_param_eq l spec_param fun_param
        | (TA_ord tas_o,TA_ord taf_o) -> (equate_o tas_o taf_o); typ_param_eq l spec_param fun_param
        | (TA_eft tas_e,TA_eft taf_e) -> (equate_e tas_e taf_e); typ_param_eq l spec_param fun_param
        | _ -> 
          raise (Reporting_basic.err_typ l 
                   ("Specification and function definition have different kinds for variable " ^ ids))
      else raise (Reporting_basic.err_typ l 
                    ("Specification type variables must match in order and number the function definition type variables, stopped matching at " ^ ids ^ " and " ^ idf))

let type_param_consistent l spec_param fun_param =
  let specs = Envmap.to_list spec_param in
  let funs = Envmap.to_list fun_param in
  match specs,funs with
    | [],[] | _,[] -> []
    | _ -> typ_param_eq l specs funs

let rec t_remove_unifications s_env t =
  match t.t with
  | Tvar _ | Tid _-> s_env
  | Tuvar tu -> 
    (match tu.subst with
      | None ->
        (match fresh_tvar s_env t with
          | Some ks -> Envmap.insert s_env ks
          | None -> s_env)
      | _ -> ignore(resolve_tsubst t); s_env)
  | Tfn(t1,t2,_,e) -> e_remove_unifications (t_remove_unifications (t_remove_unifications s_env t1) t2) e
  | Ttup(ts) -> List.fold_right (fun t s_env -> t_remove_unifications s_env t) ts s_env
  | Tapp(i,args) -> List.fold_left (fun s_env t -> ta_remove_unifications s_env t) s_env args
  | Tabbrev(ti,ta) -> (t_remove_unifications (t_remove_unifications s_env ti) ta)
  | Toptions(t1,t2) -> assert false (*This should really be removed by this point*)
and ta_remove_unifications s_env ta =
  match ta with
  | TA_typ t -> (t_remove_unifications s_env t)
  | TA_nexp n -> (n_remove_unifications s_env n)
  | TA_eft e -> (e_remove_unifications s_env e)
  | TA_ord o -> (o_remove_unifications s_env o)
and n_remove_unifications s_env n =
  (*let _ = Printf.eprintf "n_remove_unifications %s\n" (n_to_string n) in*)
  match n.nexp with
  | Nvar _ | Nid _ | Nconst _ | Npos_inf | Nneg_inf | Ninexact -> s_env
  | Nuvar _ ->
    let _ = collapse_nuvar_chain (get_outer_most n) in
    (*let _ = Printf.eprintf "nuvar is before turning into var %s\n" (n_to_string n) in*)
    (match fresh_nvar s_env n with
     | Some ks -> Envmap.insert s_env ks
     | None -> s_env)
  | N2n(n1,_) | Npow(n1,_) | Nneg n1 -> (n_remove_unifications s_env n1)
  | Nadd(n1,n2) | Nsub(n1,n2) | Nmult(n1,n2) -> (n_remove_unifications (n_remove_unifications s_env n1) n2)
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
        

let remove_internal_unifications s_env =
  let rec rem remove s_env u_list = match u_list with
    | [] -> s_env
    | i::u_list -> rem remove (remove s_env i) u_list
  in
  (rem e_remove_unifications
     (rem o_remove_unifications 
        (rem n_remove_unifications 
           (rem t_remove_unifications s_env !tuvars)
           !nuvars)
        !ouvars)
     !euvars)
      
let rec t_to_typ t =
  match t.t with
    | Tid i -> Typ_aux(Typ_id (Id_aux((Id i), Parse_ast.Unknown)),Parse_ast.Unknown)
    | Tvar i -> Typ_aux(Typ_var (Kid_aux((Var i),Parse_ast.Unknown)),Parse_ast.Unknown) 
    | Tfn(t1,t2,_,e) -> Typ_aux(Typ_fn (t_to_typ t1, t_to_typ t2, e_to_ef e),Parse_ast.Unknown)
    | Ttup ts -> Typ_aux(Typ_tup(List.map t_to_typ ts),Parse_ast.Unknown)
    | Tapp(i,args) ->
      Typ_aux(Typ_app(Id_aux((Id i), Parse_ast.Unknown),List.map targ_to_typ_arg args),Parse_ast.Unknown)
    | Tabbrev(t,_) -> t_to_typ t
    | Tuvar _ | Toptions _ -> Typ_aux(Typ_var (Kid_aux((Var "fresh"),Parse_ast.Unknown)),Parse_ast.Unknown)
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
     | Nid(i,_) -> Nexp_id (Id_aux ((Id i),Parse_ast.Unknown))
     | Nvar i -> Nexp_var (Kid_aux((Var i),Parse_ast.Unknown)) 
     | Nconst i -> Nexp_constant (int_of_big_int i) (*TODO: Push more bigint around*) 
     | Npos_inf -> Nexp_constant max_int (*TODO: Not right*)
     | Nneg_inf -> Nexp_constant min_int (* see above *)
     | Ninexact -> Nexp_constant min_int (*and above*)
     | Nmult(n1,n2) -> Nexp_times(n_to_nexp n1,n_to_nexp n2) 
     | Nadd(n1,n2) -> Nexp_sum(n_to_nexp n1,n_to_nexp n2) 
     | Nsub(n1,n2) -> Nexp_minus(n_to_nexp n1,n_to_nexp n2)
     | N2n(n,_) -> Nexp_exp (n_to_nexp n)
     | Npow(n,1) -> let Nexp_aux(n',_) = n_to_nexp n in n'
     | Npow(n,i) -> Nexp_times(n_to_nexp n,n_to_nexp( mk_pow n (i-1))) 
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
        | Some(Base((params,ta),tag,cs,efct,_,_)) ->
          let ta,cs,_,_ = subst params false false ta cs efct in
          let ta,cs' = get_abbrev d_env ta in
          (match ta.t with
          | Tabbrev(t',ta) -> ({t=Tabbrev({t=Tabbrev(t,t')},ta)},cs@cs')
          | _ -> ({t = Tabbrev(t,ta)},cs))
        | _ -> t,[])
    | Tapp(i,args) ->
      (match Envmap.apply d_env.abbrevs i with
        | Some(Base((params,ta),tag,cs,efct,_,_)) ->
          let env = Envmap.from_list2 (List.map fst params) args in
          let ta,cs' = get_abbrev d_env (typ_subst env false ta) in
          (match ta.t with
          | Tabbrev(t',ta) -> ({t=Tabbrev({t=Tabbrev(t,t')},ta)},cs_subst env (cs@cs'))
          | _ -> ({t = Tabbrev(t,ta)},cs_subst env cs))
        | _ -> t,[])
    | _ -> t,[]

let is_enum_typ d_env t = 
  let t,_ = get_abbrev d_env t in
  let t_actual = match t.t with | Tabbrev(_,ta) -> ta | _ -> t in
  match t_actual.t with
    | Tid i -> (match Envmap.apply d_env.enum_env i with
        | Some(ns) -> Some(List.length ns)
        | _ -> None)
    | _ -> None

let eq_error l msg = raise (Reporting_basic.err_typ l msg)
let multi_constraint_error l1 l2 msg = raise (Reporting_basic.err_typ_dual (get_c_loc l1) (get_c_loc l2) msg)

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
  | (BE_rmemt,BE_rmemt) -> 0
  | (BE_rmemt,_) -> -1
  | (_,BE_rmemt) -> 1
  | (BE_wmem,BE_wmem) -> 0
  | (BE_wmem,_) -> -1
  | (_,BE_wmem) -> 1
  | (BE_wmv,BE_wmv) -> 0
  | (BE_wmv, _ ) -> -1
  | (_,BE_wmv) -> 1
  | (BE_wmvt,BE_wmvt) -> 0
  | (BE_wmvt, _ ) -> -1
  | (_,BE_wmvt) -> 1
  | (BE_eamem,BE_eamem) -> 0
  | (BE_eamem,_) -> -1
  | (_,BE_eamem) -> 1
  | (BE_exmem,BE_exmem) -> 0
  | (BE_exmem,_) -> -1
  | (_,BE_exmem) -> 1
  | (BE_barr,BE_barr) -> 0
  | (BE_barr,_) -> 1
  | (_,BE_barr) -> -1
  | (BE_undef,BE_undef) -> 0
  | (BE_undef,_) -> -1
  | (_,BE_undef) -> 1
  | (BE_unspec,BE_unspec) -> 0
  | (BE_unspec,_) -> -1
  | (_,BE_unspec) -> 1
  | (BE_nondet,BE_nondet) -> 0
  | (BE_nondet,_) -> -1
  | (_,BE_nondet) -> 1
  | (BE_depend,BE_depend) -> 0
  | (BE_depend,_) -> -1
  | (_,BE_depend) -> 1
  | (BE_lset,BE_lset) -> 0
  | (BE_lset,_) -> -1
  | (_,BE_lset) -> 1
  | (BE_lret,BE_lret) -> 0
  | (BE_lret,_) -> -1
  | (_, BE_lret) -> 1
  | (BE_escape,BE_escape) -> 0

let effect_sort = List.sort compare_effect

let eq_be_effect (BE_aux (e1,_)) (BE_aux(e2,_)) = e1 = e2

(* Check that o1 is or can be eqaul to o2. 
   In the event that one is polymorphic, inc or dec can be used polymorphically but 'a cannot be used as inc or dec *)
let order_eq co o1 o2 = 
  let l = get_c_loc co in
  match (o1.order,o2.order) with 
  | (Oinc,Oinc) | (Odec,Odec) | (Oinc,Ovar _) | (Odec,Ovar _) -> o2
  | (Ouvar i,_) -> equate_o o1 o2; o2
  | (_,Ouvar i) -> equate_o o2 o1; o2
  | (Ovar v1,Ovar v2) -> if v1=v2 then o2 
    else eq_error l ("Order variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | (Oinc,Odec) | (Odec,Oinc) -> eq_error l "Order mismatch of inc and dec"
  | (Ovar v1,Oinc) -> eq_error l ("Polymorphic order " ^ v1 ^ " cannot be used where inc is expected")
  | (Ovar v1,Odec) -> eq_error l ("Polymorhpic order " ^ v1 ^ " cannot be used where dec is expected")

let rec remove_internal_effects = function
  | [] -> []
  | (BE_aux((BE_lset | BE_lret),_))::effects -> remove_internal_effects effects
  | b::effects -> b::(remove_internal_effects effects)

let has_effect searched_for eff =
  match eff.effect with
    | Eset es ->
      List.exists (eq_be_effect searched_for) es
    | _ -> false

let has_rreg_effect = has_effect (BE_aux(BE_rreg, Parse_ast.Unknown))
let has_wreg_effect = has_effect (BE_aux(BE_wreg, Parse_ast.Unknown))
let has_rmem_effect = has_effect (BE_aux(BE_rmem, Parse_ast.Unknown))
let has_rmemt_effect = has_effect (BE_aux(BE_rmemt, Parse_ast.Unknown))
let has_wmem_effect = has_effect (BE_aux(BE_wmem, Parse_ast.Unknown))
let has_eamem_effect = has_effect (BE_aux(BE_eamem, Parse_ast.Unknown))
let has_exmem_effect = has_effect (BE_aux(BE_exmem, Parse_ast.Unknown))
let has_memv_effect = has_effect (BE_aux(BE_wmv, Parse_ast.Unknown))
let has_memvt_effect = has_effect (BE_aux(BE_wmvt, Parse_ast.Unknown))
let has_lret_effect = has_effect (BE_aux(BE_lret, Parse_ast.Unknown))

(*Similarly to above.*)
let effects_eq co e1 e2 =
  let l = get_c_loc co in
  match e1.effect,e2.effect with
  | Eset _ , Evar _ -> e2
  | Euvar i,_ -> equate_e e1 e2; e2
  | _,Euvar i -> equate_e e2 e1; e2
  | Eset es1,Eset es2 ->
    let es1, es2 = remove_internal_effects es1, remove_internal_effects es2 in
    if (List.length es1) = (List.length es2) && (List.for_all2 eq_be_effect (effect_sort es1) (effect_sort es2) ) 
    then e2 
    else eq_error l ("Effects must be the same, given " ^ e_to_string e1 ^ " and " ^ e_to_string e2)
  | Evar v1, Evar v2 -> if v1 = v2 then e2 
    else eq_error l ("Effect variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Evar v1, Eset _ -> 
    eq_error l ("Effect variable " ^ v1 ^ " cannot be used where a concrete set of effects is specified")


let build_variable_range d_env v typ =
  let t,_ = get_abbrev d_env typ in
  let t_actual = match t.t with | Tabbrev(_,t) -> t | _ -> t in
  match t_actual.t with
    | Tapp("atom", [TA_nexp n]) -> Some(VR_eq(v,n))
    | Tapp("range", [TA_nexp base;TA_nexp top]) ->
      Some(VR_range(v,[LtEq((Patt Parse_ast.Unknown),Require,base,top)]))
    | Tapp("vector", [TA_nexp start; TA_nexp rise; _; _]) -> Some(VR_vec_eq(v,rise))
    | Tuvar _ -> Some(VR_recheck(v,t_actual))
    | _ -> None

let get_vr_var = 
  function | VR_eq (v,_) | VR_range(v,_) | VR_vec_eq(v,_) | VR_vec_r(v,_) | VR_recheck(v,_) -> v

let compare_variable_range v1 v2 = compare (get_vr_var v1) (get_vr_var v2)

let extract_bounds d_env v typ = 
  match build_variable_range d_env v typ with
    | None -> No_bounds
    | Some vb -> Bounds([vb], None)

let find_bounds v bounds = match bounds with
  | No_bounds -> None
  | Bounds(bs,maps) ->
    let rec find_rec bs = match bs with
      | [] -> None
      | b::bs -> if (get_vr_var b) = v then Some(b) else find_rec bs in
    find_rec bs

let add_map_to_bounds m bounds = match bounds with
  | No_bounds -> Bounds([],Some m)
  | Bounds(bs,None) -> Bounds(bs,Some m)
  | Bounds(bs,Some m') -> Bounds(bs,Some (Nexpmap.union m m'))

let rec add_map_tannot m tannot = match tannot with
  | NoTyp -> NoTyp
  | Base(params,tag,cs,efl,efr,bounds) -> Base(params,tag,cs,efl,efr,add_map_to_bounds m bounds)
  | Overload(t,r,ts) -> Overload(add_map_tannot m t,r,ts)

let get_map_bounds = function
  | No_bounds -> None
  | Bounds(_,m) -> m

let get_map_tannot = function
  | NoTyp -> None
  | Base(_,_,_,_,_,bounds) -> get_map_bounds bounds
  | Overload _ -> None

let rec expand_nexp n = match n.nexp with
  | Nvar _ | Nconst _ | Nuvar _ | Npos_inf | Nneg_inf | Ninexact -> [n]
  | Nadd (n1,n2) | Nsub (n1,n2) | Nmult (n1,n2) -> n::((expand_nexp n1)@(expand_nexp n2))
  | N2n (n1,_) | Npow (n1,_) | Nneg n1 | Nid(_,n1) -> n::(expand_nexp n1)

let is_nconst n = match n.nexp with | Nconst _ -> true | _ -> false

let find_var_from_nexp n bounds = 
  (*let _ = Printf.eprintf "finding %s in bounds\n" (n_to_string n) in*)
  if is_nconst n then None 
  else match bounds with
    | No_bounds -> None
    | Bounds(bs,map) ->
      let rec find_rec bs n = match bs with
        | [] -> None
        | b::bs -> (match b with
            | VR_eq(ev,n1) ->
              (*let _ = Printf.eprintf "checking if %s is eq to %s, to bind to %s, eq? %b\n" 
                (n_to_string n) (n_to_string n1) ev (nexp_eq_check n1 n) in*)
              if nexp_eq_check n1 n then Some (None,ev) else find_rec bs n
            | VR_vec_eq (ev,n1)->
              (*let _ = Printf.eprintf "checking if %s is eq to %s, to bind to %s, eq? %b\n" 
                (n_to_string n) (n_to_string n1) ev (nexp_eq_check n1 n) in*)
              if nexp_eq_check n1 n then Some (Some "length",ev) else find_rec bs n
            | _ -> find_rec bs n) in
      match find_rec bs n,map with
      | None, None -> None 
      | None, Some map ->
        (match Nexpmap.apply map n with
          | None    ->  None
          | Some n' -> find_rec bs n')
      | s,_ -> s

let merge_bounds b1 b2 =
  match b1,b2 with
    | No_bounds,b | b,No_bounds -> b
    | Bounds(b1s,map1),Bounds(b2s,map2) ->
      let merged_map = match map1,map2 with
        | None, None -> None
        | None, m | m, None -> m
        | Some m1, Some m2 -> Some (Nexpmap.union m1 m2) in
      let b1s = List.sort compare_variable_range b1s in
      let b2s = List.sort compare_variable_range b2s in
      let rec merge b1s b2s = match (b1s,b2s) with
        | [],b | b,[] -> b
        | b1::b1s,b2::b2s ->
          match compare_variable_range b1 b2 with
            | -1 -> b1::(merge b1s (b2::b2s))
            | 1  -> b2::(merge (b1::b1s) b2s)
            | _  -> (match b1,b2 with
                | VR_eq(v,n1),VR_eq(_,n2) -> 
                  if nexp_eq n1 n2 then b1 else VR_range(v,[Eq((Patt Parse_ast.Unknown),n1,n2)])
                | VR_eq(v,n),VR_range(_,ranges) | 
                  VR_range(v,ranges),VR_eq(_,n) -> VR_range(v,(Eq((Patt Parse_ast.Unknown),n,n))::ranges)
                | VR_range(v,ranges1),VR_range(_,ranges2) -> VR_range(v, List.rev_append (List.rev ranges1) ranges2)
                | VR_vec_eq(v,n1),VR_vec_eq(_,n2) ->
                  if nexp_eq n1 n2 then b1 else VR_vec_r(v,[Eq((Patt Parse_ast.Unknown),n1,n2)])
                | VR_vec_eq(v,n),VR_vec_r(_,ranges) |
                  VR_vec_r(v,ranges),VR_vec_eq(_,n) -> VR_vec_r(v,(Eq((Patt Parse_ast.Unknown),n,n)::ranges))
                | _ -> b1
            )::(merge b1s b2s) in
      Bounds ((merge b1s b2s),merged_map)

let rec conforms_to_t d_env loosely within_coercion spec actual =
  (*let _ = Printf.eprintf "conforms_to_t called, evaluated loosely? %b & within_coercion? %b, with spec %s and actual %s\n"
  within_coercion loosely (t_to_string spec) (t_to_string actual) in*)
  let spec,_ = get_abbrev d_env spec in
  let actual,_ = get_abbrev d_env actual in
  match (spec.t,actual.t,loosely) with
    | (Tuvar _,_,true) -> true
    | (Ttup ss, Ttup acs,_) -> 
      (List.length ss = List.length acs) && List.for_all2 (conforms_to_t d_env loosely within_coercion) ss acs
    | (Tid is, Tid ia,_) -> is = ia
    | (Tapp(is,tas), Tapp("register",[TA_typ t]),true) ->
      if is = "register" && (List.length tas) = 1
      then List.for_all2 (conforms_to_ta d_env loosely within_coercion) tas [TA_typ t]
      else conforms_to_t d_env loosely within_coercion spec t
    | (Tapp("vector",[TA_nexp bs;TA_nexp rs;TA_ord os;TA_typ ts]),
       Tapp("vector",[TA_nexp ba;TA_nexp ra;TA_ord oa;TA_typ ta]),_) ->
      conforms_to_t d_env loosely within_coercion ts ta
      && conforms_to_o loosely os oa
      && conforms_to_n false within_coercion eq_big_int rs ra
    | (Tapp("range",[TA_nexp bs;TA_nexp rs]),Tapp("range",[TA_nexp ba;TA_nexp ra]),_) -> true (*
      conforms_to_n true within_coercion le_big_int bs ba && conforms_to_n true within_coercion ge_big_int rs ra *)
    | (Tapp("atom",[TA_nexp n]),Tapp("range",[TA_nexp ba;TA_nexp ra]),_) -> true (*
      conforms_to_n true within_coercion le_big_int ba n && conforms_to_n true within_coercion ge_big_int n ra *)
    | (Tapp("range",[TA_nexp bs;TA_nexp rs]),Tapp("atom",[TA_nexp n]),_) -> true (*
      conforms_to_n true within_coercion le_big_int bs n && conforms_to_n true within_coercion ge_big_int rs n &&
        conforms_to_n true within_coercion ge_big_int bs n *)
    | (Tapp(is,tas), Tapp(ia, taa),_) -> 
(*      let _ = Printf.eprintf "conforms to given two apps: %b, %b\n" 
        (is = ia) (List.length tas = List.length taa) in*)
      (is = ia) && (List.length tas = List.length taa) &&
      (List.for_all2 (conforms_to_ta d_env loosely within_coercion) tas taa)
    | (Tid "bit", Tapp("vector",[_;_;_;TA_typ ti]), _) ->
      within_coercion &&
      conforms_to_t d_env loosely within_coercion spec ti
    | (Tabbrev(_,s),a,_) -> conforms_to_t d_env loosely within_coercion s actual
    | (s,Tabbrev(_,a),_) -> conforms_to_t d_env loosely within_coercion spec a
    | (_,_,_) -> false
and conforms_to_ta d_env loosely within_coercion spec actual =
(*let _ = Printf.eprintf "conforms_to_ta called, evaluated loosely? %b, with %s and %s\n" 
  loosely (targ_to_string spec) (targ_to_string actual) in*)
  match spec,actual with
    | TA_typ  s, TA_typ  a -> conforms_to_t d_env loosely within_coercion s a
    | TA_nexp s, TA_nexp a -> conforms_to_n loosely within_coercion eq_big_int s a
    | TA_ord  s, TA_ord  a -> conforms_to_o loosely s a
    | TA_eft  s, TA_eft  a -> conforms_to_e loosely s a
    | _ -> false
and conforms_to_n loosely within_coercion op spec actual =
(*  let _ = Printf.eprintf "conforms_to_n called, evaluated loosely? %b, with coercion? %b with %s and %s\n" 
    loosely within_coercion (n_to_string spec) (n_to_string actual) in*)
  match (spec.nexp,actual.nexp,loosely,within_coercion) with
    | (Nconst si,Nconst ai,_,_) -> op si ai
    | (Nconst _,Nuvar _,false,false) -> false
    | _ -> true
and conforms_to_o loosely spec actual =
  match (spec.order,actual.order,loosely) with
    | (Ouvar _,_,true) | (Oinc,Oinc,_) | (Odec,Odec,_) | (_, Ouvar _,_) -> true
    | _ -> false
and conforms_to_e loosely spec actual =
  match (spec.effect,actual.effect,loosely) with
    | (Euvar _,_,true) -> true
    | (_,Euvar _,true) -> false
    | _                -> 
      try begin ignore (effects_eq (Specc Parse_ast.Unknown) spec actual); true end with
        | _ -> false

(*Is checking for structural equality amongst the types, building constraints for kind Nat. 
  When considering two range type applications, will check for consistency instead of equality
  When considering two atom type applications, will expand into a range encompasing both when widen is true
*)
let rec type_consistent_internal co d_env enforce widen t1 cs1 t2 cs2 = 
  let l = get_c_loc co in
  let t1,cs1' = get_abbrev d_env t1 in
  let t2,cs2' = get_abbrev d_env t2 in
  let cs1,cs2 = cs1@cs1',cs2@cs2' in
  let csp = cs1@cs2 in
  let t1_actual = match t1.t with | Tabbrev(_,t1) -> t1 | _ -> t1 in
  let t2_actual = match t2.t with | Tabbrev(_,t2) -> t2 | _ -> t2 in
(*  let _ = Printf.eprintf "type_consistent_internal called with, widen? %b, %s with actual %s and %s with actual %s\n" 
    widen (t_to_string t1) (t_to_string t1_actual) (t_to_string t2) (t_to_string t2_actual) in*)
  match t1_actual.t,t2_actual.t with
  | Tvar v1,Tvar v2 -> 
    if v1 = v2 then (t2,csp) 
    else eq_error l ("Type variables " ^ v1 ^ " and " ^ v2 ^ " do not match and cannot be unified")
  | Tid v1,Tid v2 -> 
    if v1 = v2 then (t2,csp) 
    else eq_error l ("Types " ^ v1 ^ " and " ^ v2 ^ " do not match")
  | Tapp("range",[TA_nexp b1;TA_nexp r1;]),Tapp("range",[TA_nexp b2;TA_nexp r2;]) -> 
    if (nexp_eq b1 b2)&&(nexp_eq r1 r2) 
    then (t2,csp)
    else (t1, csp@[GtEq(co,enforce,b1,b2);LtEq(co,enforce,r1,r2)])
  | Tapp("atom",[TA_nexp a]),Tapp("range",[TA_nexp b1; TA_nexp r1]) ->
    (t1, csp@[GtEq(co,enforce,a,b1);LtEq(co,enforce,a,r1)])
  | Tapp("range",[TA_nexp b1; TA_nexp r1]),Tapp("atom",[TA_nexp a]) ->
    (t2, csp@[LtEq(co,Guarantee,b1,a);GtEq(co,Guarantee,r1,a)])
  | Tapp("atom",[TA_nexp a1]),Tapp("atom",[TA_nexp a2]) ->
    if nexp_eq a1 a2
    then (t2,csp)
    else if not(widen) 
    then (t1, csp@[Eq(co,a1,a2)])
    else (match a1.nexp,a2.nexp with
      | Nconst i1, Nconst i2 ->
        if lt_big_int i1 i2 
        then ({t= Tapp("range",[TA_nexp a1;TA_nexp a2])},csp)
        else ({t=Tapp ("range",[TA_nexp a2;TA_nexp a1])},csp)
      (*| Nconst _, Nuvar _ | Nuvar _, Nconst _->
        (t1, csp@[Eq(co,a1,a2)])*) (*TODO This is the correct constraint. 
                                     However, without the proper support for In checks actually working,
                                     this will cause specs to not build*)      
      | _ -> (*let nu1,nu2 = new_n (),new_n () in 
             ({t=Tapp("range",[TA_nexp nu1;TA_nexp nu2])},
              csp@[LtEq(co,enforce,nu1,a1);LtEq(co,enforce,nu1,a2);LtEq(co,enforce,a1,nu2);LtEq(co,enforce,a2,nu2)])*)
        (t1, csp@[LtEq(co,enforce,a1,a2);(GtEq(co,enforce,a1,a2))]))
  (*EQ is the right thing to do, but see above. Introducing new free vars here is bad*)
  | Tapp("vector",[TA_nexp b1; TA_nexp l1; ord; ty1]),Tapp("vector",[TA_nexp b2; TA_nexp l2; ord2; ty2]) ->
    let cs = if widen then [Eq(co,l1,l2)] else [Eq(co,l1,l2);Eq(co,b1,b2)] in
    (t2, cs@(type_arg_eq co d_env enforce widen ord ord2)@(type_arg_eq co d_env enforce widen ty1 ty2))
  | Tapp(id1,args1), Tapp(id2,args2) ->
    (*let _ = Printf.eprintf "checking consistency of %s and %s\n" id1 id2 in*)
    let la1,la2 = List.length args1, List.length args2 in
    if id1=id2 && la1 = la2 
    then (t2,csp@(List.flatten (List.map2 (type_arg_eq co d_env enforce widen) args1 args2)))
    else eq_error l ("Type application of " ^ (t_to_string t1) ^ " and " ^ (t_to_string t2) ^ " must match")
  | Tfn(tin1,tout1,_,effect1),Tfn(tin2,tout2,_,effect2) -> 
    let (tin,cin) = type_consistent co d_env Require widen tin1 tin2 in
    let (tout,cout) = type_consistent co d_env Guarantee widen tout1 tout2 in
    let _ = effects_eq co effect1 effect2 in
    (t2,csp@cin@cout)
  | Ttup t1s, Ttup t2s ->
    (t2,csp@(List.flatten (List.map snd (List.map2 (type_consistent co d_env enforce widen) t1s t2s))))
  | Tuvar _, t -> equate_t t1 t2; (t1,csp)
  (*| Tapp("range",[TA_nexp b;TA_nexp r]),Tuvar _ ->
    let b2,r2 = new_n (), new_n () in
    let t2' = {t=Tapp("range",[TA_nexp b2;TA_nexp r2])} in
    equate_t t2 t2';
    (t2,csp@[GtEq(co,enforce,b,b2);LtEq(co,enforce,r,r2)])*)
  | Tapp("atom",[TA_nexp a]),Tuvar _ ->
    if widen
    then
      let b,r = new_n (), new_n () in
      let t2' = {t=Tapp("range",[TA_nexp b;TA_nexp r])} in
      begin equate_t t2 t2';
        (t2,csp@[GtEq(co,enforce,a,b);LtEq(co,enforce,a,r)]) end
    else begin equate_t t2 t1; (t2,csp) end
  | t,Tuvar _ -> equate_t t2 t1; (t2,csp)
  | _,_ -> eq_error l ("Type mismatch found " ^ (t_to_string t1) ^ " but expected a " ^ (t_to_string t2))

and type_arg_eq co d_env enforce widen ta1 ta2 = 
  match ta1,ta2 with
  | TA_typ t1,TA_typ t2 -> snd (type_consistent co d_env enforce widen t1 t2)
  | TA_nexp n1,TA_nexp n2 -> if nexp_eq n1 n2 then [] else [Eq(co,n1,n2)]
  | TA_eft e1,TA_eft e2 -> (ignore(effects_eq co e1 e2); [])
  | TA_ord o1,TA_ord o2 -> (ignore(order_eq co o1 o2);[])
  | _,_ -> eq_error (get_c_loc co) "Type arguments must be of the same kind" 

and type_consistent co d_env enforce widen t1 t2 =
  type_consistent_internal co d_env enforce widen t1 [] t2 []

let rec type_coerce_internal co d_env enforce is_explicit widen bounds t1 cs1 e t2 cs2 = 
  let l = get_c_loc co in
  let t1,cs1' = get_abbrev d_env t1 in
  let t2,cs2' = get_abbrev d_env t2 in
  let t1_actual = match t1.t with | Tabbrev(_,t1) -> t1 | _ -> t1 in
  let t2_actual = match t2.t with | Tabbrev(_,t2) -> t2 | _ -> t2 in
  let cs1,cs2 = cs1@cs1',cs2@cs2' in
  let csp = cs1@cs2 in
  (*let _ = Printf.eprintf "called type_coerce_internal is_explicit %b, widen %b, turning %s with actual %s into %s with actual %s\n" 
    is_explicit widen (t_to_string t1) (t_to_string t1_actual) (t_to_string t2) (t_to_string t2_actual) in*)
  match t1_actual.t,t2_actual.t with

    (* Toptions is an internal constructor representing the type we're
    going to be casting to and the natural type.  source-language type
    annotations might be demanding a coercion, so this checks
    conformance and adds a coercion if needed *)

  | Toptions(to1,Some to2),_ -> 
    if (conforms_to_t d_env false true to1 t2_actual || conforms_to_t d_env false true to2 t2_actual)
    then begin t1_actual.t <- t2_actual.t; (t2,csp,pure_e,e) end
    else eq_error l ("Neither " ^ (t_to_string to1) ^
                     " nor " ^ (t_to_string to2) ^ " can match expected type " ^ (t_to_string t2))
  | Toptions(to1,None),_ -> 
    if is_explicit 
    then type_coerce_internal co d_env enforce is_explicit widen bounds to1 cs1 e t2 cs2
    else (t2,csp,pure_e,e)
  | _,Toptions(to1,Some to2) -> 
    if (conforms_to_t d_env false true to1 t1_actual || conforms_to_t d_env false true to2 t1_actual)
    then begin t2_actual.t <- t1_actual.t; (t1,csp,pure_e,e) end
    else eq_error l ((t_to_string t1) ^ " can match neither expected type " ^
                        (t_to_string to1) ^ " nor " ^ (t_to_string to2))
  | _,Toptions(to1,None) -> 
    if is_explicit
    then type_coerce_internal co d_env enforce is_explicit widen bounds t1_actual cs1 e to1 cs2
    else (t1,csp,pure_e,e)

        (* recursive coercions to components of tuples.  They may be
        complex expressions, not top-level tuples, so we sometimes
        need to add a pattern match. At present we do that almost
        always, unnecessarily often.  The any_coerced is wrong *)
  | Ttup t1s, Ttup t2s ->
    let tl1,tl2 = List.length t1s,List.length t2s in
    if tl1=tl2 then 
      let ids = List.map (fun _ -> Id_aux(Id (new_id ()),l)) t1s in
      let vars = List.map2 (fun i t -> E_aux(E_id(i),(l,Base(([],t),Emp_local,[],pure_e,pure_e,nob)))) ids t1s in
      let (coerced_ts,cs,efs,coerced_vars,any_coerced) = 
        List.fold_right2 (fun v (t1,t2) (ts,cs,efs,es,coerced) ->
          let (t',c',ef,e') = type_coerce co d_env enforce is_explicit widen bounds t1 v t2 in
          ((t'::ts),c'@cs,union_effects ef efs,(e'::es), coerced || (v == e')))
          vars (List.combine t1s t2s) ([],[],pure_e,[],false) in
      if (not any_coerced) then (t2,cs,pure_e,e)
      else let e' = E_aux(E_case(e,
                                 [(Pat_aux(Pat_exp
                                             (P_aux(P_tup 
                                                      (List.map2 
                                                         (fun i t ->
                                                            P_aux(P_id i,
                                                                  (l,
                                                                   (*TODO should probably link i and t in bindings*)
                                                                   (Base(([],t),Emp_local,[],pure_e,pure_e,nob)))))
                                                         ids t1s),(l,Base(([],t1),Emp_local,[],pure_e,pure_e,nob))),
                                                     E_aux(E_tuple coerced_vars,
                                                           (l,Base(([],t2),Emp_local,cs,pure_e,pure_e,nob)))),
                                             (l,Base(([],t2),Emp_local,[],pure_e,pure_e,nob))))]),
                          (l,(Base(([],t2),Emp_local,[],pure_e,pure_e,nob)))) in
           (t2,csp@cs,efs,e')
    else eq_error l ("Found a tuple of length " ^ (string_of_int tl1) ^
                     " but expected a tuple of length " ^ (string_of_int tl2))


        (* all the Tapp cases *)
  | Tapp(id1,args1),Tapp(id2,args2) ->
    if id1=id2 && (id1 <> "vector")
        (* no coercion needed, so fall back to consistency *)
    then let t',cs' = type_consistent co d_env enforce widen t1 t2 in (t',cs',pure_e,e)
    else (match id1,id2,is_explicit with

      (* can coerce between two vectors just to change the start index *)
    | "vector","vector",_ ->
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord o1;TA_typ t1i],
        [TA_nexp b2;TA_nexp r2;TA_ord o2;TA_typ t2i] ->
        (match o1.order,o2.order with
        | Oinc,Oinc | Odec,Odec -> ()
        | Oinc,Ouvar _ | Odec,Ouvar _ -> equate_o o2 o1;
        | Ouvar _,Oinc | Ouvar _, Odec -> equate_o o1 o2;
        | _,_ -> equate_o o1 o2); 
        let cs = csp@[Eq(co,r1,r2)]@(if widen then [] else [Eq(co,b1,b2)]) in
        let t',cs' = type_consistent co d_env enforce widen t1i t2i in
        let tannot = Base(([],t2),Emp_local,cs@cs',pure_e,(get_cummulative_effects (get_eannot e)),nob) in
        let e' = E_aux(E_internal_cast ((l,(Base(([],t2),Emp_local,[],pure_e,pure_e,nob))),e),(l,tannot)) in
        (t2,cs@cs',pure_e,e')
      | _ -> raise (Reporting_basic.err_unreachable l "vector is not properly kinded"))

          (* coercion from a bit vector into a number *)
    | "vector","range",_ -> 
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord _;TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
        let cs = [Eq(co,b2,n_zero);LtEq(co,Guarantee,mk_sub (mk_2n(r1)) n_one,r2)] in
        (t2,cs,pure_e,E_aux(E_app((Id_aux(Id "unsigned",l)),[e]),
                            (l,
                             cons_tag_annot_efr t2 (External (Some "unsigned"))
                                                cs (get_cummulative_effects (get_eannot e)))))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
        eq_error l "Cannot convert a vector to a range without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert non-bit vector into an range"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or range is not properly kinded"))

          (* similar to vector/range case *)
    | "vector","atom",_ -> 
      (match args1,args2 with
      | [TA_nexp b1;TA_nexp r1;TA_ord _;TA_typ {t=Tid "bit"}],
        [TA_nexp b2] -> 
        let cs = [GtEq(co,Guarantee,b2,n_zero);LtEq(co,Guarantee,b2,mk_sub (mk_2n(r1)) n_one)] in
        (t2,cs,pure_e,E_aux(E_app((Id_aux(Id "unsigned",l)),[e]),
                            (l,
                             cons_tag_annot_efr t2 (External (Some "unsigned"))
                                                cs (get_cummulative_effects (get_eannot e)))))
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert non-bit vector into an range"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or range is not properly kinded"))

          (* coercion from number into bit vector, if there's an explicit type annotation in the source (the "true") *)
          (* this can be lossy, if it doesn't fit into that vector, so we want to require the user to specify the vector size. It was desired by some users, but maybe should be turned back into an error and an explicit truncate function be used *)
    | "range","vector",true -> 
      (match args2,args1 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
        let cs = [] (*[LtEq(co,Guarantee,r2,mk_sub {nexp=N2n(r1,None)} n_one)] 
                      (*This constraint failing should be a warning, but truncation is ok*)*)  in
        let tannot = (l, Base(([],t2), External (Some "to_vec_inc"), cs,
                              pure_e, (get_cummulative_effects (get_eannot e)), bounds)) in
        (t2,cs,pure_e,E_aux(E_app((Id_aux(Id "to_vec_inc",l)),
                                  [(E_aux(E_internal_exp(tannot), tannot));e]),tannot))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2;TA_nexp r2;] -> 
        let cs = [] (* See above [LtEq(co,Guarantee,r2,mk_sub {nexp=N2n(r1,None)} n_one)]*) in
        let tannot = (l, Base(([],t2),External (Some "to_vec_dec"),
                              cs, pure_e, (get_cummulative_effects (get_eannot e)),bounds)) in
        (*let _ = Printf.eprintf "Generating to_vec_dec call: bounds are %s\n" (bounds_to_string bounds) in*)
        (t2,cs,pure_e,E_aux(E_app((Id_aux(Id "to_vec_dec",l)),
                                  [(E_aux(E_internal_exp(tannot), tannot)); e]),tannot))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
        eq_error l "Cannot convert a range to a vector without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert a range into a non-bit vector"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or range is not properly kinded"))

          (* similar to number to bit vector case *)
    | "atom","vector",true -> 
      (match args2,args1 with
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Oinc};TA_typ {t=Tid "bit"}],
        [TA_nexp b2] -> 
        let cs = [](*[LtEq(co,Guarantee,b2,mk_sub {nexp=N2n(r1,None)} n_one)]*) in
        let tannot = (l, Base(([],t2), External(Some "to_vec_inc"), cs, pure_e,
                              (get_cummulative_effects (get_eannot e)), bounds)) in
        (t2,cs,pure_e,E_aux(E_app((Id_aux(Id "to_vec_inc",l)),
                                  [(E_aux(E_internal_exp(tannot), tannot));e]),tannot))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Odec};TA_typ {t=Tid "bit"}],
        [TA_nexp b2] -> 
        let cs = [](*[LtEq(co,Guarantee,b2,mk_sub {nexp=N2n(r1,None)} n_one)]*) in
        let tannot = (l, Base(([],t2), External (Some "to_vec_dec"), cs, pure_e,
                              (get_cummulative_effects (get_eannot e)), bounds)) in
        (*let _ = Printf.eprintf "Generating to_vec_dec call: bounds are %s\n" (bounds_to_string bounds) in*)
        (t2,cs,pure_e,E_aux(E_app((Id_aux(Id "to_vec_dec",l)),
                                  [(E_aux(E_internal_exp(tannot), tannot)); e]),tannot))
      | [TA_nexp b1;TA_nexp r1;TA_ord {order = Ovar o};TA_typ {t=Tid "bit"}],_ -> 
        eq_error l "Cannot convert a range to a vector without an order"
      | [TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ t],_ -> 
        eq_error l "Cannot convert a range into a non-bit vector"
      | _,_ -> raise (Reporting_basic.err_unreachable l "vector or range is not properly kinded"))

          (* implicit dereference of a register, from register<t> to t, and then perhaps also from t to the expected type *)
    | "register",_,_ ->
      (match args1 with
        | [TA_typ t] ->
          (*TODO Should this be an internal cast? 
            Probably, make sure it doesn't interfere with the other internal cast and get removed *)
          (*let _ = Printf.eprintf "Adding cast to remove register read: t %s ; t2 %s\n" 
            (t_to_string t) (t_to_string t2) in*)
          let efc = (BE_aux (BE_rreg, l)) in
          let ef = add_effect efc pure_e in
          let new_e = E_aux(E_cast(t_to_typ unit_t,e),
                            (l,Base(([],t),External None,[],
                                    ef,add_effect efc (get_cummulative_effects (get_eannot e)),nob))) in
          let (t',cs,ef',e) = type_coerce co d_env Guarantee is_explicit widen bounds t new_e t2 in
          (t',cs,union_effects ef ef',e)
        | _ -> raise (Reporting_basic.err_unreachable l "register is not properly kinded"))

          (* otherwise in Tapp case, fall back on type_consistent *)
    | _,_,_ -> 
      let t',cs' = type_consistent co d_env enforce widen t1 t2 in (t',cs',pure_e,e))

        (* bit vector of length 1 to bit *)
  | Tapp("vector",[TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ {t=Tid "bit"}]),Tid("bit") ->
    let cs = [Eq(co,r1,n_one)] in
    (t2,cs,pure_e,E_aux((E_app ((Id_aux (Id "most_significant", l)), [e])),
                        (l, cons_tag_annot_efr t2 (External (Some "most_significant"))
                           cs (get_cummulative_effects (get_eannot e)))))

      (* bit to a bitvector of length 1 *)
  | Tid("bit"),Tapp("vector",[TA_nexp b1;TA_nexp r1;TA_ord o;TA_typ {t=Tid "bit"}]) ->
    let cs = [Eq(co,r1,n_one)] in
    (t2,cs,pure_e,E_aux(E_vector [e], (l, constrained_annot_efr t2 cs (get_cummulative_effects (get_eannot e)))))

      (* bit to a number range (including 0..1) *)
  | Tid("bit"),Tapp("range",[TA_nexp b1;TA_nexp r1]) ->
    let t',cs'= type_consistent co d_env enforce false {t=Tapp("range",[TA_nexp n_zero;TA_nexp n_one])} t2 in
    (t2,cs',pure_e,
     E_aux(E_case (e,[Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_zero,l)),(l,simple_annot t1)),
                                      E_aux(E_lit(L_aux(L_num 0,l)),(l,simple_annot t2))),
                              (l,simple_annot t2));
                      Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_one,l)),(l,simple_annot t1)),
                                      E_aux(E_lit(L_aux(L_num 1,l)),(l,simple_annot t2))),
                              (l,simple_annot t2));]),
           (l,simple_annot_efr t2 (get_cummulative_effects (get_eannot e)))))   


      (* similar to above, bit to a singleton number range *)
  | Tid("bit"),Tapp("atom",[TA_nexp b1]) ->
    let t',cs'= type_consistent co d_env enforce false t2 {t=Tapp("range",[TA_nexp n_zero;TA_nexp n_one])} in
    (t2,cs',pure_e,
     E_aux(E_case (e,[Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_zero,l)),(l,simple_annot t1)),
                                      E_aux(E_lit(L_aux(L_num 0,l)),(l,simple_annot t2))),
                              (l,simple_annot t2));
                      Pat_aux(Pat_exp(P_aux(P_lit(L_aux(L_one,l)),(l,simple_annot t1)),
                                      E_aux(E_lit(L_aux(L_num 1,l)),(l,simple_annot t2))),
                              (l,simple_annot t2));]),
           (l,simple_annot_efr t2 (get_cummulative_effects (get_eannot e)))))


      (* number range to a bit *)
  | Tapp("range",[TA_nexp b1;TA_nexp r1;]),Tid("bit") ->
    let t',cs'= type_consistent co d_env enforce false t1 {t=Tapp("range",[TA_nexp n_zero;TA_nexp n_one])} in
    let efr = get_cummulative_effects (get_eannot e)
    in (t2,cs',pure_e,E_aux(E_if(E_aux(E_app(Id_aux(Id "is_one",l),[e]),
                                       (l, tag_annot_efr bit_t (External (Some "is_one")) efr)),
                                 E_aux(E_lit(L_aux(L_one,l)),(l,simple_annot bit_t)),
                                 E_aux(E_lit(L_aux(L_zero,l)),(l,simple_annot bit_t))),
                            (l,simple_annot_efr bit_t efr)))

      (* similar to above *)
  | Tapp("atom",[TA_nexp b1]),Tid("bit") ->
    let t',cs'= type_consistent co d_env enforce false t1 {t=Tapp("range",[TA_nexp n_zero;TA_nexp n_one])} in
    let efr = get_cummulative_effects (get_eannot e)
    in (t2,cs',pure_e,E_aux(E_if(E_aux(E_app(Id_aux(Id "is_one",l),[e]),(l, tag_annot_efr bit_t (External None) efr)),
                                 E_aux(E_lit(L_aux(L_one,l)),(l,simple_annot bit_t)),
                                 E_aux(E_lit(L_aux(L_zero,l)),(l,simple_annot bit_t))),
                            (l,simple_annot_efr bit_t efr)))

      (* number range to an enumeration type *)
  | Tapp("range",[TA_nexp b1;TA_nexp r1;]),Tid(i) -> 
    (match Envmap.apply d_env.enum_env i with
    | Some(enums) -> 
      let num_enums = List.length enums in
      (t2,[GtEq(co,Require,b1,n_zero);LtEq(co,Require,r1,mk_c(big_int_of_int num_enums))],pure_e,
       E_aux(E_case(e,
                    List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_lit(L_aux((L_num i),l)), (l,simple_annot t1)),
                                                          E_aux(E_id(Id_aux(Id a,l)),
                                                                (l, tag_annot t2 (Enum num_enums)))),
                                                  (l,simple_annot t2))) enums),
             (l,simple_annot_efr t2 (get_cummulative_effects (get_eannot e)))))
    | None -> eq_error l ("Type mismatch: found a " ^ (t_to_string t1) ^ " but expected " ^ (t_to_string t2)))

        (* similar to above *)
  | Tapp("atom",[TA_nexp b1]),Tid(i) -> 
    (match Envmap.apply d_env.enum_env i with
      | Some(enums) -> 
        let num_enums = List.length enums in
        (t2,[GtEq(co,Require,b1,n_zero);
             LtEq(co,Require,b1,mk_c(big_int_of_int num_enums))],pure_e,
         E_aux(E_case(e,
                      List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_lit(L_aux((L_num i),l)),(l, simple_annot t1)),
                                                            E_aux(E_id(Id_aux(Id a,l)),
                                                                  (l, tag_annot t2 (Enum num_enums)))),
                                                    (l,simple_annot t2))) enums),
               (l,simple_annot_efr t2 (get_cummulative_effects (get_eannot e)))))
      | None -> eq_error l ("Type mismatch: found a " ^ (t_to_string t1) ^ " but expected " ^ (t_to_string t2)))

        (* bit vector to an enumeration type *)
  | Tapp("vector", [TA_nexp _; TA_nexp size; _; TA_typ {t= Tid "bit"}]), Tid(i) ->
    (match Envmap.apply d_env.enum_env i with
     | Some(enums) ->
       let num_enums = List.length enums in
       (t2,[LtEq(co,Require,mk_sub (mk_2n size) n_one, mk_c_int num_enums)], pure_e,
        E_aux(E_case (E_aux(E_app((Id_aux(Id "unsigned",l)),[e]),
                            (l,
                             tag_annot_efr (mk_range n_zero (mk_sub (mk_2n size) n_one)) (External (Some "unsigned"))
                               (get_cummulative_effects (get_eannot e)))),
                      List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_lit(L_aux((L_num i),l)), (l,simple_annot t1)),
                                                            E_aux(E_id(Id_aux(Id a,l)),
                                                                  (l, tag_annot t2 (Enum num_enums)))),
                                                    (l,simple_annot t2))) enums),
              (l,simple_annot_efr t2 (get_cummulative_effects (get_eannot e)))))
     | None -> eq_error l ("Type mismatch: found a " ^ (t_to_string t1) ^ " but expected " ^ (t_to_string t2)))

        (* enumeration type to number range *)
  | Tid(i),Tapp("range",[TA_nexp b1;TA_nexp r1;]) -> 
    (match Envmap.apply d_env.enum_env i with
    | Some(enums) -> 
      (t2,[Eq(co,b1,n_zero);GtEq(co,Guarantee,r1,mk_c(big_int_of_int (List.length enums)))],pure_e,
       E_aux(E_case(e,
                    List.mapi (fun i a -> Pat_aux(Pat_exp(P_aux(P_id(Id_aux(Id a,l)), (l,simple_annot t1)),
                                                          E_aux(E_lit(L_aux((L_num i),l)),(l,simple_annot t2))),
                                                  (l,simple_annot t2))) enums),
             (l,simple_annot_efr t2 (get_cummulative_effects (get_eannot e)))))
    | None -> eq_error l ("Type mismatch: " ^ (t_to_string t1) ^ " , " ^ (t_to_string t2)))


        (* probably there's a missing enumeration type to singleton number range *)

        (* fall through to type_consistent *)
  | _,_ -> let t',cs = type_consistent co d_env enforce widen t1 t2 in (t',cs,pure_e,e)

and type_coerce co d_env enforce is_explicit widen bounds t1 e t2 = 
  type_coerce_internal co d_env enforce is_explicit widen bounds t1 [] e t2 [];;

let rec select_overload_variant d_env params_check get_all variants actual_type =
  match variants with
    | [] -> []
    | NoTyp::variants | Overload _::variants ->
      select_overload_variant d_env params_check get_all variants actual_type
    | Base((parms,t_orig),tag,cs,ef,_,bindings)::variants ->
      (*let _ = Printf.eprintf "About to check a variant %s\n" (t_to_string t_orig) in*)
      let t,cs,ef,_ = if parms=[] then t_orig,cs,ef,Envmap.empty else subst parms false false t_orig cs ef in
      (*let _ = Printf.eprintf "And after substitution %s\n" (t_to_string t) in*)
      let t,cs' = get_abbrev d_env t in
      let recur _ = select_overload_variant d_env params_check get_all variants actual_type in
      (match t.t with
        | Tfn(a,r,_,e) ->
          let is_matching = 
            if params_check then conforms_to_t d_env true false a actual_type 
            else match actual_type.t with
              | Toptions(at1,Some at2) -> 
                (conforms_to_t d_env false true at1 r || conforms_to_t d_env false true at2 r)
              | Toptions(at1,None) -> conforms_to_t d_env false true at1 r
              | _ -> conforms_to_t d_env true true actual_type r in
          (*let _ = Printf.eprintf "Checked a variant, matching? %b\n" is_matching in*)
          if is_matching 
          then (Base(([],t),tag,cs@cs',ef,pure_e,bindings))::(if get_all then (recur ()) else [])
          else recur ()
        | _ -> recur () )

let rec split_conditional_constraints = function
  | [] -> [],[],[]
  | Predicate(co,cp,cn)::cs ->
    let (csa,csp,csn) = split_conditional_constraints cs in
    (csa,cp::csp, cn::csn)
  | c::cs ->
    let (csa,csp,csn) = split_conditional_constraints cs in
    (c::csa,csp, csn)

let rec in_constraint_env = function
  | [] -> []
  | InS(co,nexp,vals)::cs ->
    (nexp,(List.map (fun c -> mk_c(big_int_of_int c)) vals))::(in_constraint_env cs)
  | In(co,i,vals)::cs -> 
    (mk_nv i,(List.map (fun c -> mk_c(big_int_of_int c)) vals))::(in_constraint_env cs)
  | _::cs -> in_constraint_env cs

let rec contains_var nu n =
  match n.nexp with
  | Nvar _ | Nuvar _ -> nexp_eq_check nu n
  | Nconst _ | Npos_inf | Nneg_inf | Ninexact -> false
  | Nadd(n1,n2) | Nsub(n1,n2) | Nmult(n1,n2) -> contains_var nu n1 || contains_var nu n2
  | Nneg n | N2n(n,_) | Npow(n,_) | Nid(_,n) -> contains_var nu n

let rec contains_in_vars in_env n =
  match in_env with
  | [] -> None
  | (ne,vals)::in_env -> 
    (match contains_in_vars in_env n with
    | None -> if contains_var ne n then Some [ne,vals] else None
    | Some(e_env) -> if contains_var ne n then Some((ne,vals)::e_env) else Some(e_env))

let rec get_nuvars n =
  match n.nexp with
    | Nconst _ | Nvar _ | Nid _ | Npos_inf | Nneg_inf | Ninexact-> []
    | Nuvar _ -> [n]
    | Nmult(n1,n2) | Nadd(n1,n2) | Nsub(n1,n2) -> (get_nuvars n1)@(get_nuvars n2)
    | Nneg n | N2n(n,_) | Npow(n,_) -> get_nuvars n

let rec get_all_nuvars_cs cs = match cs with
  | [] -> Var_set.empty 
  | (Eq(_,n1,n2) | GtEq(_,_,n1,n2) | LtEq(_,_,n1,n2) | Gt(_,_,n1,n2) | Lt(_,_,n1,n2))::cs -> 
    let s = get_all_nuvars_cs cs in
    let n1s = get_nuvars n1 in
    let n2s = get_nuvars n2 in
    List.fold_right (fun n s -> Var_set.add n s) (n1s@n2s) s
  | Predicate(_,cp,cn)::cs -> 
    Var_set.union (get_all_nuvars_cs [cp;cn]) (get_all_nuvars_cs cs)
  | CondCons(_,_,_,pats,exps)::cs ->
    let s = get_all_nuvars_cs cs in
    let ps = get_all_nuvars_cs pats in
    let es = get_all_nuvars_cs exps in
    Var_set.union s (Var_set.union ps es)
  | BranchCons(_,_,c)::cs ->
    Var_set.union (get_all_nuvars_cs c) (get_all_nuvars_cs cs)
  | _::cs -> get_all_nuvars_cs cs

let rec subst_nuvars nus n =
  let is_imp_param = n.imp_param in
  let new_n = 
    match n.nexp with
      | Nconst _ | Nvar _ | Nid _ | Npos_inf | Nneg_inf | Ninexact -> n
      | Nuvar _ ->
        (match Nexpmap.apply nus n with
          | None -> n
          | Some nc -> nc)
      | Nmult(n1,n2) -> mk_mult (subst_nuvars nus n1) (subst_nuvars nus n2)
      | Nadd(n1,n2) -> mk_add (subst_nuvars nus n1) (subst_nuvars nus n2)
      | Nsub(n1,n2) -> mk_sub (subst_nuvars nus n1) (subst_nuvars nus n2)
      | Nneg n -> mk_neg (subst_nuvars nus n)
      | N2n(n,None) -> mk_2n (subst_nuvars nus n)
      | N2n(n,Some(i)) -> mk_2nc (subst_nuvars nus n) i
      | Npow(n,i) -> mk_pow (subst_nuvars nus n) i in
  (if is_imp_param then set_imp_param new_n);
  new_n

let rec subst_nuvars_cs nus cs = 
  match cs with
    | [] -> []
    | Eq(l,n1,n2)::cs -> Eq(l,subst_nuvars nus n1,subst_nuvars nus n2)::(subst_nuvars_cs nus cs)
    | NtEq(l,n1,n2)::cs -> NtEq(l, subst_nuvars nus n1, subst_nuvars nus n2)::(subst_nuvars_cs nus cs)
    | GtEq(l,enforce,n1,n2)::cs -> GtEq(l,enforce,subst_nuvars nus n1, subst_nuvars nus n2)::(subst_nuvars_cs nus cs)
    | Gt(l,enforce,n1,n2)::cs -> Gt(l,enforce,subst_nuvars nus n1, subst_nuvars nus n2)::(subst_nuvars_cs nus cs)
    | LtEq(l,enforce,n1,n2)::cs -> LtEq(l,enforce,subst_nuvars nus n1, subst_nuvars nus n2)::(subst_nuvars_cs nus cs)
    | Lt(l,enforce,n1,n2)::cs -> Lt(l,enforce,subst_nuvars nus n1, subst_nuvars nus n2)::(subst_nuvars_cs nus cs)
    | In(l,s,ns)::cs -> In(l,s,ns)::(subst_nuvars_cs nus cs)
    | InS(l,n,ns)::cs -> InS(l,subst_nuvars nus n,ns)::(subst_nuvars_cs nus cs)
    | Predicate(l, cp,cn)::cs -> 
      Predicate(l, List.hd(subst_nuvars_cs nus [cp]), List.hd(subst_nuvars_cs nus [cn]))::(subst_nuvars_cs nus cs)
    | CondCons(l,kind,my_substs,cs_p,cs_e)::cs -> 
      CondCons(l,kind,my_substs,subst_nuvars_cs nus cs_p,subst_nuvars_cs nus cs_e)::(subst_nuvars_cs nus cs)
    | BranchCons(l,possible_invars,bs)::cs -> 
      BranchCons(l,possible_invars,subst_nuvars_cs nus bs)::(subst_nuvars_cs nus cs)

let rec constraint_size = function
  | [] -> 0
  | c::cs -> 
    (match c with 
      | CondCons(_,_,_,ps,es) -> constraint_size ps + constraint_size es
      | BranchCons(_,_,bs) -> constraint_size bs
      | _ -> 1) + constraint_size cs

let freshen_constraints cs =
  let nuvars =
    Var_set.fold (fun n map ->
        let ne = new_n() in
        (*let _ = Printf.eprintf "mapping %s to %s\n%!" (n_to_string n) (n_to_string ne) in*)
        Nexpmap.insert map (n,ne)) (get_all_nuvars_cs cs) Nexpmap.empty in
  (subst_nuvars_cs nuvars cs,nuvars)

let rec prepare_constraints = function
  | [] -> []
  | CondCons(l,(Positive|Negative|Switch as kind),None,cs_p,cs_e)::cs ->
    let (new_pred_cs,my_substs) = freshen_constraints cs_p in
    let new_expr_cs = subst_nuvars_cs my_substs cs_e in
    CondCons(l,kind,Some(my_substs),new_pred_cs,(prepare_constraints new_expr_cs))::(prepare_constraints cs)
  | CondCons(l,Solo,None,cs_p,cs_e)::cs ->
    CondCons(l,Solo,None,cs_p,(prepare_constraints cs_e))::(prepare_constraints cs)
  | BranchCons(l,_,bs)::cs -> BranchCons(l,None, prepare_constraints bs)::(prepare_constraints cs)
  | c::cs -> c::(prepare_constraints cs)

let nexpmap_to_string nmap =
  Nexpmap.fold (fun acc k v ->
      match v with
      | One n -> "(" ^ n_to_string k ^ " |-> " ^ n_to_string n ^ ") " ^ acc
      | Two(n1,n2) -> "(" ^ n_to_string k ^ " |-> (" ^ n_to_string n1 ^ ", or " ^ n_to_string n2 ^ ")) " ^ acc
      | Many ns -> "(" ^ n_to_string k ^ " |-> (" ^ string_of_list ", " n_to_string ns ^ ") : " ^ (string_of_list ", " (fun n -> if is_all_nuvar n then "true" else "false") ns) ^ ") " ^ acc) "" nmap

let rec make_merged_constraints acc =  function
  | [] -> acc
  | c::cs ->
    (*    let _ = Printf.eprintf "merging constraints acc thus far is %s\n%!" (nexpmap_to_string acc) in*)
    make_merged_constraints 
      (Nexpmap.fold 
         (fun acc k v ->
(*            let _ = Printf.eprintf "folding over c: we have %s |-> %s for acc of %s\n%!" 
              (n_to_string k) (n_to_string v) (nexpmap_to_string acc) in*)
            match Nexpmap.apply acc k with
            | None -> Nexpmap.insert acc (k, One v)
            | Some(One v') -> Nexpmap.insert (Nexpmap.remove acc k) (k, Two(v,v'))
            | Some(Two(v',v'')) -> Nexpmap.insert (Nexpmap.remove acc k) (k,Many [v;v';v''])
            | Some(Many vs) -> Nexpmap.insert (Nexpmap.remove acc k) (k,Many (v::vs))) acc c)
      cs      
      
let merge_branch_constraints merge_nuvars constraint_sets =
  (*let _ = Printf.eprintf "merge_branch_constraints called\n%!" in*)
  (*Separate variables into only occurs in one set, or occurs in multiple sets*)
  (*assumes k and n outermost and all nuvar*)
  let conditionally_set k n =
    not(merge_nuvars) || ((occurs_in_nexp k n) || (occurs_in_nexp n k) || equate_n k n || equate_n n k) in
  (*This function assumes n outermost and k all nuvar; 
    inserts a new nuvar at bottom, and an eq to k for non-nuvar*)
  let conditionally_lift_to_nuvars_on_merge k n =
    if not(merge_nuvars) || (is_all_nuvar n && conditionally_set k n)
    then [],None
    else
      let new_nuvar = new_n () in
      let new_temp = new_n () in
      match first_non_nu n with
      | Some n' ->
        new_temp.nexp <- n'.nexp;      (*Save equation*)
        n'.nexp <- new_nuvar.nexp;      (*Put a nuvar in place*)
        [Eq(Patt(Parse_ast.Unknown),k,new_temp)], Some(Nexpmap.from_list [k,new_temp])
      | None -> [],None
  in
  let merged_constraints = make_merged_constraints Nexpmap.empty constraint_sets in
  let merge_walker (sc,new_cs,new_map) k v = match v with
    | One n ->
      (*let _ = Printf.eprintf "Variables in one path: merge_nuvars %b, key %s, one %s\n%!" 
          merge_nuvars (n_to_string k) (n_to_string n) in*)
      let k,n = get_outer_most k, get_outer_most n in
      if (is_all_nuvar k || is_all_nuvar n) && conditionally_set k n
      then (sc,new_cs,new_map)
      else (sc, (Eq(Patt(Parse_ast.Unknown),k,n))::new_cs,new_map)
    | Two(n1,n2) ->
      (*let _ = Printf.eprintf "Variables in two paths: merge_nuvars %b, key %s, n1 %s, n2 %s\n%!" 
          merge_nuvars (n_to_string k) (n_to_string n1) (n_to_string n2) in*)
      let k,n1,n2 = get_outer_most k, get_outer_most n1, get_outer_most n2 in
      let all_nk, all_nn1, all_nn2 = is_all_nuvar k, is_all_nuvar n1, is_all_nuvar n2 in
      if all_nk && all_nn1 && all_nn2 
      then
        let set1,set2 = conditionally_set k n1, conditionally_set k n2 in
        if set1 && set2 then sc,new_cs,new_map 
        else (Nexpmap.insert sc (k,v),new_cs,new_map)
      else (if all_nk
            then
              let ncs1,nm1 = conditionally_lift_to_nuvars_on_merge k n1 in
              let ncs2,nm2 = conditionally_lift_to_nuvars_on_merge k n2 in
              let set1,set2 = conditionally_set k n1, conditionally_set k n2 in
              if set1 && set2
              then sc,ncs1@ncs2@new_cs,merge_option_maps new_map (merge_option_maps nm1 nm2)
              else (Nexpmap.insert sc (k,v),new_cs,merge_option_maps new_map (merge_option_maps nm1 nm2))
            else (Nexpmap.insert sc (k,v),new_cs,new_map))
    | Many ns ->
      (*(if merge_nuvars then
        let _ = Printf.eprintf "Variables in many paths: merge_nuvars %b, key %s, [" 
            merge_nuvars (n_to_string k) in
        let _ = List.iter (fun n -> Printf.eprintf "%s ;" (n_to_string n)) ns in
        let _ = Printf.eprintf "]\n%!" in
        let _ = Printf.eprintf "Is all nuvar? %b\n%!" 
        (List.for_all is_all_nuvar (List.map get_outer_most ns)) in ());*)
      let k, ns = get_outer_most k, List.map get_outer_most ns in
      let is_all_nuvars = List.for_all is_all_nuvar ns in
      if not(merge_nuvars)
      then Nexpmap.insert sc (k,v),new_cs,new_map
      else if is_all_nuvars
      then if List.for_all (fun i -> i) (List.map (conditionally_set k) ns)
        then (sc,new_cs,new_map)
        else (Nexpmap.insert sc (k,v),new_cs,new_map)
      else
        let rec all_eq = function
          | [] | [_] -> true
          | n1::n2::ns ->
            (nexp_eq n1 n2) && all_eq (n2::ns) 
        in 
        if (all_eq ns) && not(ns=[])
        then if List.for_all (fun i -> i) (List.map (conditionally_set k) ns)
          then  (sc,new_cs,new_map)
          else (Nexpmap.insert sc (k,v),new_cs,new_map)
        else            
          let sets = List.map (conditionally_lift_to_nuvars_on_merge k) ns in
          let css = (List.flatten (List.map fst sets))@ new_cs in
          let map = List.fold_right merge_option_maps (List.map snd sets) new_map in
          (Nexpmap.insert sc (k,v),css, map) in
  let shared_path_distinct_constraints = Nexpmap.fold merge_walker (Nexpmap.empty,[],None) merged_constraints in
  (*let _ = if merge_nuvars then
      Printf.eprintf "merge branch constraints: shared var mappings after merge %s\n%!"
        (nexpmap_to_string merged_constraints) in*)
  if merge_nuvars then Nexpmap.fold merge_walker (Nexpmap.empty,[],None) merged_constraints
  else 
  shared_path_distinct_constraints

let rec extract_path_substs = function
  | [] -> [],[]
  | CondCons(l,k,Some(substs),ps,es)::cs -> 
    let set v n = match n.nexp with
      | Nuvar _ -> ignore(equate_n n v)
      | _ -> if nexp_eq n v then () else assert false (*Get a location to here*)
    in
    let updated_substs = 
      Nexpmap.fold (fun substs key newvar ->
          (*let _ =  Printf.eprintf "building substs sets: %s |-> %s\n" (n_to_string key) (n_to_string newvar) in*)
          match key.nexp with
          | Nuvar _ -> Nexpmap.insert substs (key,newvar)
          | _ -> begin set key newvar; substs end) Nexpmap.empty substs in
    let (substs, cs_rest) = extract_path_substs cs in
    (updated_substs::substs, CondCons(l,k,Some(updated_substs),ps,es)::cs_rest)
  | c::cs -> 
    let (substs,cs_rest) = extract_path_substs cs in
    (substs,c::cs_rest)

let rec merge_paths merge_nuvars = function
  | [] -> [],None
  | (BranchCons(co,_,branches) as b)::cs ->
    (*let _ = Printf.eprintf "merge_paths BranchCons case branch is %s\n\n" (constraints_to_string [b]) in*)
    let branches_merged,new_map = merge_paths merge_nuvars branches in
    let path_substs,branches_up = extract_path_substs branches_merged in
    let (shared_vars,new_cs,nm) = merge_branch_constraints merge_nuvars path_substs in
    let (rest_cs,rest_map) = merge_paths merge_nuvars cs in
    let out_map = merge_option_maps (merge_option_maps new_map nm) rest_map in
    (BranchCons(co,Some(shared_vars),branches_up)::(new_cs@rest_cs), out_map)
  | CondCons(co,k,substs,ps,es)::cs ->
    (*let _ = Printf.eprintf "merge_paths CondCons case: ps %s \n es %s\n\n" (constraints_to_string ps) (constraints_to_string es) in*)
    let (new_es,nm) = merge_paths merge_nuvars es in
    let (rest_cs,rest_map) = merge_paths merge_nuvars cs in
    let map = merge_option_maps nm rest_map in
    (CondCons(co,k,substs,ps,new_es)::rest_cs, map)
  | con::cs ->
    let (rest_cs, rest_map) = merge_paths merge_nuvars cs in
    (con::rest_cs, rest_map)

let rec equate_nuvars in_env cs = 
  (*let _ = Printf.eprintf "equate_nuvars\n" in*)
  let equate = equate_nuvars in_env in
  match cs with
    | [] -> []
    | (Eq(co,n1,n2) as c)::cs ->
      (match (n1.nexp,n2.nexp) with
        | Nuvar u1, Nuvar u2 ->
          (*let _ = Printf.eprintf "setting two nuvars, %s and %s in equate\n" (n_to_string n1) (n_to_string n2) in*)
          let occurs = (occurs_in_nexp n1 n2) || (occurs_in_nexp n2 n1) in
          (*let _ = Printf.eprintf "did they occur? %b\n" occurs in*)
          if not(occurs) 
          then if (equate_n n1 n2) then equate cs else c::equate cs
          else c::equate cs
        | _ -> c::equate cs)
    | CondCons(co,kind,substs,pats,exps):: cs ->
      let pats' = equate pats in
      let exps' = equate exps in
      (match pats',exps' with
        | [],[] -> equate cs
        | _     -> CondCons(co,kind,substs,pats',exps')::(equate cs))
    | BranchCons(co,sv,branches)::cs ->
      let b' = equate branches in
      if [] = b' 
      then equate cs
      else BranchCons(co,sv,b')::(equate cs)
    | c::cs -> c::(equate cs)


let rec flatten_constraints = function
  | [] -> []
  | c::cs -> 
    (match c with 
      | CondCons(_,_,_,ps,es) -> flatten_constraints ps @ flatten_constraints es
      | BranchCons(_,_,bs) -> flatten_constraints bs
      | _ -> [c]) @ flatten_constraints cs

let rec simple_constraint_check in_env cs = 
  let check = simple_constraint_check in_env in
  (*let _ = Printf.eprintf "simple_constraint_check of %i constraints\n%!" (constraint_size cs) in*)
  match cs with 
  | [] -> []
  | Eq(co,n1,n2)::cs -> 
    let eq_to_zero ok_to_set n1 n2 =    
      (*let _ = Printf.eprintf "eq_to_zero called with n1 %s and n2%s\n" (n_to_string n1) (n_to_string n2) in*)
      let new_n = normalize_nexp (mk_sub n1 n2) in
      (match new_n.nexp with
        | Nconst i -> 
          if eq_big_int i zero
          then None
          else eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires "
                                        ^ n_to_string new_n ^ " to equal 0, not " ^ string_of_big_int i)
        | Nuvar u1 ->
          if ok_to_set
          then if (equate_n new_n n_zero) then None else Some(Eq(co,new_n,n_zero))
          else Some(Eq(co,new_n,n_zero))
        | Nadd(new_n1,new_n2) ->
          (match new_n1.nexp, new_n2.nexp with
            | _ -> Some(Eq(co,n1,n2)))
        | _ -> Some(Eq(co,n1,n2))) in
    let check_eq ok_to_set n1 n2 = 
      (*let _ = Printf.eprintf "eq check, about to normalize_nexp of %s, %s arising from %s \n" 
        (n_to_string n1) (n_to_string n2) (co_to_string co) in*)
      let n1',n2' = normalize_nexp n1,normalize_nexp n2 in
      (*let _ = Printf.eprintf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
      (match n1'.nexp,n2'.nexp,n1.nexp,n2.nexp with
      | Ninexact,nok,_,_ | nok,Ninexact,_,_ -> 
        eq_error (get_c_loc co) 
          ("Type constraint arising from here requires " ^ n_to_string {nexp = nok; imp_param = false}
           ^ " to be equal to +inf + -inf")
      | Npos_inf,Npos_inf,_,_ | Nneg_inf, Nneg_inf,_,_ -> None
      | Nconst i1, Nconst i2,_,_ | Nconst i1,N2n(_,Some(i2)),_,_ | N2n(_,Some(i1)),Nconst(i2),_,_ -> 
        if eq_big_int i1 i2 then None 
        else eq_error (get_c_loc co) 
          ("Type constraint mismatch: constraint arising from here requires " ^ n_to_string n1 ^
              " to equal " ^ n_to_string n2 )
      | Nuvar u1, Nuvar u2, _, _ ->
        (*let _ = Printf.eprintf "setting two nuvars, %s and %s, it is ok_to_set %b\n" 
          (n_to_string n1) (n_to_string n2) ok_to_set in*)
        if nexp_eq_check n1 n2
        then None
        else 
          let occurs = (occurs_in_nexp n1' n2') || (occurs_in_nexp n2' n1') in
          if ok_to_set && not(occurs) 
          then if (equate_n n1' n2') then None else Some(Eq(co,n1',n2'))
          else if occurs then eq_to_zero ok_to_set n1' n2'
          else Some(Eq(co,n1',n2'))
      | _, Nuvar u, _, Nuvar _ -> 
        (*let _ = Printf.eprintf "setting right nuvar\n" in*)
        let occurs = occurs_in_nexp n1' n2 in
        let leave = leave_nu_as_var (get_outer_most n2') in
        (*let _ = Printf.eprintf "occurs? %b, leave? %b n1' %s in n2' %s\n" 
          occurs leave (n_to_string n1') (n_to_string n2') in*)
        if (*not(u.nin) &&*) ok_to_set && not(occurs) && not(leave)
        then if (equate_n n2 n1) then  None else (Some (Eq(co,n1',n2')))
        else if occurs 
        then eq_to_zero ok_to_set n1' n2'
        else Some (Eq(co,n1',n2')) 
      | Nuvar u, _,Nuvar _, _ ->
        (*let _ = Printf.eprintf "setting left nuvar\n" in*)
        let occurs = occurs_in_nexp n2' n1 in
        let leave = leave_nu_as_var (get_outer_most n1') in
        (*let _ = Printf.eprintf "occurs? %b, leave? %b n2' %s in n1' %s\n"
          occurs leave (n_to_string n2') (n_to_string n1') in*)
        if (*not(u.nin) &&*) ok_to_set && not(occurs) && not(leave)
        then if equate_n n1 n2 then None else (Some (Eq(co,n1,n2)))
        else if occurs
        then eq_to_zero ok_to_set n1' n2'
        else Some (Eq(co,n1',n2'))
      | _,_,_,_ -> 
        if nexp_eq_check n1' n2'
        then None
        else eq_to_zero ok_to_set n1' n2')
    in
    (match check_eq true n1 n2 with
      | None -> (check cs)
      | Some(c) -> c::(check cs))
  | NtEq(co,n1,n2)::cs -> 
    let nt_eq_to_zero n1 n2 =   
      (*let _ = Printf.eprintf "nt_eq_to_zero called with n1 %s and n2%s\n" (n_to_string n1) (n_to_string n2) in*)
      let new_n = normalize_nexp (mk_sub n1 n2) in
      (match new_n.nexp with
        | Nconst i -> 
          if eq_big_int i zero
          then eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires "
                                        ^ n_to_string new_n ^ " to not equal 0")
          else None
        | _ -> Some(NtEq(co,n1,n2))) in
    let check_not_eq n1 n2 = 
      (*let _ = Printf.eprintf "not eq check, about to normalize_nexp of %s, %s arising from %s \n"
        (n_to_string n1) (n_to_string n2) (co_to_string co) in*)
      let n1',n2' = normalize_nexp n1,normalize_nexp n2 in
      (*let _ = Printf.eprintf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
      (match n1'.nexp,n2'.nexp with
      | Ninexact,nok | nok,Ninexact -> 
        eq_error (get_c_loc co) 
          ("Type constraint arising from here requires " ^ n_to_string {nexp = nok; imp_param = false} ^
              " to be compared to +inf + -inf")
      | Npos_inf,Npos_inf | Nneg_inf, Nneg_inf -> 
        eq_error (get_c_loc co)
          ("Type constraint arising from here requires " ^ n_to_string n1' ^ " to be not = to " ^ n_to_string n2')
      | Nconst i1, Nconst i2 | Nconst i1,N2n(_,Some(i2)) | N2n(_,Some(i1)),Nconst(i2) -> 
        if eq_big_int i1 i2 
        then eq_error (get_c_loc co) 
          ("Type constraint mismatch: constraint arising from here requires " ^ n_to_string n1 ^
              " to not equal " ^ n_to_string n2 )
        else None
      | _,_ -> 
        if nexp_eq_check n1' n2'
        then eq_error (get_c_loc co)
          ("Type constraing mismatch: constraint arising from here requires " ^ n_to_string n1 ^ " to not equal " ^
              n_to_string n2)
        else nt_eq_to_zero n1' n2')
    in
    (match check_not_eq n1 n2 with
      | None -> (check cs)
      | Some(c) -> c::(check cs))
  | GtEq(co,enforce,n1,n2)::cs ->
    (*let _ = Printf.eprintf ">= check, about to normalize_nexp of %s, %s\n" 
      (n_to_string n1) (n_to_string n2) in *)
    let n1',n2' = normalize_nexp n1,normalize_nexp n2 in
    (*let _ = Printf.eprintf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in*)
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 | Nconst i1,N2n(_,Some(i2)) | N2n(_,Some(i1)),Nconst i2 -> 
      if ge_big_int i1 i2 
      then check cs
      else eq_error (get_c_loc co) 
        ("Type constraint mismatch: constraint of " ^ n_to_string n1 ^ " >= " ^ n_to_string n2 ^ 
            " arising from here requires " 
         ^ string_of_big_int i1 ^ " to be greater than or equal to " ^ string_of_big_int i2)
    | Npos_inf, _ |  _, Nneg_inf  -> check cs
    | Nconst _ ,Npos_inf -> 
      eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires " 
                               ^ (n_to_string n1') ^ " to be greater than or equal to infinity")
(*    | Nneg_inf,Nuvar _ ->
      if equate_n n2' n1' then check cs else (GtEq(co,enforce,n1',n2')::check cs)
    | Nneg_inf, _ -> 
      eq_error (get_c_loc co) 
        ("Type constraint mismatch: constraint arising from here requires negative infinity to be >= to " 
         ^ (n_to_string n2')) *)
    | Nuvar _, _ | _, Nuvar _ -> GtEq(co,enforce, n1, n2)::(check cs)
    | _,_ -> 
      (match nexp_ge n1' n2' with
        | Yes -> check cs
        | No -> eq_error (get_c_loc co) 
          ("Type constraint mismatch: constraint arising from here requires " ^ n_to_string n1 ^ " to be >= to " ^ 
              (n_to_string n2))
        | Maybe ->
          let new_n = normalize_nexp (mk_sub n1' n2') in
          (match new_n.nexp with
            | Nconst i -> 
              if ge_big_int i zero
              then (check cs)
              else eq_error (get_c_loc co) 
                ("Type constraint mismatch: constraint arising from here requires "
                 ^ n_to_string new_n ^ " to be greater than or equal to 0, not " ^ string_of_big_int i)
            | _ -> GtEq(co,enforce,n1',n2')::(check cs))))
  | Gt(co,enforce,n1,n2)::cs ->
    (*let _ = Printf.eprintf "> check, about to normalize_nexp of %s, %s\n"
      (n_to_string n1) (n_to_string n2) in *)
    let n1',n2' = normalize_nexp n1,normalize_nexp n2 in
    (*let _ = Printf.eprintf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in*)
    (match nexp_gt n1' n2' with
      | Yes -> check cs
      | No -> eq_error (get_c_loc co)
          ("Type constraint mismatch: constraint arising from here requires " ^ n_to_string n1 ^ " to be > to " ^ 
              (n_to_string n2))
      | Maybe -> 
        let new_n = normalize_nexp (mk_sub n1' n2') in
        (match new_n.nexp with
          | Nconst i -> 
            if gt_big_int i zero
            then (check cs)
            else eq_error (get_c_loc co) 
              ("Type constraint mismatch: constraint arising from here requires "
               ^ n_to_string new_n ^ " to be greater than or equal to 0, not " ^ string_of_big_int i)
          | _ -> Gt(co,enforce,n1',n2')::(check cs)))
  | LtEq(co,enforce,n1,n2)::cs ->
    (*let _ = Printf.eprintf "<= check, about to normalize_nexp of %s, %s\n" 
      (n_to_string n1) (n_to_string n2) in *)
    let n1',n2' = normalize_nexp n1,normalize_nexp n2 in
    (*let _ = Printf.eprintf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 | Nconst i1, N2n(_,Some(i2)) | N2n(_,Some(i1)),Nconst i2 -> 
      if le_big_int i1 i2 
      then check cs
      else eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires " 
                                    ^ string_of_big_int i1 ^ " to be less than or equal to " ^ string_of_big_int i2)
    | _, Npos_inf | Nneg_inf, _  -> check cs
    | Nuvar _, _ | _, Nuvar _ -> LtEq(co,enforce, n1, n2)::(check cs)
    | _,_ ->
      (match nexp_ge n2' n1' with
        | Yes -> check cs
        | No -> eq_error (get_c_loc co) 
          ("Type constraint mismatch: constraint arising from here requires " ^ n_to_string n1 ^
              " to be less than or equal to " ^ (n_to_string n2))
        | Maybe -> LtEq(co,enforce,n1',n2')::(check cs)))
  | Lt(co,enforce,n1,n2)::cs ->
    (*let _ = Printf.eprintf "< check, about to normalize_nexp of %s, %s\n"
      (n_to_string n1) (n_to_string n2) in *)
    let n1',n2' = normalize_nexp n1,normalize_nexp n2 in
    (*let _ = Printf.eprintf "finished evaled to %s, %s\n" (n_to_string n1') (n_to_string n2') in *)
    (match n1'.nexp,n2'.nexp with
    | Nconst i1, Nconst i2 | Nconst i1, N2n(_,Some(i2)) | N2n(_,Some(i1)),Nconst i2 -> 
      if lt_big_int i1 i2 
      then check cs
      else eq_error (get_c_loc co) ("Type constraint mismatch: constraint arising from here requires " 
                                    ^ string_of_big_int i1 ^ " to be less than " ^ string_of_big_int i2)
    | _, Npos_inf | Nneg_inf, _  -> check cs
    | _,_ ->
      (match nexp_gt n2' n1' with
        | Yes -> check cs
        | No -> eq_error (get_c_loc co) 
          ("Type constraint mismatch: constraint arising from here requires " ^ n_to_string n1 ^
              " to be less than " ^ (n_to_string n2))
        | Maybe -> Lt(co,enforce,n1',n2')::(check cs)))
  | CondCons(co,kind,substs,pats,exps):: cs ->
    (*let _ = Printf.eprintf "Condcons check length pats %i, length exps %i\n" 
      (constraint_size pats) (constraint_size exps) in*)
    let pats' = check pats in
    let exps' = check exps in
    (*let _ = Printf.eprintf "Condcons after check length pats' %i, length exps' %i\n" 
      (constraint_size pats') (constraint_size exps') in*)
    (match pats',exps',substs with
      | [],[],None -> check cs
      | _     -> CondCons(co,kind,substs,pats',exps')::(check cs))
  | BranchCons(co,sv,branches)::cs ->
    (*let _ = Printf.eprintf "BranchCons pre_check with %i branches and %i for after\n" (constraint_size branches) (constraint_size cs) in*)
    let b = check branches in
    (*let _ = Printf.eprintf "Branchcons check length branches before %i and after %i with %i remaining after\n"
      (constraint_size branches) (constraint_size b) (constraint_size cs) in*)
    if [] = b 
    then check cs
    else BranchCons(co,sv,b)::(check cs)
  | Predicate _::cs -> check cs
  | x::cs ->
    (*let _ = Printf.eprintf "In default case with %s\n%!" (constraints_to_string [x]) in*)
    x::(check cs)

let rec resolve_in_constraints cs = cs

let tri_to_bl c =
  match c with
  | Yes | Maybe -> true
  | _ -> false

type var_side = Left | Right | Neither

let reform_nexps nv lft rght =
  let contains_left, contains_right = contains_nuvar_nexp nv lft, contains_nuvar_nexp nv rght in
  if contains_left && contains_right
  then
    match isolate_nexp nv lft, isolate_nexp nv rght with
    | (Some varl, Some factorl, lft_rst), (Some varr, Some factorr, rght_rst) ->
      if nexp_eq factorl factorr && nexp_eq varl varr
      then None, normalize_nexp (mk_sub rght_rst lft_rst), Neither
      else None, normalize_nexp (mk_sub rght lft), Neither (*Hard cases, let's punt for now*)
    | (Some varl, Some factor, lft_rst), (Some varr, None, rght_rst) ->
      if nexp_eq varl varr
      then Some (normalize_nexp (mk_mult (mk_sub factor n_one) varl)),
           normalize_nexp (mk_sub rght_rst (mk_mult factor lft_rst)), Left
      else None, normalize_nexp (mk_sub rght lft), Neither (*More hard cases*)
    | (Some varl, None, lft_rst), (Some varr, Some factor, rght_rst) ->
      if nexp_eq varl varr
      then Some (normalize_nexp (mk_mult (mk_add factor n_one) varl)),
           normalize_nexp (mk_sub (mk_mult factor rght_rst) lft_rst), Left
      else None, normalize_nexp (mk_sub rght lft), Neither (*More hard cases*)
    | (Some varl, None, lft_rst), (Some varr, None, rght_rst) ->
      if nexp_eq varl varr
      then None, normalize_nexp (mk_sub rght_rst lft_rst), Neither
      else None, normalize_nexp (mk_sub rght lft), Neither
    | (None,_,_),(_,_,_) | (_,_,_),(None,_,_) -> assert false
  else if contains_left
  then  
    match isolate_nexp nv lft with
    | (Some var, Some factor, lft_rst) ->
      if divisible_by rght factor
      then Some var, normalize_nexp (mk_sub (divide_by rght factor) lft_rst),Left
      else Some (mk_mult var factor), normalize_nexp (mk_sub rght (mk_mult factor lft_rst)),Left
    | Some var, None, lft_rst -> Some var, normalize_nexp (mk_sub rght lft_rst),Left
    | None, _, lft -> None,normalize_nexp (mk_sub rght lft),Neither
  else if contains_right
  then match isolate_nexp nv rght with
    | (Some var, Some factor, rgt_rst) ->
      if divisible_by lft factor
      then Some var, normalize_nexp (mk_sub (divide_by lft factor) rgt_rst),Right
      else Some (mk_mult var factor), normalize_nexp (mk_sub lft (mk_mult factor rgt_rst)),Right
    | Some var, None, rgt_rst -> Some var, normalize_nexp (mk_sub lft rgt_rst),Right
    | None, _, rght -> None,normalize_nexp (mk_sub rght lft),Neither
  else None, normalize_nexp (mk_sub rght lft), Neither

let iso_builder nuv builder co enforce lft rgt = 
  match reform_nexps nuv lft rgt with
  | Some v, nexp_term, Left ->
    builder co enforce v nexp_term
  | Some v, nexp_term, Right ->
    builder co enforce nexp_term v
  | None,nexp_term,Neither ->
    builder co enforce n_zero nexp_term
  | _ -> assert false (*Should be unreachable*) 
  
let rec isolate_constraint nuv constraints = match constraints with
  | [] -> []
  | c::cs -> 
    (match c with 
     | LtEq(co,enforce,lft,rgt) -> iso_builder nuv (fun c e l r -> LtEq(c,e,l,r)) co enforce lft rgt
     | Lt(co,enforce,lft,rgt) ->  iso_builder nuv (fun c e l r -> Lt(c,e,l,r)) co enforce lft rgt
     | GtEq(co,enforce,lft,rgt) ->  iso_builder nuv (fun c e l r -> GtEq(c,e,l,r)) co enforce lft rgt
     | Gt(co,enforce,lft,rgt) ->  iso_builder nuv (fun c e l r -> Gt(c,e,l,r)) co enforce lft rgt
     | _ -> c)::isolate_constraint nuv cs

let check_range_consistent require_lt require_gt guarantee_lt guarantee_gt = 
  match require_lt,require_gt,guarantee_lt,guarantee_gt with
    | None,None,None,None 
    | Some _, None, None, None | None, Some _ , None, None | None, None, Some _ , None | None, None, None, Some _ 
    | Some _, Some _,None,None | None,None,Some _,Some _ (*earlier check should ensure these*)
      -> ()
    | Some(crlt,rlt), Some(crgt,rgt), Some(cglt,glt), Some(cggt,ggt) -> 
      if tri_to_bl (nexp_ge rlt glt) (*Can we guarantee the up is less than the required up*)
      then if tri_to_bl (nexp_ge rlt ggt) (*Can we guarantee the lw is less than the required up*)
        then if tri_to_bl (nexp_ge glt rgt) (*Can we guarantee the up is greater than the required lw*)
          then if tri_to_bl (nexp_ge ggt rgt) (*Can we guarantee that the lw is greater than the required lw*)
            then ()
            else multi_constraint_error cggt crgt ("Constraints arising from these locations requires greater than "
                                              ^ (n_to_string rgt) ^ " but best guarantee is " ^ (n_to_string ggt))
          else multi_constraint_error cglt crgt ("Constraints arising from these locations guarantees a number no greather than " ^ (n_to_string glt) ^ " but requires a number greater than " ^ (n_to_string rgt))
        else multi_constraint_error crlt cggt ("Constraints arising from these locations guarantees a number that is less than " ^ (n_to_string rlt) ^ " but best guarantee is " ^ (n_to_string ggt))
      else multi_constraint_error crlt cglt ("Constraints arising from these locations require no more than " ^ (n_to_string rlt) ^ " but guarantee indicates it may be above " ^ (n_to_string glt)) 
    | _ ->
      (*let _ = Printf.eprintf "check_range_consistent is in the partial case\n" in*)
      ()

let check_ranges cs =
  (*let _ = Printf.eprintf "In check_ranges with %i constraints\n%!" (constraint_size cs) in*)
  let nuvars = get_all_nuvars_cs cs in
  (*let _ = Printf.eprintf "Have %i nuvars\n" (List.length (Var_set.elements nuvars)) in*)
  let nus_with_cs = List.map (fun n -> (n,contains_nuvar n cs)) (Var_set.elements nuvars) in
  let nus_with_iso_cs = List.map (fun (n,ncs) -> (n,isolate_constraint n ncs)) nus_with_cs in
  let refined_cs = List.concat (List.map (fun (n,ncs) ->
      let guarantees,max_guarantee_lt,min_guarantee_gt =
        refine_guarantees false None None n (flatten_constraints ncs) in
      let require_cs,min_require_lt,max_require_gt = refine_requires false None None n guarantees in
      check_range_consistent  min_require_lt max_require_gt max_guarantee_lt min_guarantee_gt;
      require_cs)
      nus_with_iso_cs)
  in
  refined_cs

let do_resolve_constraints = ref true

let resolve_constraints cs = 
  (*let _ = Printf.eprintf "called resolve constraints with %i constraints\n" (constraint_size cs) in*)
  if not !do_resolve_constraints
  then (cs,None)
  else
    let rec fix checker len cs =
      (*let _ = Printf.eprintf "Calling fix check thunk, fix check point is %i\n%!" len in *)
      let cs' = checker (in_constraint_env cs) cs in
      let len' = constraint_size cs' in
      if len > len' then fix checker len' cs'
      else cs' in
    (*let _ = Printf.eprintf "Original constraints are %s\n%!" (constraints_to_string cs) in*)
    let branch_freshened = prepare_constraints cs in
    (*let _ = Printf.eprintf "Constraints after prepare constraints are %s\n"
        (constraints_to_string branch_freshened) in*)
    let nuvar_equated = fix equate_nuvars (constraint_size branch_freshened) branch_freshened in
    (*let _ = Printf.eprintf "Constraints after nuvar equated are %s\n%!" (constraints_to_string nuvar_equated) in*)
    let complex_constraints = 
          fix (fun in_env cs -> let (ncs,_) = merge_paths false (simple_constraint_check in_env cs) in ncs)
            (constraint_size nuvar_equated) nuvar_equated in
    (*let _ = Printf.eprintf "Now considering %i constraints \n%!" (constraint_size complex_constraints) in*)
    let (complex_constraints,map) = merge_paths true complex_constraints in
    let complex_constraints = check_ranges complex_constraints in
    (*let _ = Printf.eprintf "Resolved as many constraints as possible, leaving %i\n" 
        (constraint_size complex_constraints) in 
      let _ = Printf.eprintf "%s\n" (constraints_to_string complex_constraints) in*)
    (complex_constraints,map)


let check_tannot l annot imp_param constraints efs = 
  match annot with
  | Base((params,t),tag,cs,ef,_,bindings) ->
    let efs = remove_local_effects efs in
    ignore(effects_eq (Specc l) efs ef);
    let s_env = (t_remove_unifications Envmap.empty t) in
    let params = Envmap.to_list s_env in
    ignore (remove_internal_unifications s_env);
    let t' = match (t.t,imp_param) with
      | Tfn(p,r,_,e),Some x -> {t = Tfn(p,r,IP_user x,e) }
      | _ -> t in
    Base((params,t'),tag,cs,ef,pure_e,bindings)
  | NoTyp -> raise (Reporting_basic.err_unreachable l "check_tannot given the place holder annotation")
  | Overload _ -> raise (Reporting_basic.err_unreachable l "check_tannot given overload")

let tannot_merge co denv widen t_older t_newer = 
  (*let _ = Printf.eprintf "tannot_merge called\n" in*)
  match t_older,t_newer with
    | NoTyp,NoTyp -> NoTyp
    | NoTyp,_ -> t_newer
    | _,NoTyp -> t_older
    | Base((ps_o,t_o),tag_o,cs_o,efl_o,_,bounds_o),Base((ps_n,t_n),tag_n,cs_n,efl_n,_,bounds_n) -> 
      (match tag_o,tag_n with
        | Default,tag -> 
          (match t_n.t with
            | Tuvar _ -> let t_o,cs_o,ef_o,_ = subst ps_o false false t_o cs_o efl_o in
                         let t,_ = type_consistent co denv Guarantee false t_n t_o in
                         Base(([],t),tag_n,cs_o,ef_o,pure_e,bounds_o)
            | _ -> t_newer)
        | Emp_local, Emp_local -> 
          (*let _ = Printf.eprintf "local-local case\n" in*)
          if conforms_to_t denv true false t_n t_o
          then
          let t,cs_b = type_consistent co denv Guarantee widen t_n t_o in
          (*let _ = Printf.eprintf "types consistent\n" in*)
          Base(([],t),Emp_local,cs_o@cs_n@cs_b,union_effects efl_o efl_n,pure_e, merge_bounds bounds_o bounds_n)
          else Base(([],t_n),Emp_local,cs_n,efl_n,pure_e,bounds_n)
        | _,_ -> t_newer)
    | _ -> t_newer
