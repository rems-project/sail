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
open Ast_util

module Nameset = Set.Make(String)

let mt = Nameset.empty

let set_to_string n = 
  let rec list_to_string = function
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ ", " ^ list_to_string ns in
  list_to_string (Nameset.elements n)


(*Query a spec for its default order if one is provided. Assumes Inc if not *)
(* let get_default_order_sp (DT_aux(spec,_)) =
  match spec with
  | DT_order (Ord_aux(o,_)) ->
    (match o with
     | Ord_inc -> Some {order = Oinc}
     | Ord_dec -> Some { order = Odec}
     | _ -> Some {order = Oinc})
  | _ -> None

let get_default_order_def = function
  | DEF_default def_spec -> get_default_order_sp def_spec
  | _ -> None

let rec default_order (Defs defs) =
  match defs with
  | [] -> { order = Oinc } (*When no order is specified, we assume that it's inc*)
  | def::defs ->
    match get_default_order_def def with
    | None -> default_order (Defs defs)
    | Some o -> o *)

(*Is within range*)

(* let check_in_range (candidate : big_int) (range : typ) : bool =
  match range.t with
  | Tapp("range", [TA_nexp min; TA_nexp max]) | Tabbrev(_,{t=Tapp("range", [TA_nexp min; TA_nexp max])}) ->
    let min,max = 
      match min.nexp,max.nexp with
      | (Nconst min, Nconst max)
      | (Nconst min, N2n(_, Some max))
      | (N2n(_, Some min), Nconst max)
      | (N2n(_, Some min), N2n(_, Some max))
        -> min, max
      | (Nneg n, Nconst max) | (Nneg n, N2n(_, Some max))->
        (match n.nexp with
         | Nconst abs_min | N2n(_,Some abs_min) ->
           (minus_big_int abs_min), max
         | _ -> assert false (*Put a better error message here*))
      | (Nconst min,Nneg n) | (N2n(_, Some min), Nneg n) ->
        (match n.nexp with
         | Nconst abs_max | N2n(_,Some abs_max) ->
           min, (minus_big_int abs_max)
         | _ -> assert false (*Put a better error message here*))
    | (Nneg nmin, Nneg nmax) ->
      ((match nmin.nexp with
          | Nconst abs_min | N2n(_,Some abs_min) -> (minus_big_int abs_min)
          | _ -> assert false (*Put a better error message here*)),
       (match nmax.nexp with
        | Nconst abs_max | N2n(_,Some abs_max) -> (minus_big_int abs_max)
        | _ -> assert false (*Put a better error message here*)))
    | _ -> assert false        
    in le_big_int min candidate && le_big_int candidate max
  | _ -> assert false

(*Rmove me when switch to zarith*)
let rec power_big_int b n =
  if eq_big_int n zero_big_int
  then unit_big_int
  else mult_big_int b (power_big_int b (sub_big_int n unit_big_int))

let unpower_of_2 b =
  let two = big_int_of_int 2 in
  let four = big_int_of_int 4 in
  let eight = big_int_of_int 8 in
  let sixteen = big_int_of_int 16 in
  let thirty_two = big_int_of_int 32 in
  let sixty_four = big_int_of_int 64 in
  let onetwentyeight = big_int_of_int 128 in
  let twofiftysix = big_int_of_int 256 in
  let fivetwelve = big_int_of_int 512 in
  let oneotwentyfour = big_int_of_int 1024 in
  let to_the_sixteen = big_int_of_int 65536 in
  let to_the_thirtytwo = big_int_of_string "4294967296" in
  let to_the_sixtyfour = big_int_of_string "18446744073709551616" in
  let ck i = eq_big_int b i in
  if      ck unit_big_int     then zero_big_int
  else if ck two              then unit_big_int
  else if ck four             then two
  else if ck eight            then big_int_of_int 3
  else if ck sixteen          then four
  else if ck thirty_two       then big_int_of_int 5
  else if ck sixty_four       then big_int_of_int 6
  else if ck onetwentyeight   then big_int_of_int 7
  else if ck twofiftysix      then eight
  else if ck fivetwelve       then big_int_of_int 9
  else if ck oneotwentyfour   then big_int_of_int 10
  else if ck to_the_sixteen   then sixteen
  else if ck to_the_thirtytwo then thirty_two
  else if ck to_the_sixtyfour then sixty_four
  else let rec unpower b power =
         if eq_big_int b unit_big_int
         then power
         else (unpower (div_big_int b  two) (succ_big_int power)) in
    unpower b zero_big_int

let is_within_range candidate range constraints =
  let candidate_actual = match candidate.t with
    | Tabbrev(_,t) -> t
    | _ -> candidate in
  match candidate_actual.t with
  | Tapp("atom", [TA_nexp n]) ->
    (match n.nexp with
     | Nconst i | N2n(_,Some i) -> if check_in_range i range then Yes else No
     | _ -> Maybe)
  | Tapp("range", [TA_nexp bot; TA_nexp top]) ->
    (match bot.nexp,top.nexp with
     | Nconst b, Nconst t | Nconst b, N2n(_,Some t) | N2n(_, Some b), Nconst t | N2n(_,Some b), N2n(_, Some t) ->
       let at_least_in = check_in_range b range in
       let at_most_in = check_in_range t range in
       if at_least_in && at_most_in
       then Yes
       else if at_least_in || at_most_in
       then Maybe
       else No
     | _ -> Maybe)
  | Tapp("vector", [_; TA_nexp size ; _; _]) ->
    (match size.nexp with
     | Nconst i | N2n(_, Some i) ->
       if check_in_range (power_big_int (big_int_of_int 2) i) range
       then Yes
       else No
     | _ -> Maybe)
  | _ -> Maybe

let is_within_machine64 candidate constraints = is_within_range candidate int64_t constraints *)
  
(************************************************************************************************)
(*FV finding analysis: identifies the free variables of a function, expression, etc *)

let conditional_add typ_or_exp bound used id =
  let known_list =
    if typ_or_exp (*true for typ*)
    then ["bit";"vector";"unit";"string";"int";"bool"]
    else ["=="; "!="; "|";"~";"&";"add_int"] in
  let i = (string_of_id id) in
  if Nameset.mem i bound || List.mem i known_list
  then used
  else Nameset.add i used

let conditional_add_typ = conditional_add true
let conditional_add_exp = conditional_add false


let nameset_bigunion = List.fold_left Nameset.union mt


let rec free_type_names_t consider_var (Typ_aux (t, _)) = match t with
  | Typ_var name -> if consider_var then Nameset.add (string_of_kid name) mt else mt
  | Typ_id name -> Nameset.add (string_of_id name) mt
  | Typ_fn (t1,t2,_) -> Nameset.union (free_type_names_t consider_var t1)
                                     (free_type_names_t consider_var t2)
  | Typ_tup ts -> free_type_names_ts consider_var ts
  | Typ_app (name,targs) -> Nameset.add (string_of_id name) (free_type_names_t_args consider_var targs)
  | Typ_wild -> mt
  | Typ_exist (kids,_,t') -> List.fold_left (fun s kid -> Nameset.remove (string_of_kid kid) s) (free_type_names_t consider_var t') kids
and free_type_names_ts consider_var ts = nameset_bigunion (List.map (free_type_names_t consider_var) ts)
and free_type_names_maybe_t consider_var = function
  | Some t -> free_type_names_t consider_var t
  | None -> mt
and free_type_names_t_arg consider_var = function
  | Typ_arg_aux (Typ_arg_typ t, _) -> free_type_names_t consider_var t
  | _ -> mt
and free_type_names_t_args consider_var targs =
  nameset_bigunion (List.map (free_type_names_t_arg consider_var) targs)


let rec free_type_names_tannot consider_var = function
  | None -> mt
  | Some (_, t, _) -> free_type_names_t consider_var t


let rec fv_of_typ consider_var bound used (Typ_aux (t,_)) : Nameset.t =
  match t with
  | Typ_wild -> used
  | Typ_var (Kid_aux (Var v,l)) ->
    if consider_var
    then conditional_add_typ bound used (Ast.Id_aux (Ast.Id v,l))
    else used
  | Typ_id id -> conditional_add_typ bound used id
  | Typ_fn(arg,ret,_) -> fv_of_typ consider_var bound (fv_of_typ consider_var bound used arg) ret
  | Typ_tup ts -> List.fold_right (fun t n -> fv_of_typ consider_var bound n t) ts used
  | Typ_app(id,targs) ->
     List.fold_right (fun ta n -> fv_of_targ consider_var bound n ta) targs (conditional_add_typ bound used id)
  | Typ_exist (kids,_,t') -> fv_of_typ consider_var (List.fold_left (fun b (Kid_aux (Var v,_)) -> Nameset.add v b) bound kids) used t'

and fv_of_targ consider_var bound used (Ast.Typ_arg_aux(targ,_)) : Nameset.t = match targ with
  | Typ_arg_typ t -> fv_of_typ consider_var bound used t
  | Typ_arg_nexp n -> fv_of_nexp consider_var bound used n
  | _ -> used

and fv_of_nexp consider_var bound used (Ast.Nexp_aux(n,_)) = match n with
  | Nexp_id id -> conditional_add_typ bound used id
  | Nexp_var (Ast.Kid_aux (Ast.Var i,_)) ->
    if consider_var
    then conditional_add_typ bound used (Ast.Id_aux (Ast.Id i, Parse_ast.Unknown))
    else used
  | Nexp_times (n1,n2) | Ast.Nexp_sum (n1,n2) | Ast.Nexp_minus(n1,n2) ->
    fv_of_nexp consider_var bound (fv_of_nexp consider_var bound used n1) n2
  | Nexp_exp n | Ast.Nexp_neg n -> fv_of_nexp consider_var bound used n
  | _ -> used

let typq_bindings (TypQ_aux(tq,_)) = match tq with
  | TypQ_tq quants ->
    List.fold_right (fun (QI_aux (qi,_)) bounds ->
        match qi with
        | QI_id (KOpt_aux(k,_)) ->
          (match k with
           | KOpt_none (Kid_aux (Var s,_)) -> Nameset.add s bounds
           | KOpt_kind (_, Kid_aux (Var s,_)) -> Nameset.add s bounds)
        | _ -> bounds) quants mt
  | TypQ_no_forall -> mt  

let fv_of_typschm consider_var bound used (Ast.TypSchm_aux ((Ast.TypSchm_ts(typq,typ)),_)) =
  let ts_bound = if consider_var then typq_bindings typq else mt in
  ts_bound, fv_of_typ consider_var (Nameset.union bound ts_bound) used typ

let rec pat_bindings consider_var bound used (P_aux(p,(_,tannot))) =
  let list_fv bound used ps = List.fold_right (fun p (b,n) -> pat_bindings consider_var b n p) ps (bound, used) in
  match p with
  | P_as(p,id) -> let b,ns = pat_bindings consider_var bound used p in
    Nameset.add (string_of_id id) b,ns
  | P_typ(t,p) ->
     let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
     let ns = fv_of_typ consider_var bound used t in pat_bindings consider_var bound ns p
  | P_id id ->
     let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
     Nameset.add (string_of_id id) bound,used
  | P_app(id,pats) ->
    let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
    list_fv bound (Nameset.add (string_of_id id) used) pats
  | P_record(fpats,_) ->
    List.fold_right (fun (Ast.FP_aux(Ast.FP_Fpat(_,p),_)) (b,n) ->
        pat_bindings consider_var bound used p) fpats (bound,used)
  | P_vector pats | Ast.P_vector_concat pats | Ast.P_tup pats | Ast.P_list pats -> list_fv bound used pats
  | _ -> bound,used

let rec fv_of_exp consider_var bound used set (E_aux (e,(_,tannot))) : (Nameset.t * Nameset.t * Nameset.t) =
  let list_fv b n s es = List.fold_right (fun e (b,n,s) -> fv_of_exp consider_var b n s e) es (b,n,s) in
  match e with
  | E_block es | Ast.E_nondet es | Ast.E_tuple es | Ast.E_vector es | Ast.E_list es ->
    list_fv bound used set es
  | E_id id ->
     let used = conditional_add_exp bound used id in
     let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
     bound,used,set
  | E_cast (t,e) ->
    let u = fv_of_typ consider_var (if consider_var then bound else mt) used t in
    fv_of_exp consider_var bound u set e
  | E_app(id,es) ->
    let us = conditional_add_exp bound used id in
    list_fv bound us set es
  | E_app_infix(l,id,r) ->
    let us = conditional_add_exp bound used id in
    list_fv bound us set [l;r]
  | E_if(c,t,e) -> list_fv bound used set [c;t;e]
  | E_for(id,from,to_,by,_,body) ->
    let _,used,set = list_fv bound used set [from;to_;by] in
    fv_of_exp consider_var (Nameset.add (string_of_id id) bound) used set body
  | E_loop(_, cond, body) -> list_fv bound used set [cond; body]
  | E_vector_access(v,i) -> list_fv bound used set [v;i]
  | E_vector_subrange(v,i1,i2) -> list_fv bound used set [v;i1;i2]
  | E_vector_update(v,i,e) -> list_fv bound used set [v;i;e]
  | E_vector_update_subrange(v,i1,i2,e) -> list_fv bound used set [v;i1;i2;e]
  | E_vector_append(e1,e2) | E_cons(e1,e2) -> list_fv bound used set [e1;e2]
  | E_record (FES_aux(FES_Fexps(fexps,_),_)) ->
     let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
     List.fold_right
       (fun (FE_aux(FE_Fexp(_,e),_)) (b,u,s) -> fv_of_exp consider_var b u s e) fexps (bound,used,set)
  | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
    let b,u,s = fv_of_exp consider_var bound used set e in
    List.fold_right
      (fun (FE_aux(FE_Fexp(_,e),_)) (b,u,s) -> fv_of_exp consider_var b u s e) fexps (b,u,s)
  | E_field(e,_) -> fv_of_exp consider_var bound used set e
  | E_case(e,pes) ->
    let b,u,s = fv_of_exp consider_var bound used set e in
    fv_of_pes consider_var b u s pes
  | E_let(lebind,e) ->
    let b,u,s = fv_of_let consider_var bound used set lebind in
    fv_of_exp consider_var b u s e
  | E_assign(lexp,e) ->
    let b,u,s = fv_of_lexp consider_var bound used set lexp in
    let _,used,set = fv_of_exp consider_var bound u s e in
    b,used,set
  | E_exit e -> fv_of_exp consider_var bound used set e
  | E_assert(c,m) -> list_fv bound used set [c;m]
  | E_return e -> fv_of_exp consider_var bound used set e
  | _ -> bound,used,set

and fv_of_pes consider_var bound used set pes =
  match pes with
  | [] -> bound,used,set
  | Pat_aux(Pat_exp (p,e),_)::pes ->
    let bound_p,us_p = pat_bindings consider_var bound used p in
    let bound_e,us_e,set_e = fv_of_exp consider_var bound_p us_p set e in
    fv_of_pes consider_var bound us_e set_e pes
  | Pat_aux(Pat_when (p,g,e),_)::pes ->
    let bound_p,us_p = pat_bindings consider_var bound used p in
    let bound_g,us_g,set_g = fv_of_exp consider_var bound_p us_p set g in
    let bound_e,us_e,set_e = fv_of_exp consider_var bound_g us_g set_g e in
    fv_of_pes consider_var bound us_e set_e pes
    
and fv_of_let consider_var bound used set (LB_aux(lebind,_)) = match lebind with
  | LB_val(pat,exp) ->
    let bound_p, us_p = pat_bindings consider_var bound used pat in
    let _,us_e,set_e = fv_of_exp consider_var bound used set exp in
    bound_p,Nameset.union us_p us_e,set_e
    
and fv_of_lexp consider_var bound used set (LEXP_aux(lexp,(_,tannot))) =
  match lexp with
  | LEXP_id id ->
    let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
    let i = string_of_id id in
    if Nameset.mem i bound
    then bound, used, Nameset.add i set
    else Nameset.add i bound, Nameset.add i used, set
  | LEXP_cast(typ,id) ->
    let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
    let i = string_of_id id in
    let used_t = fv_of_typ consider_var bound used typ in
    if Nameset.mem i bound
    then bound, used_t, Nameset.add i set
    else Nameset.add i bound, Nameset.add i used_t, set
  | LEXP_tup(tups) ->
    List.fold_right (fun l (b,u,s) -> fv_of_lexp consider_var b u s l) tups (bound,used,set)
  | LEXP_memory(id,args) ->
    let (bound,used,set) =
      List.fold_right
        (fun e (b,u,s) ->
          fv_of_exp consider_var b u s e) args (bound,used,set) in
    bound,Nameset.add (string_of_id id) used,set
  | LEXP_field(lexp,_) -> fv_of_lexp consider_var bound used set lexp
  | LEXP_vector(lexp,exp) ->
    let bound_l,used,set = fv_of_lexp consider_var bound used set lexp in
    let _,used,set = fv_of_exp consider_var bound used set exp in
    bound_l,used,set
  | LEXP_vector_range(lexp,e1,e2) ->
    let bound_l,used,set = fv_of_lexp consider_var bound used set lexp in
    let _,used,set = fv_of_exp consider_var bound used set e1 in
    let _,used,set = fv_of_exp consider_var bound used set e2 in
    bound_l,used,set

let init_env s = Nameset.singleton s

let typ_variants consider_var bound tunions =
  List.fold_right
    (fun (Tu_aux(t,_)) (b,n) -> match t with
       | Tu_id id -> Nameset.add (string_of_id id) b,n
       | Tu_ty_id(t,id) -> Nameset.add (string_of_id id) b, fv_of_typ consider_var b n t)
    tunions
    (bound,mt)

let fv_of_kind_def consider_var (KD_aux(k,_)) = match k with
  | KD_nabbrev(_,id,_,nexp) -> init_env (string_of_id id), fv_of_nexp consider_var mt mt nexp

let fv_of_type_def consider_var (TD_aux(t,_)) = match t with
  | TD_abbrev(id,_,typschm) -> init_env (string_of_id id), snd (fv_of_typschm consider_var mt mt typschm)
  | TD_record(id,_,typq,tids,_) ->
    let binds = init_env (string_of_id id) in
    let bounds = if consider_var then typq_bindings typq else mt in
    binds, List.fold_right (fun (t,_) n -> fv_of_typ consider_var bounds n t) tids mt
  | TD_variant(id,_,typq,tunions,_) ->
    let bindings = Nameset.add (string_of_id id) (if consider_var then typq_bindings typq else mt) in
    typ_variants consider_var bindings tunions
  | TD_enum(id,_,ids,_) ->
    Nameset.of_list (List.map string_of_id (id::ids)),mt
  | TD_register(id,n1,n2,_) ->
    init_env (string_of_id id), fv_of_nexp consider_var mt (fv_of_nexp consider_var mt mt n1) n2

let fv_of_tannot_opt consider_var (Typ_annot_opt_aux (t,_)) =
  match t with
  | Typ_annot_opt_some (typq,typ) ->
    let bindings = if consider_var then typq_bindings typq else mt in
    let free = fv_of_typ consider_var bindings mt typ in
    (bindings,free)
  | Typ_annot_opt_none ->
    (mt, mt)

(*Unlike the other fv, the bound returns are the names bound by the pattern for use in the exp*)
let fv_of_funcl consider_var base_bounds (FCL_aux(FCL_Funcl(id,pat,exp),l)) =
  let pat_bs,pat_ns = pat_bindings consider_var base_bounds mt pat in
  let _, exp_ns, exp_sets = fv_of_exp consider_var pat_bs pat_ns mt exp in
  (pat_bs,exp_ns,exp_sets)

let fv_of_fun consider_var (FD_aux (FD_function(rec_opt,tannot_opt,_,funcls),_)) =
  let fun_name = match funcls with
    | [] -> failwith "fv_of_fun fell off the end looking for the function name"
    | FCL_aux(FCL_Funcl(id,_,_),_)::_ -> string_of_id id in
  let base_bounds = match rec_opt with
    | Rec_aux(Ast.Rec_rec,_) -> init_env fun_name
    | _ -> mt in
  let base_bounds,ns_r = match tannot_opt with
    | Typ_annot_opt_aux(Typ_annot_opt_some (typq, typ),_) ->
      let bindings = if consider_var then typq_bindings typq else mt in
      let bound = Nameset.union bindings base_bounds in
      bound, fv_of_typ consider_var bound mt typ
    | Typ_annot_opt_aux(Typ_annot_opt_none, _) ->
      base_bounds, mt in
  let ns = List.fold_right (fun (FCL_aux(FCL_Funcl(_,pat,exp),_)) ns ->
      let pat_bs,pat_ns = pat_bindings consider_var base_bounds ns pat in
      let _, exp_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
      exp_ns) funcls mt in
  (* let _ = Printf.eprintf "Function %s uses %s\n" fun_name (set_to_string (Nameset.union ns ns_r)) in *)
  init_env fun_name,Nameset.union ns ns_r

let fv_of_vspec consider_var (VS_aux(vspec,_)) = match vspec with
  | VS_val_spec(ts,id,_,_) ->
     init_env ("val:" ^ (string_of_id id)), snd (fv_of_typschm consider_var mt mt ts)

let rec find_scattered_of name = function
  | [] -> []
  | DEF_scattered (SD_aux(sda,_) as sd):: defs ->
    (match sda with
     | SD_scattered_function(_,_,_,id)
     | SD_scattered_funcl(FCL_aux(FCL_Funcl(id,_,_),_))
     | SD_scattered_unioncl(id,_) ->
       if name = string_of_id id
       then [sd] else []
     | _ -> [])@
    (find_scattered_of name defs)
  | _::defs -> find_scattered_of name defs

let rec fv_of_scattered consider_var consider_scatter_as_one all_defs (SD_aux(sd,_)) = match sd with
  | SD_scattered_function(_,tannot_opt,_,id) ->
    let b,ns = (match tannot_opt with
        | Typ_annot_opt_aux(Typ_annot_opt_some (typq, typ),_) ->
          let bindings = if consider_var then typq_bindings typq else mt in
          bindings, fv_of_typ consider_var bindings mt typ
        | Typ_annot_opt_aux(Typ_annot_opt_none, _) ->
          mt, mt) in
    init_env (string_of_id id),ns
  | SD_scattered_funcl (FCL_aux(FCL_Funcl(id,pat,exp),_)) ->
    let pat_bs,pat_ns = pat_bindings consider_var mt mt pat in
    let _,exp_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
    let scattered_binds = match pat with
      | P_aux(P_app(pid,_),_) -> init_env ((string_of_id id) ^ "/" ^ (string_of_id pid))
      | _ -> mt in
    scattered_binds, exp_ns
  | SD_scattered_variant (id,_,_) ->
    let name = string_of_id id in
    let uses =
      if consider_scatter_as_one
      then
        let variant_defs = find_scattered_of name all_defs in
        let pieces_uses =
          List.fold_right (fun (binds,uses) all_uses -> Nameset.union uses all_uses)
            (List.map (fv_of_scattered consider_var false []) variant_defs) mt in
        Nameset.remove name pieces_uses
      else mt in
    init_env name, uses
  | SD_scattered_unioncl(id, type_union) ->
    let typ_name = string_of_id id in
    let b = init_env typ_name in
    let (b,r) = typ_variants consider_var b [type_union] in
    (Nameset.remove typ_name b, Nameset.add typ_name r)
  | SD_scattered_end id ->
    let name = string_of_id id in
    let uses = if consider_scatter_as_one
    (*Note: if this is a function ending, the dec is included *)
      then
        let scattered_defs = find_scattered_of name all_defs in
        List.fold_right (fun (binds,uses) all_uses -> Nameset.union (Nameset.union binds uses) all_uses)
          (List.map (fv_of_scattered consider_var false []) scattered_defs) (init_env name)
      else init_env name in
    init_env (name ^ "/end"), uses

let fv_of_rd consider_var (DEC_aux (d,_)) = match d with
  | DEC_reg(t,id) ->
    init_env (string_of_id id), fv_of_typ consider_var mt mt t
  | DEC_alias(id,alias) ->
    init_env (string_of_id id),mt
  | DEC_typ_alias(t,id,alias) ->
    init_env (string_of_id id), mt

let fv_of_def consider_var consider_scatter_as_one all_defs = function
  | DEF_kind kdef -> fv_of_kind_def consider_var kdef
  | DEF_type tdef -> fv_of_type_def consider_var tdef
  | DEF_fundef fdef -> fv_of_fun consider_var fdef
  | DEF_val lebind -> ((fun (b,u,_) -> (b,u)) (fv_of_let consider_var mt mt mt lebind))
  | DEF_spec vspec -> fv_of_vspec consider_var vspec
  | DEF_fixity _ -> mt,mt
  | DEF_overload (id,ids) -> init_env (string_of_id id), List.fold_left (fun ns id -> Nameset.add (string_of_id id) ns) mt ids
  | DEF_default def -> mt,mt
  | DEF_scattered sdef -> fv_of_scattered consider_var consider_scatter_as_one all_defs sdef
  | DEF_reg_dec rdec -> fv_of_rd consider_var rdec
  | DEF_comm _ -> mt,mt

let group_defs consider_scatter_as_one (Ast.Defs defs) =
  List.map (fun d -> (fv_of_def false consider_scatter_as_one defs d,d)) defs

(*******************************************************************************
 * Reorder defs take 2
*)

(*remove all of ns1 instances from ns2*)
let remove_all ns1 ns2 =
  List.fold_right Nameset.remove (Nameset.elements ns1) ns2

let remove_from_all_uses bs dbts =
  List.map (fun ((b,uses),d) -> (b,remove_all bs uses),d) dbts

let remove_local_or_lib_vars dbts =
  let bound_in_dbts = List.fold_right (fun ((b,_),_) bounds -> Nameset.union b bounds) dbts mt in
  let is_bound_in_defs s = Nameset.mem s bound_in_dbts in
  let rec remove_from_uses = function
    | [] -> []
    | ((b,uses),d)::defs ->
      ((b,(Nameset.filter is_bound_in_defs uses)),d)::remove_from_uses defs in
  remove_from_uses dbts

let compare_dbts ((_,u1),_) ((_,u2),_) = Pervasives.compare (Nameset.cardinal u1) (Nameset.cardinal u2)

let rec print_dependencies orig_queue work_queue names =
  match work_queue with
  | [] -> ()
  | ((binds,uses),_)::wq ->
    (if not(Nameset.is_empty(Nameset.inter names binds))
     then ((Printf.eprintf "binds of %s has uses of %s\n" (set_to_string binds) (set_to_string uses));
           print_dependencies orig_queue orig_queue uses));
    print_dependencies orig_queue wq names

let merge_mutrecs defs =
  let merge_aux ((binds', uses'), def) ((binds, uses), fundefs) =
    let fundefs = match def with
      | DEF_fundef fundef -> fundef :: fundefs
      | DEF_internal_mutrec fundefs' -> fundefs' @ fundefs
      | _ ->
        (* let _ = Pretty_print_sail2.pp_defs stderr (Defs [def]) in *)
        raise (Reporting_basic.err_unreachable (def_loc def)
          "Trying to merge non-function definition with mutually recursive functions") in
    (* let _ = Printf.eprintf " - Merging %s (using %s)\n" (set_to_string binds') (set_to_string uses') in *)
    ((Nameset.union binds' binds, Nameset.union uses' uses), fundefs) in
  let ((binds, uses), fundefs) = List.fold_right merge_aux defs ((mt, mt), []) in
  ((binds, uses), DEF_internal_mutrec fundefs)

let rec topological_sort work_queue defs =
  match work_queue with
  | [] -> List.rev defs
  | ((binds,uses),def)::wq ->
    (*Assumes work queue given in sorted order, invariant mantained on appropriate recursive calls*)
    if (Nameset.cardinal uses = 0)
    then (*let _ = Printf.eprintf "Adding def that binds %s to definitions\n" (set_to_string binds) in*)
      topological_sort (remove_from_all_uses binds wq) (def::defs)
    else if not(Nameset.is_empty(Nameset.inter binds uses))
    then topological_sort (((binds,(remove_all binds uses)),def)::wq) defs
    else
      match List.stable_sort compare_dbts work_queue with (*We wait to sort until there are no 0 dependency nodes on top*)
      | [] -> failwith "sort shrunk the list???"
      | (((n,uses),def)::rest) as wq ->
        if (Nameset.cardinal uses = 0)
        then topological_sort wq defs
        else
          let _ = Printf.eprintf "Merging (potentially) mutually recursive definitions %s and %s\n" (set_to_string n) (set_to_string uses) in
          let is_used ((binds', uses'), def') = not(Nameset.is_empty(Nameset.inter binds' uses)) in
          let (used, rest) = List.partition is_used rest in
          let wq = merge_mutrecs (((n,uses),def)::used) :: rest in
          topological_sort wq defs

let rec add_to_partial_order ((binds,uses),def) = function
  | [] ->
(*    let _ = Printf.eprintf "add_to_partial_order for def with bindings %s, uses %s.\n Eol case.\n" (set_to_string binds) (set_to_string uses) in*)
    [(binds,uses),def]
  | (((bf,uf),deff)::defs as full_defs) ->
    (*let _ = Printf.eprintf "add_to_partial_order for def with bindings %s, uses %s.\n None eol case. With first def binding %s, uses %s\n" (set_to_string binds) (set_to_string uses) (set_to_string bf) (set_to_string uf) in*)
    if Nameset.is_empty uses
    then ((binds,uses),def)::full_defs
    else if Nameset.subset binds uf (*deff relies on def, so def must be defined first*)
    then ((binds,uses),def)::((bf,(remove_all binds uf)),deff)::defs
    else if Nameset.subset bf uses (*def relies at least on deff, but maybe more, push in*)
    then ((bf,uf),deff)::(add_to_partial_order ((binds,(remove_all bf uses)),def) defs)
    else (*These two are unrelated but new def might need to go further in*)
      ((bf,uf),deff)::(add_to_partial_order ((binds,uses),def) defs)

let rec gather_defs name already_included def_bind_triples =
  match def_bind_triples with
  | [] -> [],already_included,mt
  | ((binds,uses),def)::def_bind_triples ->
    let (defs,already_included,requires) = gather_defs name already_included def_bind_triples in
    let bound_names = Nameset.elements binds in
    if List.mem name already_included || List.exists (fun b -> List.mem b already_included) bound_names 
    then (defs,already_included,requires)
    else
      let uses = List.fold_right Nameset.remove already_included uses in
      if Nameset.mem name binds
      then (def::defs,(bound_names@already_included), Nameset.remove name (Nameset.union uses requires))
      else (defs,already_included,requires)

let rec gather_all names already_included def_bind_triples =
  let rec gather ns already_included defs reqs = match ns with
    | [] -> defs,already_included,reqs
    | name::ns ->
      if List.mem name already_included
      then gather ns already_included defs (Nameset.remove name reqs)
      else
        let (new_defs,already_included,new_reqs) = gather_defs name already_included def_bind_triples in
        gather ns already_included (new_defs@defs) (Nameset.remove name (Nameset.union new_reqs reqs))
  in
  let (defs,already_included,reqs) = gather names already_included [] mt in
  if Nameset.is_empty reqs
  then defs
  else (gather_all (Nameset.elements reqs) already_included def_bind_triples)@defs
    
let restrict_defs defs name_list =
  let defsno = gather_all name_list [] (group_defs false defs) in
  let rdbts = group_defs true (Defs defsno) in
  (*let partial_order =
    List.fold_left (fun po d -> add_to_partial_order d po) [] rdbts in
    let defs = List.map snd partial_order in*)
  let defs = topological_sort (List.sort compare_dbts (remove_local_or_lib_vars rdbts)) [] in
  Defs defs


let top_sort_defs defs =
  let rdbts = group_defs true defs in
  let defs = topological_sort (List.stable_sort compare_dbts (remove_local_or_lib_vars rdbts)) [] in
  Defs defs
