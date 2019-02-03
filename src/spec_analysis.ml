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
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
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
open Extra_pervasives

module Nameset = Set.Make(String)

let mt = Nameset.empty

let set_to_string n = 
  let rec list_to_string = function
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ ", " ^ list_to_string ns in
  list_to_string (Nameset.elements n)


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


let rec free_type_names_t consider_var (Typ_aux (t, l)) = match t with
  | Typ_var name -> if consider_var then Nameset.add (string_of_kid name) mt else mt
  | Typ_id name -> Nameset.add (string_of_id name) mt
  | Typ_fn (arg_typs,ret_typ,_) ->
     List.fold_left Nameset.union (free_type_names_t consider_var ret_typ) (List.map (free_type_names_t consider_var) arg_typs)
  | Typ_bidir (t1, t2) -> Nameset.union (free_type_names_t consider_var t1)
                                        (free_type_names_t consider_var t2)
  | Typ_tup ts -> free_type_names_ts consider_var ts
  | Typ_app (name,targs) -> Nameset.add (string_of_id name) (free_type_names_t_args consider_var targs)
  | Typ_exist (kopts,_,t') -> List.fold_left (fun s kopt -> Nameset.remove (string_of_kid (kopt_kid kopt)) s) (free_type_names_t consider_var t') kopts
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
and free_type_names_ts consider_var ts = nameset_bigunion (List.map (free_type_names_t consider_var) ts)
and free_type_names_maybe_t consider_var = function
  | Some t -> free_type_names_t consider_var t
  | None -> mt
and free_type_names_t_arg consider_var = function
  | A_aux (A_typ t, _) -> free_type_names_t consider_var t
  | _ -> mt
and free_type_names_t_args consider_var targs =
  nameset_bigunion (List.map (free_type_names_t_arg consider_var) targs)


let rec free_type_names_tannot consider_var tannot =
  match Type_check.destruct_tannot tannot with
  | None -> mt
  | Some (_, t, _) -> free_type_names_t consider_var t


let rec fv_of_typ consider_var bound used (Typ_aux (t,l)) : Nameset.t =
  match t with
  | Typ_var (Kid_aux (Var v,l)) ->
    if consider_var
    then conditional_add_typ bound used (Ast.Id_aux (Ast.Id v,l))
    else used
  | Typ_id id -> conditional_add_typ bound used id
  | Typ_fn(arg,ret,_) ->
     fv_of_typ consider_var bound (List.fold_left Nameset.union Nameset.empty (List.map (fv_of_typ consider_var bound used) arg)) ret
  | Typ_bidir(t1, t2) -> fv_of_typ consider_var bound (fv_of_typ consider_var bound used t1) t2 (* TODO FIXME? *)
  | Typ_tup ts -> List.fold_right (fun t n -> fv_of_typ consider_var bound n t) ts used
  | Typ_app(id,targs) ->
     List.fold_right (fun ta n -> fv_of_targ consider_var bound n ta) targs (conditional_add_typ bound used id)
  | Typ_exist (kopts,_,t') ->
     fv_of_typ consider_var
       (List.fold_left (fun b (KOpt_aux (KOpt_kind (_, (Kid_aux (Var v,_))), _)) -> Nameset.add v b) bound kopts)
       used t'
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"

and fv_of_targ consider_var bound used (Ast.A_aux(targ,_)) : Nameset.t = match targ with
  | A_typ t -> fv_of_typ consider_var bound used t
  | A_nexp n -> fv_of_nexp consider_var bound used n
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
    let us = conditional_add_exp bound us (prepend_id "val:" id) in
    list_fv bound us set es
  | E_app_infix(l,id,r) ->
    let us = conditional_add_exp bound used id in
    let us = conditional_add_exp bound us (prepend_id "val:" id) in
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
  | E_record fexps ->
     let used = Nameset.union (free_type_names_tannot consider_var tannot) used in
     List.fold_right
       (fun (FE_aux(FE_Fexp(_,e),_)) (b,u,s) -> fv_of_exp consider_var b u s e) fexps (bound,used,set)
  | E_record_update(e, fexps) ->
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
  | E_var (lexp, exp1, exp2) ->
    let b,u,s = fv_of_lexp consider_var bound used set lexp in
    let _,used,set = fv_of_exp consider_var bound used set exp1 in
    fv_of_exp consider_var b used set exp2
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
  | LEXP_deref exp ->
    fv_of_exp consider_var bound used set exp
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
  | LEXP_vector_concat(args) ->
     List.fold_right
       (fun e (b,u,s) ->
         fv_of_lexp consider_var b u s e) args (bound,used,set)
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
    (fun (Tu_aux(Tu_ty_id(t,id),_)) (b,n) -> Nameset.add (string_of_id id) b, fv_of_typ consider_var b n t)
    tunions
    (bound,mt)

let fv_of_kind_def consider_var (KD_aux(k,_)) = match k with
  | KD_nabbrev(_,id,_,nexp) -> init_env (string_of_id id), fv_of_nexp consider_var mt mt nexp

let fv_of_abbrev consider_var bound used typq typ_arg =
  let ts_bound = if consider_var then typq_bindings typq else mt in
  ts_bound, fv_of_targ consider_var (Nameset.union bound ts_bound) used typ_arg

let fv_of_type_def consider_var (TD_aux(t,_)) = match t with
  | TD_abbrev(id,typq,typ_arg) ->
     init_env (string_of_id id), snd (fv_of_abbrev consider_var mt mt typq typ_arg)
  | TD_record(id,_,typq,tids,_) ->
    let binds = init_env (string_of_id id) in
    let bounds = if consider_var then typq_bindings typq else mt in
    binds, List.fold_right (fun (t,_) n -> fv_of_typ consider_var bounds n t) tids mt
  | TD_variant(id,_,typq,tunions,_) ->
    let bindings = Nameset.add (string_of_id id) (if consider_var then typq_bindings typq else mt) in
    typ_variants consider_var bindings tunions
  | TD_enum(id,_,ids,_) ->
    Nameset.of_list (List.map string_of_id (id::ids)),mt
  | TD_bitfield(id,typ,_) ->
    init_env (string_of_id id), Nameset.empty (* fv_of_typ consider_var mt typ *)

let fv_of_tannot_opt consider_var (Typ_annot_opt_aux (t,_)) =
  match t with
  | Typ_annot_opt_some (typq,typ) ->
    let bindings = if consider_var then typq_bindings typq else mt in
    let free = fv_of_typ consider_var bindings mt typ in
    (bindings,free)
  | Typ_annot_opt_none ->
    (mt, mt)

(*Unlike the other fv, the bound returns are the names bound by the pattern for use in the exp*)
let fv_of_funcl consider_var base_bounds (FCL_aux(FCL_Funcl(id,pexp),l)) =
  match pexp with
  | Pat_aux(Pat_exp (pat,exp),_) ->
     let pat_bs,pat_ns = pat_bindings consider_var base_bounds mt pat in
     let _, exp_ns, exp_sets = fv_of_exp consider_var pat_bs pat_ns mt exp in
     (pat_bs,exp_ns,exp_sets)
  | Pat_aux(Pat_when (pat,guard,exp),_) ->
     let pat_bs,pat_ns = pat_bindings consider_var base_bounds mt pat in
     let bound_g, exp_ns, exp_sets = fv_of_exp consider_var pat_bs pat_ns mt exp in
     let _, exp_ns, exp_sets = fv_of_exp consider_var bound_g exp_ns exp_sets exp in
     (pat_bs,exp_ns,exp_sets)

let fv_of_fun consider_var (FD_aux (FD_function(rec_opt,tannot_opt,_,funcls),_) as fd) =
  let fun_name = match funcls with
    | [] -> failwith "fv_of_fun fell off the end looking for the function name"
    | FCL_aux(FCL_Funcl(id,_),_)::_ -> string_of_id id in
  let base_bounds = match rec_opt with
    (* Current Sail does not require syntax for declaring functions as recursive,
       and type checker does not check whether functions are recursive, so
       just always add a self-dependency of functions on themselves, as well as
       adding dependencies from any specified termination measure further below
    | Rec_aux(Ast.Rec_rec,_) -> init_env fun_name
    | _ -> mt*)
    | _ -> init_env fun_name in
  let base_bounds,ns_r = match tannot_opt with
    | Typ_annot_opt_aux(Typ_annot_opt_some (typq, typ),_) ->
      let bindings = if consider_var then typq_bindings typq else mt in
      let bound = Nameset.union bindings base_bounds in
      bound, fv_of_typ consider_var bound mt typ
    | Typ_annot_opt_aux(Typ_annot_opt_none, _) ->
      base_bounds, mt in
  let ns_measure = match rec_opt with
    | Rec_aux(Rec_measure (pat,exp),_) ->
       let pat_bs,pat_ns = pat_bindings consider_var base_bounds mt pat in
       let _, exp_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
       exp_ns
    | _ -> mt
  in
  let ns = List.fold_right (fun (FCL_aux(FCL_Funcl(_,pexp),_)) ns ->
    match pexp with
    | Pat_aux(Pat_exp (pat,exp),_) ->
       let pat_bs,pat_ns = pat_bindings consider_var base_bounds ns pat in
       let _, exp_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
       exp_ns
    | Pat_aux(Pat_when (pat,guard,exp),_) ->
       let pat_bs,pat_ns = pat_bindings consider_var base_bounds ns pat in
       let guard_bs, guard_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty guard in
       let _, exp_ns,_ = fv_of_exp consider_var guard_bs guard_ns Nameset.empty exp in
       exp_ns
  ) funcls mt in
  let ns_vs = init_env ("val:" ^ (string_of_id (id_of_fundef fd))) in
  (* let _ = Printf.eprintf "Function %s uses %s\n" fun_name (set_to_string (Nameset.union ns ns_r)) in *)
  init_env fun_name, Nameset.union ns_vs (Nameset.union ns (Nameset.union ns_r ns_measure))

let fv_of_vspec consider_var (VS_aux(vspec,_)) = match vspec with
  | VS_val_spec(ts,id,_,_) ->
     init_env ("val:" ^ (string_of_id id)), snd (fv_of_typschm consider_var mt mt ts)

let rec find_scattered_of name = function
  | [] -> []
  | DEF_scattered (SD_aux(sda,_) as sd):: defs ->
    (match sda with
     | SD_function(_,_,_,id)
     | SD_funcl(FCL_aux(FCL_Funcl(id,_),_))
     | SD_unioncl(id,_) ->
       if name = string_of_id id
       then [sd] else []
     | _ -> [])@
    (find_scattered_of name defs)
  | _::defs -> find_scattered_of name defs

let rec fv_of_scattered consider_var consider_scatter_as_one all_defs (SD_aux(sd,(l, _))) = match sd with
  | SD_function(_,tannot_opt,_,id) ->
    let b,ns = (match tannot_opt with
        | Typ_annot_opt_aux(Typ_annot_opt_some (typq, typ),_) ->
          let bindings = if consider_var then typq_bindings typq else mt in
          bindings, fv_of_typ consider_var bindings mt typ
        | Typ_annot_opt_aux(Typ_annot_opt_none, _) ->
          mt, mt) in
    init_env (string_of_id id),ns
  | SD_funcl (FCL_aux(FCL_Funcl(id,pexp),_)) ->
     begin
       match pexp with
       | Pat_aux(Pat_exp (pat,exp),_) ->
          let pat_bs,pat_ns = pat_bindings consider_var mt mt pat in
          let _,exp_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
          let scattered_binds = match pat with
            | P_aux(P_app(pid,_),_) -> init_env ((string_of_id id) ^ "/" ^ (string_of_id pid))
            | _ -> mt in
          scattered_binds, exp_ns
       | Pat_aux(Pat_when (pat,guard,exp),_) ->
          let pat_bs,pat_ns = pat_bindings consider_var mt mt pat in
          let guard_bs, guard_ns,_ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty guard in
          let _, exp_ns,_ = fv_of_exp consider_var guard_bs guard_ns Nameset.empty exp in
          let scattered_binds = match pat with
            | P_aux(P_app(pid,_),_) -> init_env ((string_of_id id) ^ "/" ^ (string_of_id pid))
            | _ -> mt in
          scattered_binds, exp_ns
     end
  | SD_variant (id,_,_) ->
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
  | SD_unioncl(id, type_union) ->
    let typ_name = string_of_id id in
    let b = init_env typ_name in
    let (b,r) = typ_variants consider_var b [type_union] in
    (Nameset.remove typ_name b, Nameset.add typ_name r)
  | SD_end id ->
    let name = string_of_id id in
    let uses = if consider_scatter_as_one
    (*Note: if this is a function ending, the dec is included *)
      then
        let scattered_defs = find_scattered_of name all_defs in
        List.fold_right (fun (binds,uses) all_uses -> Nameset.union (Nameset.union binds uses) all_uses)
          (List.map (fv_of_scattered consider_var false []) scattered_defs) (init_env name)
      else init_env name in
    init_env (name ^ "/end"), uses
  | _ -> raise (Reporting.err_unreachable l __POS__ "Tried to find free variables for scattered mapping clause")

let fv_of_rd consider_var (DEC_aux (d, annot)) =
  (* When we get the free variables of a register, we have to ensure
     that we expand all synonyms so we can pick up dependencies with
     undefined_type function, even when type is indirected through a
     synonym. *)
  let open Type_check in
  let env = env_of_annot annot in
  match d with
  | DEC_reg(t, id) ->
     let t' = Env.expand_synonyms env t in
     init_env (string_of_id id),
     Nameset.union (fv_of_typ consider_var mt mt t) (fv_of_typ consider_var mt mt t')
  | DEC_config(id, t, exp) ->
     let t' = Env.expand_synonyms env t in
     init_env (string_of_id id),
     Nameset.union (fv_of_typ consider_var mt mt t) (fv_of_typ consider_var mt mt t')
  | DEC_alias(id, alias) ->
     init_env (string_of_id id), mt
  | DEC_typ_alias(t, id, alias) ->
     init_env (string_of_id id), mt

let fv_of_def consider_var consider_scatter_as_one all_defs = function
  | DEF_kind kdef -> fv_of_kind_def consider_var kdef
  | DEF_type tdef -> fv_of_type_def consider_var tdef
  | DEF_fundef fdef -> fv_of_fun consider_var fdef
  | DEF_mapdef mdef -> mt,mt (* fv_of_map consider_var mdef *)
  | DEF_val lebind -> ((fun (b,u,_) -> (b,u)) (fv_of_let consider_var mt mt mt lebind))
  | DEF_spec vspec -> fv_of_vspec consider_var vspec
  | DEF_fixity _ -> mt,mt
  | DEF_overload (id,ids) ->
     init_env (string_of_id id),
     List.fold_left (fun ns id -> Nameset.add ("val:" ^ string_of_id id) ns) mt ids
  | DEF_default def -> mt,mt
  | DEF_internal_mutrec fdefs ->
     let fvs = List.map (fv_of_fun consider_var) fdefs in
     List.fold_left Nameset.union Nameset.empty (List.map fst fvs),
     List.fold_left Nameset.union Nameset.empty (List.map snd fvs)
  | DEF_scattered sdef -> fv_of_scattered consider_var consider_scatter_as_one all_defs sdef
  | DEF_reg_dec rdec -> fv_of_rd consider_var rdec
  | DEF_pragma _ -> mt,mt
  | DEF_measure _ -> mt,mt (* currently removed beforehand *)

let group_defs consider_scatter_as_one (Ast.Defs defs) =
  List.map (fun d -> (fv_of_def false consider_scatter_as_one defs d,d)) defs


(*
 *  Sorting definitions, take 3
 *)

module Namemap = Map.Make(String)
(* Nodes are labeled with strings.  A graph is represented as a map associating
   each node with its sucessors *)
type graph = Nameset.t Namemap.t
type node_idx = { index : int; root : int }

(* Find strongly connected components using Tarjan's algorithm.
   This algorithm also returns a topological sorting of the graph components. *)
let scc ?(original_order : string list option) (g : graph) =
  let components = ref [] in
  let index = ref 0 in

  let stack = ref [] in
  let push v = (stack := v :: !stack) in
  let pop () =
    begin
      let v = List.hd !stack in
      stack := List.tl !stack;
      v
    end
  in

  let node_indices = Hashtbl.create (Namemap.cardinal g) in
  let get_index v = (Hashtbl.find node_indices v).index in
  let get_root v = (Hashtbl.find node_indices v).root in
  let set_root v r =
    Hashtbl.replace node_indices v { (Hashtbl.find node_indices v) with root = r } in

  let rec visit_node v =
    begin
      Hashtbl.add node_indices v { index = !index; root = !index };
      index := !index + 1;
      push v;
      if Namemap.mem v g then Nameset.iter (visit_edge v) (Namemap.find v g);
      if get_root v = get_index v then (* v is the root of a SCC *)
        begin
          let component = ref [] in
          let finished = ref false in
          while not !finished do
            let w = pop () in
            component := w :: !component;
            if String.compare v w = 0 then finished := true;
          done;
          components := !component :: !components;
        end
    end
  and visit_edge v w =
    if not (Hashtbl.mem node_indices w) then
      begin
        visit_node w;
        if Hashtbl.mem node_indices w then set_root v (min (get_root v) (get_root w));
      end else begin
        if List.mem w !stack then set_root v (min (get_root v) (get_index w))
      end
  in

  let nodes = match original_order with
    | Some nodes -> nodes
    | None -> List.map fst (Namemap.bindings g)
  in
  List.iter (fun v -> if not (Hashtbl.mem node_indices v) then visit_node v) nodes;
  List.rev !components

let add_def_to_graph (prelude, original_order, defset, graph) d =
  let bound, used = fv_of_def false true [] d in
  let used = match d with
    | DEF_reg_dec _ ->
       (* For a register, we need to ensure that any undefined_type
          functions for types used by the register are placed before
          the register declaration. *)
       let undefineds = Nameset.map (fun name -> "undefined_" ^ name) used in
       Nameset.union undefineds used
    | _ -> used
  in
  try
    (* A definition may bind multiple identifiers, e.g. "let (x, y) = ...".
       We add all identifiers to the dependency graph as a cycle.  The actual
       definition is attached to only one of the identifiers, so it will not
       be duplicated in the final output. *)
    let id = Nameset.choose bound in
    let other_ids = Nameset.remove id bound in
    let graph_id = Namemap.add id (Nameset.union used other_ids) graph in
    let add_other_node id' g = Namemap.add id' (Nameset.singleton id) g in
    prelude,
    original_order @ [id],
    Namemap.add id d defset,
    Nameset.fold add_other_node other_ids graph_id
  with
  | Not_found ->
     (* Some definitions do not bind any identifiers at all.  This *should*
        only happen for default bitvector order declarations, operator fixity
        declarations, and comments.  The sorting does not (currently) attempt
        to preserve the positions of these AST nodes; they are collected
        separately and placed at the beginning of the output.  Comments are
        currently ignored by the Lem and OCaml backends, anyway.  For
        default order and fixity declarations, this means that specifications
        currently have to assume those declarations are moved to the
        beginning when using a backend that requires topological sorting. *)
     prelude @ [d], original_order, defset, graph

let print_dot graph component : unit =
  match component with
  | root :: _ ->
     prerr_endline ("// Dependency cycle including " ^ root);
     prerr_endline ("digraph cycle_" ^ root ^ " {");
     List.iter (fun caller ->
       let print_edge callee = prerr_endline ("  \"" ^ caller ^ "\" -> \"" ^ callee ^ "\";") in
       Namemap.find caller graph
       |> Nameset.filter (fun id -> List.mem id component)
       |> Nameset.iter print_edge) component;
     prerr_endline "}"
  | [] -> ()

let def_of_component graph defset comp =
  let get_def id = if Namemap.mem id defset then [Namemap.find id defset] else [] in
  match List.concat (List.map get_def comp) with
  | [] -> []
  | [def] -> [def]
  | (def :: _) as defs ->
     let get_fundefs = function
       | DEF_fundef fundef -> [fundef]
       | DEF_internal_mutrec fundefs -> fundefs
       | _ ->
          raise (Reporting.err_unreachable (def_loc def) __POS__
            "Trying to merge non-function definition with mutually recursive functions") in
     let fundefs = List.concat (List.map get_fundefs defs) in
     print_dot graph (List.map (fun fd -> string_of_id (id_of_fundef fd)) fundefs);
     [DEF_internal_mutrec fundefs]

let top_sort_defs (Defs defs) =
  let prelude, original_order, defset, graph =
    List.fold_left add_def_to_graph ([], [], Namemap.empty, Namemap.empty) defs in
  let components = scc ~original_order:original_order graph in
  Defs (prelude @ List.concat (List.map (def_of_component graph defset) components))
