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
module Big_int = Nat_big_num

(* See mli file for details on what these flags do *)
let opt_undefined_gen = ref false
let opt_magic_hash = ref false
let opt_enum_casts = ref false

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

let rec kind_to_string kind = match kind.k with
  | K_Nat -> "Nat"
  | K_Typ -> "Type"
  | K_Ord -> "Order"
  | K_Efct -> "Effect"
  | K_infer -> "Infer"
  | K_Val -> "Val"
  | K_Lam (kinds,kind) -> "Lam [" ^ string_of_list ", " kind_to_string kinds ^ "] -> " ^ (kind_to_string kind)

(*Envs is a tuple of used names (currently unused), map from id to kind, default order for vector types and literal vectors *)
type envs = Nameset.t * kind Envmap.t * order
type 'a envs_out = 'a * envs

let id_to_string (Id_aux(id,l)) =
  match id with | Id(x) | DeIid(x) -> x

let var_to_string (Kid_aux(Var v,l)) = v

let typquant_to_quantkinds k_env typquant =
  match typquant with
  | TypQ_aux(tq,_) ->
    (match tq with
    | TypQ_no_forall -> []
    | TypQ_tq(qlist) ->
      List.fold_right
        (fun (QI_aux(qi,_)) rst ->
          match qi with
          | QI_const _ -> rst
          | QI_id(ki) -> begin
            match ki with
            | KOpt_aux(KOpt_none(v),l) | KOpt_aux(KOpt_kind(_,v),l) ->
              (match Envmap.apply k_env (var_to_string v) with
              | Some(typ) -> typ::rst
              | None -> raise (Reporting_basic.err_unreachable l "Envmap didn't get an entry during typschm processing"))
          end)
        qlist
        [])

let typ_error l msg opt_id opt_var opt_kind =
  raise (Reporting_basic.err_typ
           l
           (msg ^
              (match opt_id, opt_var, opt_kind with
              | Some(id),None,Some(kind) -> (id_to_string id) ^ " of " ^ (kind_to_string kind)
              | Some(id),None,None -> ": " ^ (id_to_string id)
              | None,Some(v),Some(kind) -> (var_to_string v) ^ " of " ^ (kind_to_string kind)
              | None,Some(v),None -> ": " ^ (var_to_string v)
              | None,None,Some(kind) -> " " ^ (kind_to_string kind)
              | _ -> "")))

let string_of_parse_id_aux = function
  | Parse_ast.Id v -> v
  | Parse_ast.DeIid v -> v

let string_contains str char =
  try (ignore (String.index str char); true) with
  | Not_found -> false

let to_ast_id (Parse_ast.Id_aux(id, l)) =
  if string_contains (string_of_parse_id_aux id) '#' && not (!opt_magic_hash)
  then typ_error l "Identifier contains hash character" None None None
  else Id_aux ((match id with
                | Parse_ast.Id(x) -> Id(x)
                | Parse_ast.DeIid(x) -> DeIid(x)),
               l)

let to_ast_var (Parse_ast.Kid_aux(Parse_ast.Var v,l)) = Kid_aux(Var v,l)

let to_ast_base_kind (Parse_ast.BK_aux(k,l')) =
  match k with
  | Parse_ast.BK_type -> BK_aux(BK_type,l'), { k = K_Typ}
  | Parse_ast.BK_nat -> BK_aux(BK_nat,l'), { k = K_Nat }
  | Parse_ast.BK_order -> BK_aux(BK_order,l'), { k = K_Ord }

let to_ast_kind (k_env : kind Envmap.t) (Parse_ast.K_aux(Parse_ast.K_kind(klst),l)) : (Ast.kind * kind) =
  match klst with
  | [] -> raise (Reporting_basic.err_unreachable l "Kind with empty kindlist encountered")
  | [k] -> let k_ast,k_typ = to_ast_base_kind k in
           K_aux(K_kind([k_ast]),l), k_typ
  | ks -> let k_pairs = List.map to_ast_base_kind ks in
          let reverse_typs = List.rev (List.map snd k_pairs) in
          let ret,args = List.hd reverse_typs, List.rev (List.tl reverse_typs) in
          match ret.k with
          | K_Typ -> K_aux(K_kind(List.map fst k_pairs), l), { k = K_Lam(args,ret) }
          | _ -> typ_error l "Type constructor must have an -> kind ending in Type" None None None

let rec to_ast_typ (k_env : kind Envmap.t) (def_ord : order) (t: Parse_ast.atyp) : Ast.typ =
(*  let _ = Printf.eprintf "to_ast_typ\n" in*)
  match t with
  | Parse_ast.ATyp_aux(t,l) ->
    Typ_aux( (match t with
              | Parse_ast.ATyp_id(id) -> Typ_id (to_ast_id id)
              | Parse_ast.ATyp_var(v) ->
                let v = to_ast_var v in
                let mk = Envmap.apply k_env (var_to_string v) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Typ -> Typ_var v
                              | K_infer -> k.k <- K_Typ; Typ_var v
                              | _ -> typ_error l "Required a variable with kind Type, encountered " None (Some v) (Some k))
                | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
              | Parse_ast.ATyp_fn(arg,ret,efct) -> Typ_fn( (to_ast_typ k_env def_ord arg),
                                                           (to_ast_typ k_env def_ord ret),
                                                           (to_ast_effects k_env efct))
              | Parse_ast.ATyp_tup(typs) -> Typ_tup( List.map (to_ast_typ k_env def_ord) typs)
	      | Parse_ast.ATyp_app(Parse_ast.Id_aux(Parse_ast.Id "vector_sugar_tb",il), [ b; r; ord ; ti]) ->
		let make_r bot top =
		  match bot,top with
		    | Parse_ast.ATyp_aux(Parse_ast.ATyp_constant b,_),Parse_ast.ATyp_aux(Parse_ast.ATyp_constant t,l) ->
                      Parse_ast.ATyp_aux(Parse_ast.ATyp_constant (Big_int.add (Big_int.sub t b) (Big_int.of_int 1)),l)
		    | bot,(Parse_ast.ATyp_aux(_,l) as top) ->
		      Parse_ast.ATyp_aux((Parse_ast.ATyp_sum
					    ((Parse_ast.ATyp_aux
						(Parse_ast.ATyp_sum (top,
                                                                     Parse_ast.ATyp_aux(Parse_ast.ATyp_constant (Big_int.of_int 1),Parse_ast.Unknown)),
						 Parse_ast.Unknown)),
					  (Parse_ast.ATyp_aux ((Parse_ast.ATyp_neg bot),Parse_ast.Unknown)))), l) in
		let base = to_ast_nexp k_env b in
		let rise = match def_ord with
		  | Ord_aux(Ord_inc,dl) ->  to_ast_nexp k_env (make_r b r)
		  | Ord_aux(Ord_dec,dl) ->  to_ast_nexp k_env (make_r r b)
		  | _ -> raise (Reporting_basic.err_unreachable l "Default order not inc or dec") in
		Typ_app(Id_aux(Id "vector",il),
			[Typ_arg_aux (Typ_arg_nexp base,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_nexp rise,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_order def_ord,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_typ (to_ast_typ k_env def_ord ti), Parse_ast.Unknown);])
	      | Parse_ast.ATyp_app(Parse_ast.Id_aux(Parse_ast.Id "vector_sugar_r",il), [b;r;ord;ti]) ->
		let make_sub_one t =
		  match t with
                    | Parse_ast.ATyp_aux(Parse_ast.ATyp_constant t,_) -> Parse_ast.ATyp_aux(Parse_ast.ATyp_constant (Big_int.sub t (Big_int.of_int 1)),l)
		    | t -> (Parse_ast.ATyp_aux
                              (Parse_ast.ATyp_sum (t, Parse_ast.ATyp_aux(Parse_ast.ATyp_constant (Big_int.negate (Big_int.of_int 1)),Parse_ast.Unknown)),
			       Parse_ast.Unknown)) in
		let (base,rise) = match def_ord with
		  | Ord_aux(Ord_inc,dl) -> (to_ast_nexp k_env b), (to_ast_nexp k_env r)
		  | Ord_aux(Ord_dec,dl) -> (to_ast_nexp k_env (make_sub_one r)), (to_ast_nexp k_env r)
		  | _ -> raise (Reporting_basic.err_unreachable l "Default order not inc or dec") in
		Typ_app(Id_aux(Id "vector",il),
			[Typ_arg_aux (Typ_arg_nexp base,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_nexp rise,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_order def_ord,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_typ (to_ast_typ k_env def_ord ti), Parse_ast.Unknown);])
              | Parse_ast.ATyp_app(pid,typs) ->
                  let id = to_ast_id pid in
                  let k = Envmap.apply k_env (id_to_string id) in
                  (match k with
                  | Some({k = K_Lam(args,t)}) ->
		    if ((List.length args) = (List.length typs))
		      then
		      Typ_app(id,(List.map2 (fun k a -> (to_ast_typ_arg k_env def_ord k a)) args typs))
		    else typ_error l "Type constructor given incorrect number of arguments" (Some id) None None
                  | None -> typ_error l "Required a type constructor, encountered an unbound identifier" (Some id) None None
                  | _ -> typ_error l "Required a type constructor, encountered a base kind variable" (Some id) None None)
              | Parse_ast.ATyp_exist (kids, nc, atyp) ->
                 let kids = List.map to_ast_var kids in
                 let k_env = List.fold_left Envmap.insert k_env (List.map (fun kid -> (var_to_string kid, {k=K_Nat})) kids) in
                 let exist_typ = to_ast_typ k_env def_ord atyp in
                 Typ_exist (kids, to_ast_nexp_constraint k_env nc, exist_typ)
              | _ -> typ_error l "Required an item of kind Type, encountered an illegal form for this kind" None None None
    ), l)

and to_ast_nexp (k_env : kind Envmap.t) (n: Parse_ast.atyp) : Ast.nexp =
  match n with
  | Parse_ast.ATyp_aux(t,l) ->
    (match t with
     | Parse_ast.ATyp_id i -> Nexp_aux (Nexp_id (to_ast_id i), l)
     | Parse_ast.ATyp_var v -> Nexp_aux (Nexp_var (to_ast_var v), l)
     | Parse_ast.ATyp_constant i -> Nexp_aux (Nexp_constant i, l)
     | Parse_ast.ATyp_sum (t1, t2) ->
        let n1 = to_ast_nexp k_env t1 in
        let n2 = to_ast_nexp k_env t2 in
        Nexp_aux (Nexp_sum (n1, n2), l)
     | Parse_ast.ATyp_exp t1 -> Nexp_aux(Nexp_exp(to_ast_nexp k_env t1),l)
     | Parse_ast.ATyp_neg t1 -> Nexp_aux(Nexp_neg(to_ast_nexp k_env t1),l)
     | Parse_ast.ATyp_times (t1, t2) ->
        let n1 = to_ast_nexp k_env t1 in
        let n2 = to_ast_nexp k_env t2 in
        Nexp_aux (Nexp_times (n1, n2), l)
     | Parse_ast.ATyp_minus (t1, t2) ->
        let n1 = to_ast_nexp k_env t1 in
        let n2 = to_ast_nexp k_env t2 in
        Nexp_aux (Nexp_minus (n1, n2), l)
     | Parse_ast.ATyp_app (id, ts) ->
        let nexps = List.map (to_ast_nexp k_env) ts in
        Nexp_aux (Nexp_app (to_ast_id id, nexps), l)
     | _ -> typ_error l "Required an item of kind Nat, encountered an illegal form for this kind" None None None)

and to_ast_order (k_env : kind Envmap.t) (def_ord : order) (o: Parse_ast.atyp) : Ast.order =
  match o with
  | Parse_ast.ATyp_aux(t,l) ->
    (match t with
      | Parse_ast.ATyp_var(v) ->
        let v = to_ast_var v in
        let mk = Envmap.apply k_env (var_to_string v) in
        (match mk with
          | Some(k) -> (match k.k with
              | K_Ord -> Ord_aux(Ord_var v, l)
              | K_infer -> k.k <- K_Ord; Ord_aux(Ord_var v,l)
              | _ -> typ_error l "Required a variable with kind Order, encountered " None (Some v) (Some k))
          | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
      | Parse_ast.ATyp_inc -> Ord_aux(Ord_inc,l)
      | Parse_ast.ATyp_dec -> Ord_aux(Ord_dec,l)
      | Parse_ast.ATyp_default_ord -> def_ord
      | _ -> typ_error l "Requred an item of kind Order, encountered an illegal form for this kind" None None None
    )

and to_ast_effects (k_env : kind Envmap.t) (e : Parse_ast.atyp) : Ast.effect =
  match e with
  | Parse_ast.ATyp_aux(t,l) ->
    Effect_aux( (match t with
               | Parse_ast.ATyp_var(v) ->
                let v = to_ast_var v in
                let mk = Envmap.apply k_env (var_to_string v) in
                (match mk with
                | Some k -> typ_error l "Required a variable with kind Effect, encountered " None (Some v) (Some k)
                | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
               | Parse_ast.ATyp_set(effects) ->
                 Effect_set( List.map
                             (fun efct -> match efct with
                             | Parse_ast.BE_aux(e,l) ->
                               BE_aux((match e with
                               | Parse_ast.BE_barr   -> BE_barr
                               | Parse_ast.BE_rreg   -> BE_rreg
                               | Parse_ast.BE_wreg   -> BE_wreg
                               | Parse_ast.BE_rmem   -> BE_rmem
                               | Parse_ast.BE_rmemt  -> BE_rmemt
                               | Parse_ast.BE_wmem   -> BE_wmem
			       | Parse_ast.BE_wmv    -> BE_wmv
			       | Parse_ast.BE_wmvt   -> BE_wmvt
			       | Parse_ast.BE_eamem  -> BE_eamem
			       | Parse_ast.BE_exmem  -> BE_exmem
			       | Parse_ast.BE_depend -> BE_depend
                               | Parse_ast.BE_undef  -> BE_undef
                               | Parse_ast.BE_unspec -> BE_unspec
                               | Parse_ast.BE_nondet -> BE_nondet
                               | Parse_ast.BE_escape -> BE_escape),l))
                             effects)
               | _ -> typ_error l "Required an item of kind Effects, encountered an illegal form for this kind" None None None
    ), l)

and to_ast_typ_arg (k_env : kind Envmap.t) (def_ord : order) (kind : kind) (arg : Parse_ast.atyp) : Ast.typ_arg =
  let l = (match arg with Parse_ast.ATyp_aux(_,l) -> l) in
  Typ_arg_aux (
    (match kind.k with
    | K_Typ -> Typ_arg_typ (to_ast_typ k_env def_ord arg)
    | K_Nat  -> Typ_arg_nexp (to_ast_nexp k_env arg)
    | K_Ord -> Typ_arg_order (to_ast_order k_env def_ord arg)
    | _ -> raise (Reporting_basic.err_unreachable l ("To_ast_typ_arg received Lam kind or infer kind: " ^ kind_to_string kind))),
    l)

and to_ast_nexp_constraint (k_env : kind Envmap.t) (c : Parse_ast.n_constraint) : n_constraint =
  match c with
  | Parse_ast.NC_aux(nc,l) ->
    NC_aux( (match nc with
             | Parse_ast.NC_equal(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_equal(n1,n2)
             | Parse_ast.NC_not_equal(t1,t2) ->
                let n1 = to_ast_nexp k_env t1 in
                let n2 = to_ast_nexp k_env t2 in
                NC_not_equal(n1,n2)
             | Parse_ast.NC_bounded_ge(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_bounded_ge(n1,n2)
             | Parse_ast.NC_bounded_le(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_bounded_le(n1,n2)
             | Parse_ast.NC_set(id,bounds) ->
                NC_set(to_ast_var id, bounds)
             | Parse_ast.NC_or (nc1, nc2) ->
                NC_or (to_ast_nexp_constraint k_env nc1, to_ast_nexp_constraint k_env nc2)
             | Parse_ast.NC_and (nc1, nc2) ->
                NC_and (to_ast_nexp_constraint k_env nc1, to_ast_nexp_constraint k_env nc2)
             | Parse_ast.NC_true -> NC_true
             | Parse_ast.NC_false -> NC_false
    ), l)

(* Transforms a typquant while building first the kind environment of declared variables, and also the kind environment in context *)
let to_ast_typquant (k_env: kind Envmap.t) (tq : Parse_ast.typquant) : typquant * kind Envmap.t * kind Envmap.t =
  let opt_kind_to_ast k_env local_names local_env (Parse_ast.KOpt_aux(ki,l)) =
    let v, key, kind, ktyp =
      match ki with
      | Parse_ast.KOpt_none(v) ->
	let v = to_ast_var v in
	let key = var_to_string v in
	let kind,ktyp = if (Envmap.in_dom key k_env) then None,(Envmap.apply k_env key) else None,(Some{ k = K_infer }) in
	v,key,kind, ktyp
      | Parse_ast.KOpt_kind(k,v) ->
	let v = to_ast_var v in
	let key = var_to_string v in
	let kind,ktyp = to_ast_kind k_env k in
	v,key,Some(kind),Some(ktyp)
    in
    if (Nameset.mem key local_names)
    then typ_error l "Encountered duplicate name in type scheme" None (Some v) None
    else
      let local_names = Nameset.add key local_names in
      let kopt,k_env,k_env_local = (match kind,ktyp with
        | Some(k),Some(kt) -> KOpt_kind(k,v), (Envmap.insert k_env (key,kt)), (Envmap.insert local_env (key,kt))
	| None, Some(kt) -> KOpt_none(v), (Envmap.insert k_env (key,kt)), (Envmap.insert local_env (key,kt))
	| _ -> raise (Reporting_basic.err_unreachable l "Envmap in dom is true but apply gives None")) in
      KOpt_aux(kopt,l),k_env,local_names,k_env_local
  in
  match tq with
  | Parse_ast.TypQ_aux(tqa,l) ->
    (match tqa with
    | Parse_ast.TypQ_no_forall -> TypQ_aux(TypQ_no_forall,l), k_env, Envmap.empty
    | Parse_ast.TypQ_tq(qlist) ->
      let rec to_ast_q_items k_env local_names local_env = function
	| [] -> [],k_env,local_env
	| q::qs -> (match q with
	            | Parse_ast.QI_aux(qi,l) ->
		      (match qi with
		      | Parse_ast.QI_const(n_const) ->
			let c = QI_aux(QI_const(to_ast_nexp_constraint k_env n_const),l) in
			let qis,k_env,local_env = to_ast_q_items k_env local_names local_env qs in
			(c::qis),k_env,local_env
		      | Parse_ast.QI_id(kid) ->
			let kid,k_env,local_names,local_env = opt_kind_to_ast k_env local_names local_env kid in
			let c = QI_aux(QI_id(kid),l) in
			let qis,k_env,local_env = to_ast_q_items k_env local_names local_env qs in
			(c::qis),k_env,local_env))
      in
      let lst,k_env,local_env = to_ast_q_items k_env Nameset.empty Envmap.empty qlist in
      TypQ_aux(TypQ_tq(lst),l), k_env, local_env)

let to_ast_typschm (k_env:kind Envmap.t) (def_ord:order) (tschm:Parse_ast.typschm) :Ast.typschm * kind Envmap.t * kind Envmap.t =
  match tschm with
  | Parse_ast.TypSchm_aux(ts,l) ->
    (match ts with | Parse_ast.TypSchm_ts(tquant,t) ->
      let tq,k_env,local_env = to_ast_typquant k_env tquant in
      let typ = to_ast_typ k_env def_ord t in
      TypSchm_aux(TypSchm_ts(tq,typ),l),k_env,local_env)

let to_ast_lit (Parse_ast.L_aux(lit,l)) : lit =
  L_aux(
    (match lit with
    | Parse_ast.L_unit -> L_unit
    | Parse_ast.L_zero -> L_zero
    | Parse_ast.L_one -> L_one
    | Parse_ast.L_true -> L_true
    | Parse_ast.L_false -> L_false
    | Parse_ast.L_undef -> L_undef
    | Parse_ast.L_num(i) -> L_num(i)
    | Parse_ast.L_hex(h) -> L_hex(h)
    | Parse_ast.L_bin(b) -> L_bin(b)
    | Parse_ast.L_real r -> L_real r
    | Parse_ast.L_string(s) -> L_string(s))
    ,l)

let rec to_ast_typ_pat (Parse_ast.ATyp_aux (typ_aux, l)) =
  match typ_aux with
  | Parse_ast.ATyp_wild -> TP_aux (TP_wild, l)
  | Parse_ast.ATyp_var kid -> TP_aux (TP_var (to_ast_var kid), l)
  | Parse_ast.ATyp_app (f, typs) ->
     TP_aux (TP_app (to_ast_id f, List.map to_ast_typ_pat typs), l)
  | _ -> typ_error l "Unexpected type in type pattern" None None None
                                     
let rec to_ast_pat (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.P_aux(pat,l) : Parse_ast.pat) : unit pat =
  P_aux(
    (match pat with
    | Parse_ast.P_lit(lit) -> P_lit(to_ast_lit lit)
    | Parse_ast.P_wild -> P_wild
    | Parse_ast.P_var (pat, Parse_ast.ATyp_aux (Parse_ast.ATyp_id id, _)) ->
       P_as (to_ast_pat k_env def_ord pat, to_ast_id id)
    | Parse_ast.P_typ(typ,pat) -> P_typ(to_ast_typ k_env def_ord typ,to_ast_pat k_env def_ord pat)
    | Parse_ast.P_id(id) -> P_id(to_ast_id id)
    | Parse_ast.P_var (pat, typ) -> P_var (to_ast_pat k_env def_ord pat, to_ast_typ_pat typ)
    | Parse_ast.P_app(id,pats) ->
      if pats = []
      then P_id (to_ast_id id)
      else P_app(to_ast_id id, List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_record(fpats,_) ->
      P_record(List.map
                 (fun (Parse_ast.FP_aux(Parse_ast.FP_Fpat(id,fp),l)) ->
		      FP_aux(FP_Fpat(to_ast_id id, to_ast_pat k_env def_ord fp),(l,())))
                 fpats, false)
    | Parse_ast.P_vector(pats) -> P_vector(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_vector_concat(pats) -> P_vector_concat(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_tup(pats) -> P_tup(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_list(pats) -> P_list(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_cons(pat1, pat2) -> P_cons (to_ast_pat k_env def_ord pat1, to_ast_pat k_env def_ord pat2)
    ), (l,()))


let rec to_ast_letbind (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.LB_aux(lb,l) : Parse_ast.letbind) : unit letbind =
  LB_aux(
    (match lb with
    | Parse_ast.LB_val(pat,exp) ->
      LB_val(to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord exp)
    ), (l,()))

and to_ast_exp (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.E_aux(exp,l) : Parse_ast.exp) : unit exp =
  E_aux(
    (match exp with
    | Parse_ast.E_block(exps) ->
      (match to_ast_fexps false k_env def_ord exps with
      | Some(fexps) -> E_record(fexps)
      | None -> E_block(List.map (to_ast_exp k_env def_ord) exps))
    | Parse_ast.E_nondet(exps) -> E_nondet(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_id(id) -> E_id(to_ast_id id)
    | Parse_ast.E_ref(id) -> E_ref(to_ast_id id)
    | Parse_ast.E_lit(lit) -> E_lit(to_ast_lit lit)
    | Parse_ast.E_cast(typ,exp) -> E_cast(to_ast_typ k_env def_ord typ, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_app(f,args) ->
      (match List.map (to_ast_exp k_env def_ord) args with
	| [] -> E_app(to_ast_id f, [])
	| [E_aux(E_tuple(exps),_)] -> E_app(to_ast_id f, exps)
	| exps -> E_app(to_ast_id f, exps))
    | Parse_ast.E_app_infix(left,op,right) ->
      E_app_infix(to_ast_exp k_env def_ord left, to_ast_id op, to_ast_exp k_env def_ord right)
    | Parse_ast.E_tuple(exps) -> E_tuple(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_if(e1,e2,e3) -> E_if(to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2, to_ast_exp k_env def_ord e3)
    | Parse_ast.E_for(id,e1,e2,e3,atyp,e4) ->
      E_for(to_ast_id id,to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2,
            to_ast_exp k_env def_ord e3,to_ast_order k_env def_ord atyp, to_ast_exp k_env def_ord e4)
    | Parse_ast.E_loop (Parse_ast.While, e1, e2) -> E_loop (While, to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2)
    | Parse_ast.E_loop (Parse_ast.Until, e1, e2) -> E_loop (Until, to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2)
    | Parse_ast.E_vector(exps) -> E_vector(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_vector_access(vexp,exp) -> E_vector_access(to_ast_exp k_env def_ord vexp, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_vector_subrange(vex,exp1,exp2) ->
      E_vector_subrange(to_ast_exp k_env def_ord vex, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_vector_update(vex,exp1,exp2) ->
      E_vector_update(to_ast_exp k_env def_ord vex, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_vector_update_subrange(vex,e1,e2,e3) ->
      E_vector_update_subrange(to_ast_exp k_env def_ord vex, to_ast_exp k_env def_ord e1,
			       to_ast_exp k_env def_ord e2, to_ast_exp k_env def_ord e3)
    | Parse_ast.E_vector_append(e1,e2) -> E_vector_append(to_ast_exp k_env def_ord e1,to_ast_exp k_env def_ord e2)
    | Parse_ast.E_list(exps) -> E_list(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_cons(e1,e2) -> E_cons(to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2)
    | Parse_ast.E_record fexps ->
       (match to_ast_fexps true k_env def_ord fexps with
        | Some fexps -> E_record fexps
        | None -> raise (Reporting_basic.err_unreachable l "to_ast_fexps with true returned none"))
    | Parse_ast.E_record_update(exp,fexps) ->
      (match to_ast_fexps true k_env def_ord fexps with
      | Some(fexps) -> E_record_update(to_ast_exp k_env def_ord exp, fexps)
      | _ -> raise (Reporting_basic.err_unreachable l "to_ast_fexps with true returned none"))
    | Parse_ast.E_field(exp,id) -> E_field(to_ast_exp k_env def_ord exp, to_ast_id id)
    | Parse_ast.E_case(exp,pexps) -> E_case(to_ast_exp k_env def_ord exp, List.map (to_ast_case k_env def_ord) pexps)
    | Parse_ast.E_try (exp, pexps) -> E_try (to_ast_exp k_env def_ord exp, List.map (to_ast_case k_env def_ord) pexps)
    | Parse_ast.E_let(leb,exp) -> E_let(to_ast_letbind k_env def_ord leb, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_assign(lexp,exp) -> E_assign(to_ast_lexp k_env def_ord lexp, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_var(lexp,exp1,exp2) -> E_var(to_ast_lexp k_env def_ord lexp, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_sizeof(nexp) -> E_sizeof(to_ast_nexp k_env nexp)
    | Parse_ast.E_constraint nc -> E_constraint (to_ast_nexp_constraint k_env nc)
    | Parse_ast.E_exit exp -> E_exit(to_ast_exp k_env def_ord exp)
    | Parse_ast.E_throw exp -> E_throw (to_ast_exp k_env def_ord exp)
    | Parse_ast.E_return exp -> E_return(to_ast_exp k_env def_ord exp)
    | Parse_ast.E_assert(cond,msg) -> E_assert(to_ast_exp k_env def_ord cond, to_ast_exp k_env def_ord msg)
    | _ -> raise (Reporting_basic.err_unreachable l "Unparsable construct in to_ast_exp")
    ), (l,()))

and to_ast_lexp (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.E_aux(exp,l) : Parse_ast.exp) : unit lexp =
  LEXP_aux(
    (match exp with
     | Parse_ast.E_id(id) -> LEXP_id(to_ast_id id)
     | Parse_ast.E_deref(exp) -> LEXP_deref(to_ast_exp k_env def_ord exp)
     | Parse_ast.E_cast(typ,Parse_ast.E_aux(Parse_ast.E_id(id),l')) ->
       LEXP_cast(to_ast_typ k_env def_ord typ, to_ast_id id)
     | Parse_ast.E_tuple(tups) ->
       let ltups = List.map (to_ast_lexp k_env def_ord) tups in
       let is_ok_in_tup (LEXP_aux (le,(l,_))) =
         match le with
         | LEXP_id _ | LEXP_cast _ | LEXP_vector _ | LEXP_field _ | LEXP_vector_range _ | LEXP_tup _ -> ()
         | LEXP_memory _ | LEXP_deref _ ->
           typ_error l "only identifiers, fields, and vectors may be set in a tuple" None None None in
       List.iter is_ok_in_tup ltups;
       LEXP_tup(ltups)
    | Parse_ast.E_app((Parse_ast.Id_aux(f,l') as f'),args) ->
      (match f with
      | Parse_ast.Id(id) ->
	(match List.map (to_ast_exp k_env def_ord) args with
	  | [] -> LEXP_memory(to_ast_id f',[])
	  | [E_aux(E_tuple exps,_)] -> LEXP_memory(to_ast_id f',exps)
	  | args -> LEXP_memory(to_ast_id f', args))
      | _ -> typ_error l' "memory call on lefthand side of assignment must begin with an id" None None None)
    | Parse_ast.E_vector_access(vexp,exp) -> LEXP_vector(to_ast_lexp k_env def_ord vexp, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_vector_subrange(vexp,exp1,exp2) ->
      LEXP_vector_range(to_ast_lexp k_env def_ord vexp, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_field(fexp,id) -> LEXP_field(to_ast_lexp k_env def_ord fexp, to_ast_id id)
    | _ -> typ_error l "Only identifiers, cast identifiers, vector accesses, vector slices, and fields can be on the lefthand side of an assignment" None None None)
      , (l,()))

and to_ast_case (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.Pat_aux(pex,l) : Parse_ast.pexp) : unit pexp =
  match pex with
  | Parse_ast.Pat_exp(pat,exp) -> Pat_aux(Pat_exp(to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord exp),(l,()))
  | Parse_ast.Pat_when(pat,guard,exp) ->
     Pat_aux (Pat_when (to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord guard, to_ast_exp k_env def_ord exp), (l, ()))

and to_ast_fexps (fail_on_error:bool) (k_env:kind Envmap.t) (def_ord:order) (exps : Parse_ast.exp list) : unit fexps option =
  match exps with
  | [] -> Some(FES_aux(FES_Fexps([],false), (Parse_ast.Unknown,())))
  | fexp::exps -> let maybe_fexp,maybe_error = to_ast_record_try k_env def_ord fexp in
                  (match maybe_fexp,maybe_error with
                  | Some(fexp),None ->
                    (match (to_ast_fexps fail_on_error k_env def_ord exps) with
                    | Some(FES_aux(FES_Fexps(fexps,_),l)) -> Some(FES_aux(FES_Fexps(fexp::fexps,false),l))
                    | _  -> None)
                  | None,Some(l,msg) ->
                    if fail_on_error
                    then typ_error l msg None None None
                    else None
                  | _ -> None)

and to_ast_record_try (k_env:kind Envmap.t) (def_ord:order) (Parse_ast.E_aux(exp,l):Parse_ast.exp): unit fexp option * (l * string) option =
  match exp with
  | Parse_ast.E_app_infix(left,op,r) ->
    (match left, op with
    | Parse_ast.E_aux(Parse_ast.E_id(id),li), Parse_ast.Id_aux(Parse_ast.Id("="),leq) ->
      Some(FE_aux(FE_Fexp(to_ast_id id, to_ast_exp k_env def_ord r), (l,()))),None
    | Parse_ast.E_aux(_,li) , Parse_ast.Id_aux(Parse_ast.Id("="),leq) ->
      None,Some(li,"Expected an identifier to begin this field assignment")
    | Parse_ast.E_aux(Parse_ast.E_id(id),li), Parse_ast.Id_aux(_,leq) ->
      None,Some(leq,"Expected a field assignment to be identifier = expression")
    | Parse_ast.E_aux(_,li),Parse_ast.Id_aux(_,leq) ->
      None,Some(l,"Expected a field assignment to be identifier = expression"))
  | _ ->
    None,Some(l, "Expected a field assignment to be identifier = expression")

let to_ast_default (names, k_env, default_order) (default : Parse_ast.default_typing_spec) : default_spec envs_out =
  match default with
  | Parse_ast.DT_aux(df,l) ->
    (match df with
    | Parse_ast.DT_kind(bk,v) ->
      let k,k_typ = to_ast_base_kind bk in
      let v = to_ast_var v in
      let key = var_to_string v in
      DT_aux(DT_kind(k,v),l),(names,(Envmap.insert k_env (key,k_typ)),default_order)
    | Parse_ast.DT_typ(typschm,id) ->
      let tps,_,_ = to_ast_typschm k_env default_order typschm in
      DT_aux(DT_typ(tps,to_ast_id id),l),(names,k_env,default_order)
    | Parse_ast.DT_order(bk,o) ->
      let k,k_typ = to_ast_base_kind bk in
      (match (k,o) with
	| (BK_aux(BK_order, _), Parse_ast.ATyp_aux(Parse_ast.ATyp_inc,lo)) ->
	  let default_order = Ord_aux(Ord_inc,lo) in
	  DT_aux(DT_order default_order,l),(names,k_env,default_order)
	| (BK_aux(BK_order, _), Parse_ast.ATyp_aux(Parse_ast.ATyp_dec,lo)) ->
	  let default_order = Ord_aux(Ord_dec,lo) in
	  DT_aux(DT_order default_order,l),(names,k_env,default_order)
	| _ -> typ_error l "Inc and Dec must have kind Order" None None None))

let to_ast_spec (names,k_env,default_order) (val_:Parse_ast.val_spec) : (unit val_spec) envs_out =
  match val_ with
  | Parse_ast.VS_aux(vs,l) ->
    (match vs with
    | Parse_ast.VS_val_spec(ts,id,ext,is_cast) ->
      let typsch,_,_ = to_ast_typschm k_env default_order ts in
      VS_aux(VS_val_spec(typsch,to_ast_id id,ext,is_cast),(l,())),(names,k_env,default_order))

let to_ast_namescm (Parse_ast.Name_sect_aux(ns,l)) =
  Name_sect_aux(
    (match ns with
    | Parse_ast.Name_sect_none -> Name_sect_none
    | Parse_ast.Name_sect_some(s) -> Name_sect_some(s)
    ),l)

let rec to_ast_range (Parse_ast.BF_aux(r,l)) = (* TODO add check that ranges are sensible for some definition of sensible *)
  BF_aux(
    (match r with
    | Parse_ast.BF_single(i) -> BF_single(i)
    | Parse_ast.BF_range(i1,i2) -> BF_range(i1,i2)
    | Parse_ast.BF_concat(ir1,ir2) -> BF_concat( to_ast_range ir1, to_ast_range ir2)),
    l)

let to_ast_type_union k_env default_order (Parse_ast.Tu_aux(tu,l)) =
  match tu with
  | Parse_ast.Tu_ty_id(atyp,id) ->
    let typ = to_ast_typ k_env default_order atyp in
    (match typ with
     | Typ_aux(Typ_id (Id_aux (Id "unit",_)),_) ->
       Tu_aux(Tu_id(to_ast_id id),l)
     | _ -> Tu_aux(Tu_ty_id(typ, to_ast_id id), l))
  | Parse_ast.Tu_id id -> (Tu_aux(Tu_id(to_ast_id id),l))

let to_ast_typedef (names,k_env,def_ord) (td:Parse_ast.type_def) : (unit type_def) envs_out =
  match td with
  | Parse_ast.TD_aux(td,l) ->
  (match td with
  | Parse_ast.TD_abbrev(id,name_scm_opt,typschm) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typschm,k_env,_ = to_ast_typschm k_env def_ord typschm in
    let td_abrv = TD_aux(TD_abbrev(id,to_ast_namescm name_scm_opt,typschm),(l,())) in
    let typ = (match typschm with
      | TypSchm_aux(TypSchm_ts(tq,typ), _) ->
        begin match (typquant_to_quantkinds k_env tq) with
        | [] -> {k = K_Typ}
        | typs -> {k= K_Lam(typs,{k=K_Typ})}
        end) in
    td_abrv,(names,Envmap.insert k_env (key,typ),def_ord)
  | Parse_ast.TD_record(id,name_scm_opt,typq,fields,_) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typq,k_env,_ = to_ast_typquant k_env typq in
    let fields = List.map (fun (atyp,id) -> (to_ast_typ k_env def_ord atyp),(to_ast_id id)) fields in (* Add check that all arms have unique names locally *)
    let td_rec = TD_aux(TD_record(id,to_ast_namescm name_scm_opt,typq,fields,false),(l,())) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_rec, (names,Envmap.insert k_env (key,typ), def_ord)
  | Parse_ast.TD_variant(id,name_scm_opt,typq,arms,_) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typq,k_env,_ = to_ast_typquant k_env typq in
    let arms = List.map (to_ast_type_union k_env def_ord) arms in (* Add check that all arms have unique names *)
    let td_var = TD_aux(TD_variant(id,to_ast_namescm name_scm_opt,typq,arms,false),(l,())) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_var, (names,Envmap.insert k_env (key,typ), def_ord)
  | Parse_ast.TD_enum(id,name_scm_opt,enums,_) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let enums = List.map to_ast_id enums in
    let keys = List.map id_to_string enums in
    let td_enum = TD_aux(TD_enum(id,to_ast_namescm name_scm_opt,enums,false),(l,())) in (* Add check that all enums have unique names *)
    let k_env = List.fold_right (fun k k_env -> Envmap.insert k_env (k,{k=K_Nat})) keys (Envmap.insert k_env (key,{k=K_Typ})) in
    td_enum, (names,k_env,def_ord)
  | Parse_ast.TD_bitfield(id,typ,ranges) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typ = to_ast_typ k_env def_ord typ in
    let ranges = List.map (fun (id, range) -> (to_ast_id id, to_ast_range range)) ranges in
    TD_aux(TD_bitfield(id,typ,ranges),(l,())), (names,Envmap.insert k_env (key, {k=K_Typ}),def_ord))

let to_ast_kdef (names,k_env,def_ord) (td:Parse_ast.kind_def) : (unit kind_def) envs_out =
  match td with
  | Parse_ast.KD_aux(td,l) ->
  (match td with
  | Parse_ast.KD_abbrev(kind,id,name_scm_opt,typschm) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let (kind,k) = to_ast_kind k_env kind in
    (match k.k with
     | K_Nat ->
       let kd_nabrv =
         (match typschm with
          | Parse_ast.TypSchm_aux(Parse_ast.TypSchm_ts(Parse_ast.TypQ_aux(tq,_),atyp),_) ->
            (match tq with
             | Parse_ast.TypQ_no_forall ->
               KD_aux(KD_nabbrev(kind,id,to_ast_namescm name_scm_opt, to_ast_nexp k_env atyp), (l,()))
             | _ -> typ_error l "Def with kind Nat cannot have universal quantification" None None None)) in
       kd_nabrv,(names,Envmap.insert k_env (key, k),def_ord)
     | _ -> assert false
    ))

let to_ast_rec (Parse_ast.Rec_aux(r,l): Parse_ast.rec_opt) : rec_opt =
  Rec_aux((match r with
  | Parse_ast.Rec_nonrec -> Rec_nonrec
  | Parse_ast.Rec_rec -> Rec_rec
  ),l)

let to_ast_tannot_opt (k_env:kind Envmap.t) (def_ord:order) (Parse_ast.Typ_annot_opt_aux(tp,l)):tannot_opt * kind Envmap.t * kind Envmap.t=
  match tp with
  | Parse_ast.Typ_annot_opt_none ->
     Typ_annot_opt_aux (Typ_annot_opt_none, l), k_env, Envmap.empty
  | Parse_ast.Typ_annot_opt_some(tq,typ) ->
    let typq,k_env,k_local = to_ast_typquant k_env tq in
    Typ_annot_opt_aux(Typ_annot_opt_some(typq,to_ast_typ k_env def_ord typ),l),k_env,k_local

let to_ast_effects_opt (k_env : kind Envmap.t) (Parse_ast.Effect_opt_aux(e,l)) : effect_opt =
  match e with
  | Parse_ast.Effect_opt_pure -> Effect_opt_aux(Effect_opt_pure,l)
  | Parse_ast.Effect_opt_effect(typ) -> Effect_opt_aux(Effect_opt_effect(to_ast_effects k_env typ),l)

let to_ast_funcl (names,k_env,def_ord) (Parse_ast.FCL_aux(fcl,l) : Parse_ast.funcl) : (unit funcl) =
  (*let _ = Printf.eprintf "to_ast_funcl\n" in*)
  match fcl with
  | Parse_ast.FCL_Funcl(id,pexp) ->
    FCL_aux(FCL_Funcl(to_ast_id id, to_ast_case k_env def_ord pexp),(l,()))

let to_ast_fundef  (names,k_env,def_ord) (Parse_ast.FD_aux(fd,l):Parse_ast.fundef) : (unit fundef) envs_out =
  match fd with
  | Parse_ast.FD_function(rec_opt,tannot_opt,effects_opt,funcls) ->
    (*let _ = Printf.eprintf "to_ast_fundef\n" in*)
    let tannot_opt, k_env,_ = to_ast_tannot_opt k_env def_ord tannot_opt in
    FD_aux(FD_function(to_ast_rec rec_opt, tannot_opt, to_ast_effects_opt k_env effects_opt, List.map (to_ast_funcl (names, k_env, def_ord)) funcls), (l,())), (names,k_env,def_ord)

type def_progress =
    No_def
  | Def_place_holder of id * Parse_ast.l
  | Finished of unit def

type partial_def = ((unit def) * bool) ref * kind Envmap.t

let rec def_in_progress (id : id) (partial_defs : (id * partial_def) list) : partial_def option =
  match partial_defs with
  | [] -> None
  | (n,pd)::defs ->
    (match n,id with
    | Id_aux(Id(n),_), Id_aux(Id(i),_) -> if (n = i) then Some(pd) else def_in_progress id defs
    | _,_ -> def_in_progress id defs)

let to_ast_alias_spec k_env def_ord (Parse_ast.E_aux(e,le)) =
  AL_aux(
    (match e with
      | Parse_ast.E_field(Parse_ast.E_aux(Parse_ast.E_id id,li), field) ->
	AL_subreg(RI_aux(RI_id (to_ast_id id),(li,())),to_ast_id field)
      | Parse_ast.E_vector_access(Parse_ast.E_aux(Parse_ast.E_id id,li),range) ->
	AL_bit(RI_aux(RI_id (to_ast_id id),(li,())),to_ast_exp k_env def_ord range)
      | Parse_ast.E_vector_subrange(Parse_ast.E_aux(Parse_ast.E_id id,li),base,stop) ->
	AL_slice(RI_aux(RI_id (to_ast_id id),(li,())),to_ast_exp k_env def_ord base,to_ast_exp k_env def_ord stop)
      | Parse_ast.E_vector_append(Parse_ast.E_aux(Parse_ast.E_id first,lf),
				  Parse_ast.E_aux(Parse_ast.E_id second,ls)) ->
	AL_concat(RI_aux(RI_id (to_ast_id first),(lf,())),
		  RI_aux(RI_id (to_ast_id second),(ls,())))
      | _ -> raise (Reporting_basic.err_unreachable le "Found an expression not supported by parser in to_ast_alias_spec")
    ), (le,()))

let to_ast_dec (names,k_env,def_ord) (Parse_ast.DEC_aux(regdec,l)) =
  DEC_aux(
    (match regdec with
      | Parse_ast.DEC_reg(typ,id) ->
	DEC_reg(to_ast_typ k_env def_ord typ,to_ast_id id)
      | Parse_ast.DEC_alias(id,e) ->
	DEC_alias(to_ast_id id,to_ast_alias_spec k_env def_ord e)
      | Parse_ast.DEC_typ_alias(typ,id,e) ->
	DEC_typ_alias(to_ast_typ k_env def_ord typ,to_ast_id id,to_ast_alias_spec k_env def_ord e)
    ),(l,()))

let to_ast_prec = function
  | Parse_ast.Infix -> Infix
  | Parse_ast.InfixL -> InfixL
  | Parse_ast.InfixR -> InfixR

let to_ast_def (names, k_env, def_ord) partial_defs def : def_progress envs_out * (id * partial_def) list =
  let envs = (names,k_env,def_ord) in
  match def with
  | Parse_ast.DEF_overload(id,ids) ->
     ((Finished(DEF_overload(to_ast_id id, List.map to_ast_id ids))),envs),partial_defs
  | Parse_ast.DEF_fixity (prec, n, op) ->
     ((Finished(DEF_fixity (to_ast_prec prec, n, to_ast_id op)),envs),partial_defs)
  | Parse_ast.DEF_kind(k_def) ->
    let kd,envs = to_ast_kdef envs k_def in
    ((Finished(DEF_kind(kd))),envs),partial_defs
  | Parse_ast.DEF_type(t_def) ->
    let td,envs = to_ast_typedef envs t_def in
    ((Finished(DEF_type(td))),envs),partial_defs
  | Parse_ast.DEF_fundef(f_def) ->
    let fd,envs = to_ast_fundef envs f_def in
    ((Finished(DEF_fundef(fd))),envs),partial_defs
  | Parse_ast.DEF_val(lbind) ->
    let lb = to_ast_letbind k_env def_ord lbind in
    ((Finished(DEF_val(lb))),envs),partial_defs
  | Parse_ast.DEF_spec(val_spec) ->
    let vs,envs = to_ast_spec envs val_spec in
    ((Finished(DEF_spec(vs))),envs),partial_defs
  | Parse_ast.DEF_default(typ_spec) ->
    let default,envs = to_ast_default envs typ_spec in
    ((Finished(DEF_default(default))),envs),partial_defs
  | Parse_ast.DEF_reg_dec(dec) ->
    let d = to_ast_dec envs dec in
    ((Finished(DEF_reg_dec(d))),envs),partial_defs
  | Parse_ast.DEF_pragma (_, _, l) ->
     typ_error l "Encountered preprocessor directive in initial check" None None None
  | Parse_ast.DEF_internal_mutrec _ ->
     (* Should never occur because of remove_mutrec *)
     typ_error Parse_ast.Unknown "Internal mutual block found when processing scattered defs" None None None
  | Parse_ast.DEF_scattered(Parse_ast.SD_aux(sd,l)) ->
    (match sd with
    | Parse_ast.SD_scattered_function(rec_opt, tannot_opt, effects_opt, id) ->
      let rec_opt = to_ast_rec rec_opt in
      let unit,k_env',k_local = to_ast_tannot_opt k_env def_ord tannot_opt in
      let effects_opt = to_ast_effects_opt k_env' effects_opt in
      let id = to_ast_id id in
      (match (def_in_progress id partial_defs) with
      | None -> let partial_def = ref ((DEF_fundef(FD_aux(FD_function(rec_opt,unit,effects_opt,[]),(l,())))),false) in
                (No_def,envs),((id,(partial_def,k_local))::partial_defs)
      | Some(d,k) -> typ_error l "Scattered function definition header name already in use by scattered definition" (Some id) None None)
    | Parse_ast.SD_scattered_funcl(funcl) ->
      (match funcl with
      | Parse_ast.FCL_aux(Parse_ast.FCL_Funcl(id,_),_) ->
        let id = to_ast_id id in
        (match (def_in_progress id partial_defs) with
	| None -> typ_error l "Scattered function definition clause does not match any exisiting function definition headers" (Some id) None None
	| Some(d,k) ->
	 (* let _ = Printf.eprintf "SD_scattered_funcl processing\n" in
	  let _ = Envmap.iter (fun v' k -> Printf.eprintf "%s -> %s\n" v' (kind_to_string k)) k in
	  let _ = Envmap.iter (fun v' k -> Printf.eprintf "%s -> %s\n" v' (kind_to_string k) ) (Envmap.union k k_env) in *)
	  (match !d with
	  | DEF_fundef(FD_aux(FD_function(r,t,e,fcls),fl)),false ->
	    let funcl = to_ast_funcl (names,Envmap.union k k_env,def_ord) funcl in
	    d:= DEF_fundef(FD_aux(FD_function(r,t,e,fcls@[funcl]),fl)),false;
	    (No_def,envs),partial_defs
	  | _,true -> typ_error l "Scattered funciton definition clauses extends ended defintion" (Some id) None None
	  | _ -> typ_error l "Scattered function definition clause matches an existing scattered type definition header" (Some id) None None)))
    | Parse_ast.SD_scattered_variant(id,naming_scheme_opt,typquant) ->
      let id = to_ast_id id in
      let name = to_ast_namescm naming_scheme_opt in
      let typq, k_env',_ = to_ast_typquant k_env typquant in
      let kind = (match (typquant_to_quantkinds k_env' typq) with
        | [ ] -> {k = K_Typ}
        | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
      (match (def_in_progress id partial_defs) with
      | None -> let partial_def = ref ((DEF_type(TD_aux(TD_variant(id,name,typq,[],false),(l,())))),false) in
                (Def_place_holder(id,l),(names,Envmap.insert k_env ((id_to_string id),kind),def_ord)),(id,(partial_def,k_env'))::partial_defs
      | Some(d,k) -> typ_error l "Scattered type definition header name already in use by scattered definition" (Some id) None None)
    | Parse_ast.SD_scattered_unioncl(id,tu) ->
      let id = to_ast_id id in
      (match (def_in_progress id partial_defs) with
      | None -> typ_error l "Scattered type definition clause does not match any existing type definition headers" (Some id) None None
      | Some(d,k) ->
        (match !d with
	| DEF_type(TD_aux(TD_variant(id,name,typq,arms,false),tl)), false ->
	  d:= DEF_type(TD_aux(TD_variant(id,name,typq,arms@[to_ast_type_union k def_ord tu],false),tl)),false;
	  (No_def,envs),partial_defs
	| _,true -> typ_error l "Scattered type definition clause extends ended definition" (Some id) None None
	| _ -> typ_error l "Scattered type definition clause matches an existing scattered function definition header" (Some id) None None))
    | Parse_ast.SD_scattered_end(id) ->
      let id = to_ast_id id in
      (match (def_in_progress id partial_defs) with
      | None -> typ_error l "Scattered definition end does not match any open scattered definitions" (Some id) None None
      | Some(d,k) ->
        (match !d with
	| (DEF_type(_) as def),false ->
	  d:= (def,true);
	  (No_def,envs),partial_defs
	| (DEF_fundef(_) as def),false ->
	  d:= (def,true);
	  ((Finished def), envs),partial_defs
	| _, true ->
	  typ_error l "Scattered definition ended multiple times" (Some id) None None
        | _ -> raise (Reporting_basic.err_unreachable l "Something in partial_defs other than fundef and type"))))

let rec to_ast_defs_helper envs partial_defs = function
  | [] -> ([],envs,partial_defs)
  | d::ds  -> let ((d', envs), partial_defs) = to_ast_def envs partial_defs d in
              let (defs,envs,partial_defs) = to_ast_defs_helper envs partial_defs ds in
              (match d' with
              | Finished def -> (def::defs,envs, partial_defs)
              | No_def -> defs,envs,partial_defs
              | Def_place_holder(id,l) ->
                (match (def_in_progress id partial_defs) with
                 | None ->
                   raise
                     (Reporting_basic.err_unreachable l "Id stored in place holder not retrievable from partial defs")
                 | Some(d,k) ->
                   if (snd !d)
                   then (fst !d) :: defs, envs, partial_defs
                   else typ_error l "Scattered type definition never ended" (Some id) None None))

let rec remove_mutrec = function
  | [] -> []
  | Parse_ast.DEF_internal_mutrec fundefs :: defs ->
     List.map (fun fdef -> Parse_ast.DEF_fundef fdef) fundefs @ remove_mutrec defs
  | def :: defs ->
     def :: remove_mutrec defs

let to_ast (default_names : Nameset.t) (kind_env : kind Envmap.t) (def_ord : order) (Parse_ast.Defs(defs)) =
  let defs = remove_mutrec defs in
  let defs,(_,k_env,def_ord),partial_defs = to_ast_defs_helper (default_names,kind_env,def_ord) [] defs in
  List.iter
    (fun (id,(d,k)) ->
      (match !d with
      | (d,false) -> typ_error Parse_ast.Unknown "Scattered definition never ended" (Some id) None None
      | (_, true) -> ()))
    partial_defs;
  (Defs defs),k_env,def_ord

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
    ("real", {k = K_Typ});
    ("list", {k = K_Lam( [{k = K_Typ}], {k = K_Typ})});
    ("reg", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("register", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("ref", {k = K_Lam( [{k = K_Typ}], {k= K_Typ})});
    ("range", {k = K_Lam( [ {k = K_Nat}; {k= K_Nat}], {k = K_Typ}) });
    ("vector", {k = K_Lam( [{k = K_Nat}; {k= K_Ord} ; {k=K_Typ}], {k=K_Typ}) } );
    ("atom", {k = K_Lam( [ {k=K_Nat} ], {k=K_Typ})});
    ("option", { k = K_Lam( [{k=K_Typ}], {k=K_Typ}) });
    ("implicit", {k = K_Lam( [{k = K_Nat}], {k=K_Typ})} );
    ("itself", {k = K_Lam( [ {k=K_Nat} ], {k=K_Typ})});
  ]

let exp_of_string order str =
  let exp = Parser.exp_eof Lexer.token (Lexing.from_string str) in
  to_ast_exp initial_kind_env order exp

let typschm_of_string order str =
  let typschm = Parser.typschm_eof Lexer.token (Lexing.from_string str) in
  let (typschm, _, _) = to_ast_typschm initial_kind_env order typschm in
  typschm

let extern_of_string order id str = mk_val_spec (VS_val_spec (typschm_of_string order str, id, (fun _ -> Some (string_of_id id)), false))
let val_spec_of_string order id str = mk_val_spec (VS_val_spec (typschm_of_string order str, id, (fun _ -> None), false))

let val_spec_ids (Defs defs) =
  let val_spec_id (VS_aux (vs_aux, _)) =
    match vs_aux with
    | VS_val_spec (_, id, _, _) -> id
  in
  let rec vs_ids = function
    | DEF_spec vs :: defs -> val_spec_id vs :: vs_ids defs
    | def :: defs -> vs_ids defs
    | [] -> []
  in
  IdSet.of_list (vs_ids defs)

let quant_item_param = function
  | QI_aux (QI_id kopt, _) when is_nat_kopt kopt -> [prepend_id "atom_" (id_of_kid (kopt_kid kopt))]
  | QI_aux (QI_id kopt, _) when is_typ_kopt kopt -> [prepend_id "typ_" (id_of_kid (kopt_kid kopt))]
  | _ -> []
let quant_item_typ = function
  | QI_aux (QI_id kopt, _) when is_nat_kopt kopt -> [atom_typ (nvar (kopt_kid kopt))]
  | QI_aux (QI_id kopt, _) when is_typ_kopt kopt -> [mk_typ (Typ_var (kopt_kid kopt))]
  | _ -> []
let quant_item_arg = function
  | QI_aux (QI_id kopt, _) when is_nat_kopt kopt -> [mk_typ_arg (Typ_arg_nexp (nvar (kopt_kid kopt)))]
  | QI_aux (QI_id kopt, _) when is_typ_kopt kopt -> [mk_typ_arg (Typ_arg_typ (mk_typ (Typ_var (kopt_kid kopt))))]
  | _ -> []
let undefined_typschm id typq =
  let qis = quant_items typq in
  if qis = [] then
    mk_typschm typq (mk_typ (Typ_fn (unit_typ, mk_typ (Typ_id id), mk_effect [BE_undef])))
  else
    let arg_typ = mk_typ (Typ_tup (List.concat (List.map quant_item_typ qis))) in
    let ret_typ = app_typ id (List.concat (List.map quant_item_arg qis)) in
    mk_typschm typq (mk_typ (Typ_fn (arg_typ, ret_typ, mk_effect [BE_undef])))

let have_undefined_builtins = ref false

let generate_undefineds vs_ids (Defs defs) =
  let gen_vs id str =
    if (IdSet.mem id vs_ids) then [] else [extern_of_string dec_ord id str]
  in
  let undefined_builtins =
    if !have_undefined_builtins then
      []
    else
      begin
        have_undefined_builtins := true;
        List.concat
          [gen_vs (mk_id "internal_pick") "forall ('a:Type). list('a) -> 'a effect {undef}";
           gen_vs (mk_id "undefined_bool") "unit -> bool effect {undef}";
           gen_vs (mk_id "undefined_bit") "unit -> bit effect {undef}";
           gen_vs (mk_id "undefined_int") "unit -> int effect {undef}";
           gen_vs (mk_id "undefined_nat") "unit -> nat effect {undef}";
           gen_vs (mk_id "undefined_real") "unit -> real effect {undef}";
           gen_vs (mk_id "undefined_string") "unit -> string effect {undef}";
           gen_vs (mk_id "undefined_list") "forall ('a:Type). 'a -> list('a) effect {undef}";
           gen_vs (mk_id "undefined_range") "forall 'n 'm. (atom('n), atom('m)) -> range('n,'m) effect {undef}";
           gen_vs (mk_id "undefined_vector") "forall 'n ('a:Type) ('ord : Order). (atom('n), 'a) -> vector('n, 'ord,'a) effect {undef}";
           (* Only used with lem_mwords *)
           gen_vs (mk_id "undefined_bitvector") "forall 'n. atom('n) -> vector('n, dec, bit) effect {undef}";
           gen_vs (mk_id "undefined_unit") "unit -> unit effect {undef}"]
      end
  in
  let undefined_tu = function
    | Tu_aux (Tu_id id, _) -> mk_exp (E_id id)
    | Tu_aux (Tu_ty_id (Typ_aux (Typ_tup typs, _), id), _) ->
       mk_exp (E_app (id, List.map (fun _ -> mk_lit_exp L_undef) typs))
    | Tu_aux (Tu_ty_id (typ, id), _) -> mk_exp (E_app (id, [mk_lit_exp L_undef]))
  in
  let undefined_td = function
    | TD_enum (id, _, ids, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
       let typschm = typschm_of_string dec_ord ("unit -> " ^ string_of_id id ^ " effect {undef}") in
       [mk_val_spec (VS_val_spec (typschm, prepend_id "undefined_" id, (fun _ -> None), false));
        mk_fundef [mk_funcl (prepend_id "undefined_" id)
                            (mk_pat (P_lit (mk_lit L_unit)))
                            (mk_exp (E_app (mk_id "internal_pick",
                                            [mk_exp (E_list (List.map (fun id -> mk_exp (E_id id)) ids))])))]]
    | TD_record (id, _, typq, fields, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
       let pat = mk_pat (P_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id)))) in
       [mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, (fun _ -> None), false));
        mk_fundef [mk_funcl (prepend_id "undefined_" id)
                            pat
                            (mk_exp (E_record (mk_fexps (List.map (fun (_, id) -> mk_fexp id (mk_lit_exp L_undef)) fields))))]]
    | TD_variant (id, _, typq, tus, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
       let pat = mk_pat (P_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id)))) in
       [mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, (fun _ -> None), false));
        mk_fundef [mk_funcl (prepend_id "undefined_" id)
                            pat
                            (mk_exp (E_app (mk_id "internal_pick",
                                            [mk_exp (E_list (List.map undefined_tu tus))])))]]
    | _ -> []
  in
  let rec undefined_defs = function
    | DEF_type (TD_aux (td_aux, _)) as def :: defs ->
       def :: undefined_td td_aux @ undefined_defs defs
    | def :: defs ->
       def :: undefined_defs defs
    | [] -> []
  in
  Defs (undefined_builtins @ undefined_defs defs)

let rec get_registers = function
  | DEF_reg_dec (DEC_aux (DEC_reg (typ, id), _)) :: defs -> (typ, id) :: get_registers defs
  | _ :: defs -> get_registers defs
  | [] -> []

let generate_initialize_registers vs_ids (Defs defs) =
  let regs = get_registers defs in
  let initialize_registers =
    if IdSet.mem (mk_id "initialize_registers") vs_ids || regs = [] then []
    else
      [val_spec_of_string dec_ord (mk_id "initialize_registers") "unit -> unit effect {undef, wreg}";
       mk_fundef [mk_funcl (mk_id "initialize_registers")
                           (mk_pat (P_lit (mk_lit L_unit)))
                           (mk_exp (E_block (List.map (fun (typ, id) -> mk_exp (E_assign (mk_lexp (LEXP_cast (typ, id)), mk_lit_exp L_undef))) regs)))]]
  in
  Defs (defs @ initialize_registers)

let generate_enum_functions vs_ids (Defs defs) =
  let rec gen_enums = function
    | DEF_type (TD_aux (TD_enum (id, _, elems, _), _)) as enum :: defs ->
       let enum_val_spec name typ =
         mk_val_spec (VS_val_spec (mk_typschm (mk_typquant []) typ, name, (fun _ -> None), !opt_enum_casts))
       in
       let enum_range = range_typ (nint 0) (nint (List.length elems - 1)) in

       (* Create a function that converts a number to an enum. *)
       let to_enum =
         let name = append_id id "_of_num" in
         let pexp n id =
           let pat =
             if n = List.length elems - 1 then
               mk_pat (P_wild)
             else
               mk_pat (P_lit (mk_lit (L_num (Big_int.of_int n))))
           in
           mk_pexp (Pat_exp (pat, mk_exp (E_id id)))
         in
         let funcl =
           mk_funcl name
             (mk_pat (P_id (mk_id "arg#")))
             (mk_exp (E_case (mk_exp (E_id (mk_id "arg#")), List.mapi pexp elems)))
         in
         let range = range_typ (nint 0) (nint (List.length elems - 1)) in
         if IdSet.mem name vs_ids then []
         else
           [ enum_val_spec name (function_typ enum_range (mk_typ (Typ_id id)) no_effect);
             mk_fundef [funcl] ]
       in

       (* Create a function that converts from an enum to a number. *)
       let from_enum =
         let name = prepend_id "num_of_" id in
         let pexp n id = mk_pexp (Pat_exp (mk_pat (P_id id), mk_lit_exp (L_num (Big_int.of_int n)))) in
         let funcl =
           mk_funcl name
             (mk_pat (P_id (mk_id "arg#")))
             (mk_exp (E_case (mk_exp (E_id (mk_id "arg#")), List.mapi pexp elems)))
         in
         if IdSet.mem name vs_ids then []
         else
           [ enum_val_spec name (function_typ (mk_typ (Typ_id id)) enum_range no_effect);
             mk_fundef [funcl] ]
         (* This is the simple way to generate this function, but the
            rewriter and backends are all kinds of broken for function clause
            patterns.
         let name = prepend_id "num_of_" id in
         let funcl n id =
           mk_funcl name
             (mk_pat (P_id id))
             (mk_lit_exp (L_num (Big_int.of_int n)))
         in
         if IdSet.mem name vs_ids then []
         else
           [ enum_val_spec name (function_typ (mk_typ (Typ_id id)) enum_range no_effect);
             mk_fundef (List.mapi funcl elems) ]
          *)
       in
       enum :: to_enum @ from_enum @ gen_enums defs

    | def :: defs -> def :: gen_enums defs
    | [] -> []
  in
  Defs (gen_enums defs)

let incremental_k_env = ref initial_kind_env

let process_ast order defs =
  let ast, k_env, _= to_ast Nameset.empty !incremental_k_env order defs in
  incremental_k_env := k_env;
  let vs_ids = val_spec_ids ast in
  if not !opt_undefined_gen then
    generate_enum_functions vs_ids ast
  else
    ast
    |> generate_undefineds vs_ids
    |> generate_enum_functions vs_ids
    |> generate_initialize_registers vs_ids

let ast_of_def_string order str =
  let def = Parser.def_eof Lexer.token (Lexing.from_string str) in
  process_ast order (Parse_ast.Defs [def])
