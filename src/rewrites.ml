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

module Big_int = Nat_big_num
open Ast
open Ast_util
open Type_check
open Spec_analysis
open Rewriter

let (>>) f g = fun x -> g(f(x))

let fresh_name_counter = ref 0

let fresh_name () =
  let current = !fresh_name_counter in
  let () = fresh_name_counter := (current + 1) in
  current

let reset_fresh_name_counter () =
  fresh_name_counter := 0

let fresh_id pre l =
  let current = fresh_name () in
  Id_aux (Id (pre ^ string_of_int current), gen_loc l)

let fresh_id_exp pre ((l,annot)) =
  let id = fresh_id pre l in
  E_aux (E_id id, (gen_loc l, annot))

let fresh_id_pat pre ((l,annot)) =
  let id = fresh_id pre l in
  P_aux (P_id id, (gen_loc l, annot))

let get_loc_exp (E_aux (_,(l,_))) = l

let gen_vs (id, spec) = Initial_check.extern_of_string dec_ord (mk_id id) spec

let annot_exp_effect e_aux l env typ effect = E_aux (e_aux, (l, Some (env, typ, effect)))
let annot_exp e_aux l env typ = annot_exp_effect e_aux l env typ no_effect
let annot_pat p_aux l env typ = P_aux (p_aux, (l, Some (env, typ, no_effect)))
let annot_letbind (p_aux, exp) l env typ =
  LB_aux (LB_val (annot_pat p_aux l env typ, exp), (l, Some (env, typ, effect_of exp)))

let simple_num l n = E_aux (
  E_lit (L_aux (L_num n, gen_loc l)),
  simple_annot (gen_loc l)
    (atom_typ (Nexp_aux (Nexp_constant n, gen_loc l))))

let effectful_effs = function
  | Effect_aux (Effect_set effs, _) ->
    List.exists
      (fun (BE_aux (be,_)) ->
       match be with
       | BE_nondet | BE_unspec | BE_undef | BE_lset -> false
       | _ -> true
      ) effs

let effectful eaux = effectful_effs (effect_of (propagate_exp_effect eaux))
let effectful_pexp pexp = effectful_effs (snd (propagate_pexp_effect pexp))

let rec small (E_aux (exp,_)) = match exp with
  | E_id _
  | E_lit _ -> true
  | E_cast (_,e) -> small e
  | E_list es -> List.for_all small es
  | E_cons (e1,e2) -> small e1 && small e2
  | E_sizeof _ -> true
  | _ -> false

let id_is_local_var id env = match Env.lookup_id id env with
  | Local _ -> true
  | _ -> false

let id_is_unbound id env = match Env.lookup_id id env with
  | Unbound -> true
  | _ -> false

let rec lexp_is_local (LEXP_aux (lexp, _)) env = match lexp with
  | LEXP_memory _ | LEXP_deref _ -> false
  | LEXP_id id
  | LEXP_cast (_, id) -> id_is_local_var id env
  | LEXP_tup lexps -> List.for_all (fun lexp -> lexp_is_local lexp env) lexps
  | LEXP_vector (lexp,_)
  | LEXP_vector_range (lexp,_,_)
  | LEXP_field (lexp,_) -> lexp_is_local lexp env

let rec lexp_is_local_intro (LEXP_aux (lexp, _)) env = match lexp with
  | LEXP_memory _ | LEXP_deref _ -> false
  | LEXP_id id
  | LEXP_cast (_, id) -> id_is_unbound id env
  | LEXP_tup lexps -> List.for_all (fun lexp -> lexp_is_local_intro lexp env) lexps
  | LEXP_vector (lexp,_)
  | LEXP_vector_range (lexp,_,_)
  | LEXP_field (lexp,_) -> lexp_is_local_intro lexp env

let lexp_is_effectful (LEXP_aux (_, (_, annot))) = match annot with
  | Some (_, _, eff) -> effectful_effs eff
  | _ -> false

let find_used_vars exp =
  (* Overapproximates the set of used identifiers, but for the use cases below
     this is acceptable. *)
  let e_id id = IdSet.singleton id, E_id id in
  fst (fold_exp
    { (compute_exp_alg IdSet.empty IdSet.union) with e_id = e_id } exp)

let find_introduced_vars exp =
  let lEXP_aux ((ids, lexp), annot) =
    let ids = match lexp with
      | LEXP_id id | LEXP_cast (_, id)
        when id_is_unbound id (env_of_annot annot) -> IdSet.add id ids
      | _ -> ids in
    (ids, LEXP_aux (lexp, annot)) in
  fst (fold_exp
    { (compute_exp_alg IdSet.empty IdSet.union) with lEXP_aux = lEXP_aux } exp)

let find_updated_vars exp =
  let intros = find_introduced_vars exp in
  let lEXP_aux ((ids, lexp), annot) =
    let ids = match lexp with
      | LEXP_id id | LEXP_cast (_, id)
        when id_is_local_var id (env_of_annot annot) && not (IdSet.mem id intros) ->
         IdSet.add id ids
      | _ -> ids in
    (ids, LEXP_aux (lexp, annot)) in
  fst (fold_exp
    { (compute_exp_alg IdSet.empty IdSet.union) with lEXP_aux = lEXP_aux } exp)

let rec rewrite_nexp_ids env (Nexp_aux (nexp, l) as nexp_aux) = match nexp with
| Nexp_id id -> rewrite_nexp_ids env (Env.get_num_def id env)
| Nexp_times (nexp1, nexp2) -> Nexp_aux (Nexp_times (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
| Nexp_sum (nexp1, nexp2) -> Nexp_aux (Nexp_sum (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
| Nexp_minus (nexp1, nexp2) -> Nexp_aux (Nexp_minus (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
| Nexp_exp nexp -> Nexp_aux (Nexp_exp (rewrite_nexp_ids env nexp), l)
| Nexp_neg nexp -> Nexp_aux (Nexp_neg (rewrite_nexp_ids env nexp), l)
| _ -> nexp_aux

let rewrite_defs_nexp_ids, rewrite_typ_nexp_ids =
  let rec rewrite_typ env (Typ_aux (typ, l) as typ_aux) = match typ with
    | Typ_fn (arg_t, ret_t, eff) ->
       Typ_aux (Typ_fn (rewrite_typ env arg_t, rewrite_typ env ret_t, eff), l)
    | Typ_tup ts ->
       Typ_aux (Typ_tup (List.map (rewrite_typ env) ts), l)
    | Typ_exist (kids, c, typ) ->
       Typ_aux (Typ_exist (kids, c, rewrite_typ env typ), l)
    | Typ_app (id, targs) ->
       Typ_aux (Typ_app (id, List.map (rewrite_typ_arg env) targs), l)
    | _ -> typ_aux
  and rewrite_typ_arg env (Typ_arg_aux (targ, l) as targ_aux) = match targ with
    | Typ_arg_nexp nexp ->
       Typ_arg_aux (Typ_arg_nexp (rewrite_nexp_ids env nexp), l)
    | Typ_arg_typ typ ->
       Typ_arg_aux (Typ_arg_typ (rewrite_typ env typ), l)
    | Typ_arg_order ord ->
       Typ_arg_aux (Typ_arg_order ord, l)
  in

  let rewrite_annot = function
    | (l, Some (env, typ, eff)) -> (l, Some (env, rewrite_typ env typ, eff))
    | (l, None) -> (l, None)
  in

  rewrite_defs_base {
    rewriters_base with rewrite_exp = (fun _ -> map_exp_annot rewrite_annot)
    },
  rewrite_typ


(* Re-write trivial sizeof expressions - trivial meaning that the
   value of the sizeof can be directly inferred from the type
   variables in scope. *)
let rewrite_trivial_sizeof, rewrite_trivial_sizeof_exp =
  let extract_typ_var l env nexp (id, (_, typ)) =
    let var = E_aux (E_id id, (l, Some (env, typ, no_effect))) in
    match destruct_atom_nexp env typ with
    | Some size when prove env (nc_eq size nexp) -> Some var
    (* AA: This next case is a bit of a hack... is there a more
       general way to deal with trivial nexps that are offset by
       constants? This will resolve a 'n - 1 sizeof when 'n is in
       scope. *)
    | Some size when prove env (nc_eq (nsum size (nint 1)) nexp) ->
       let one_exp = infer_exp env (mk_lit_exp (L_num (Big_int.of_int 1))) in
       Some (E_aux (E_app (mk_id "add_range", [var; one_exp]), (gen_loc l, Some (env, atom_typ (nsum size (nint 1)), no_effect))))
    | _ ->
       begin
         match destruct_vector env typ with
         | Some (len, _, _) when prove env (nc_eq len nexp) ->
            Some (E_aux (E_app (mk_id "length", [var]), (l, Some (env, atom_typ len, no_effect))))
         | _ -> None
       end
  in
  let rec split_nexp (Nexp_aux (nexp_aux, l) as nexp) =
    match nexp_aux with
    | Nexp_sum (n1, n2) ->
       mk_exp (E_app (mk_id "add_range", [split_nexp n1; split_nexp n2]))
    | Nexp_minus (n1, n2) ->
       mk_exp (E_app (mk_id "sub_range", [split_nexp n1; split_nexp n2]))
    | Nexp_times (n1, n2) ->
       mk_exp (E_app (mk_id "mult_range", [split_nexp n1; split_nexp n2]))
    | Nexp_neg nexp -> mk_exp (E_app (mk_id "negate_range", [split_nexp nexp]))
    | _ -> mk_exp (E_sizeof nexp)
  in
  let rec rewrite_e_aux split_sizeof (E_aux (e_aux, (l, _)) as orig_exp) =
    let env = env_of orig_exp in
    match e_aux with
    | E_sizeof (Nexp_aux (Nexp_constant c, _) as nexp) ->
       E_aux (E_lit (L_aux (L_num c, l)), (l, Some (env, atom_typ nexp, no_effect)))
    | E_sizeof nexp ->
       begin
         match nexp_simp (rewrite_nexp_ids (env_of orig_exp) nexp) with
         | Nexp_aux (Nexp_constant c, _) ->
            E_aux (E_lit (L_aux (L_num c, l)), (l, Some (env, atom_typ nexp, no_effect)))
         | _ ->
            let locals = Env.get_locals env in
            let exps = Bindings.bindings locals
                       |> List.map (extract_typ_var l env nexp)
                       |> List.map (fun opt -> match opt with Some x -> [x] | None -> [])
                       |> List.concat
            in
            match exps with
            | (exp :: _) -> check_exp env (strip_exp exp) (typ_of exp)
            | [] when split_sizeof ->
               fold_exp (rewrite_e_sizeof false) (check_exp env (split_nexp nexp) (typ_of orig_exp))
            | [] -> orig_exp
       end
    | _ -> orig_exp
  and rewrite_e_sizeof split_sizeof =
    { id_exp_alg with e_aux = (fun (exp, annot) -> rewrite_e_aux split_sizeof (E_aux (exp, annot))) }
  in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp (rewrite_e_sizeof true)) }, rewrite_e_aux true

(* Rewrite sizeof expressions with type-level variables to
   term-level expressions

   For each type-level variable used in a sizeof expressions whose value cannot
   be directly extracted from existing parameters of the surrounding function,
   a further parameter is added; calls to the function are rewritten
   accordingly (possibly causing further rewriting in the calling function) *)
let rewrite_sizeof (Defs defs) =
  let sizeof_frees exp =
    fst (fold_exp
           { (compute_exp_alg KidSet.empty KidSet.union) with
             e_sizeof = (fun nexp -> (nexp_frees nexp, E_sizeof nexp)) }
           exp) in

  (* Collect nexps whose values can be obtained directly from a pattern bind *)
  let nexps_from_params pat =
    fst (fold_pat
           { (compute_pat_alg [] (@)) with
             p_aux = (fun ((v,pat),((l,_) as annot)) ->
             let v' = match pat with
               | P_id id | P_as (_, id) ->
                  let (Typ_aux (typ,_) as typ_aux) = typ_of_annot annot in
                  (match typ with
                   | Typ_app (atom, [Typ_arg_aux (Typ_arg_nexp nexp, _)])
                        when string_of_id atom = "atom" ->
                      [nexp, E_id id]
                   | Typ_app (vector, _) when string_of_id vector = "vector" ->
                      let id_length = Id_aux (Id "length", gen_loc l) in
                      (try
                         (match Env.get_val_spec id_length (env_of_annot annot) with
                          | _ ->
                             let (_,len,_,_) = vector_typ_args_of typ_aux in
                             let exp = E_app (id_length, [E_aux (E_id id, annot)]) in
                             [len, exp])
                       with
                       | _ -> [])
                   | _ -> [])
               | _ -> [] in
             (v @ v', P_aux (pat,annot)))} pat) in

  (* Substitute collected values in sizeof expressions *)
  let rec e_sizeof nmap (Nexp_aux (nexp, l) as nexp_aux) =
    try snd (List.find (fun (nexp,_) -> nexp_identical nexp nexp_aux) nmap)
    with
    | Not_found ->
       let binop nexp1 op nexp2 = E_app_infix (
                                      E_aux (e_sizeof nmap nexp1, simple_annot l (atom_typ nexp1)),
                                      Id_aux (Id op, Parse_ast.Unknown),
                                      E_aux (e_sizeof nmap nexp2, simple_annot l (atom_typ nexp2))
                                    ) in
       let (Nexp_aux (nexp, l) as nexp_aux) = nexp_simp nexp_aux in
       (match nexp with
        | Nexp_constant i -> E_lit (L_aux (L_num i, l))
        | Nexp_times (nexp1, nexp2) -> binop nexp1 "*" nexp2
        | Nexp_sum (nexp1, nexp2) -> binop nexp1 "+" nexp2
        | Nexp_minus (nexp1, nexp2) -> binop nexp1 "-" nexp2
        | _ -> E_sizeof nexp_aux) in

  let ex_regex = Str.regexp "'ex[0-9]+" in

  (* Rewrite calls to functions which have had parameters added to pass values
     of type-level variables; these are added as sizeof expressions first, and
     then further rewritten as above. *)
  let e_app_aux param_map ((exp, exp_orig), ((l, _) as annot)) =
    let env = env_of_annot annot in
    let full_exp = E_aux (exp, annot) in
    let orig_exp = E_aux (exp_orig, annot) in
    match exp with
    | E_app (f, args) ->
       if Bindings.mem f param_map then
         (* Retrieve instantiation of the type variables of the called function
           for the given parameters in the original environment *)
         let inst =
           try instantiation_of orig_exp with
           | Type_error (l, err) ->
             raise (Reporting_basic.err_typ l (string_of_type_error err)) in
         (* Rewrite the inst using orig_kid so that each type variable has it's
            original name rather than a mangled typechecker name *)
         let inst = KBindings.fold (fun kid uvar b -> KBindings.add (orig_kid kid) uvar b) inst KBindings.empty in
         let kid_exp kid = begin
             (* We really don't want to see an existential here! *)
             assert (not (Str.string_match ex_regex (string_of_kid kid) 0));
             let uvar = try Some (KBindings.find (orig_kid kid) inst) with Not_found -> None in
             match uvar with
             | Some (U_nexp nexp) ->
                let sizeof = E_aux (E_sizeof nexp, (l, Some (env, atom_typ nexp, no_effect))) in
                (try rewrite_trivial_sizeof_exp sizeof with
                | Type_error (l, err) ->
                  raise (Reporting_basic.err_typ l (string_of_type_error err)))
             (* If the type variable is Not_found then it was probably
                introduced by a P_var pattern, so it likely exists as
                a variable in scope. It can't be an existential because the assert rules that out. *)
             | None -> annot_exp (E_id (id_of_kid (orig_kid kid))) l env (atom_typ (nvar (orig_kid kid)))
             | _ ->
                raise (Reporting_basic.err_unreachable l
                                                       ("failed to infer nexp for type variable " ^ string_of_kid kid ^
                                                          " of function " ^ string_of_id f))
           end in
         let kid_exps = List.map kid_exp (KidSet.elements (Bindings.find f param_map)) in
         (E_aux (E_app (f, kid_exps @ args), annot), orig_exp)
       else (full_exp, orig_exp)
    | _ -> (full_exp, orig_exp) in

  (* Plug this into a folding algorithm that also keeps around a copy of the
  original expressions, which we use to infer instantiations of type variables
  in the original environments *)
  let copy_exp_alg =
    { e_block = (fun es -> let (es, es') = List.split es in (E_block es, E_block es'))
    ; e_nondet = (fun es -> let (es, es') = List.split es in (E_nondet es, E_nondet es'))
    ; e_id = (fun id -> (E_id id, E_id id))
    ; e_ref = (fun id -> (E_ref id, E_ref id))
    ; e_lit = (fun lit -> (E_lit lit, E_lit lit))
    ; e_cast = (fun (typ,(e,e')) -> (E_cast (typ,e), E_cast (typ,e')))
    ; e_app = (fun (id,es) -> let (es, es') = List.split es in (E_app (id,es), E_app (id,es')))
    ; e_app_infix = (fun ((e1,e1'),id,(e2,e2')) -> (E_app_infix (e1,id,e2), E_app_infix (e1',id,e2')))
    ; e_tuple = (fun es -> let (es, es') = List.split es in (E_tuple es, E_tuple es'))
    ; e_if = (fun ((e1,e1'),(e2,e2'),(e3,e3')) -> (E_if (e1,e2,e3), E_if (e1',e2',e3')))
    ; e_for = (fun (id,(e1,e1'),(e2,e2'),(e3,e3'),order,(e4,e4')) -> (E_for (id,e1,e2,e3,order,e4), E_for (id,e1',e2',e3',order,e4')))
    ; e_loop = (fun (lt, (e1, e1'), (e2, e2')) -> (E_loop (lt, e1, e2), E_loop (lt, e1', e2')))
    ; e_vector = (fun es -> let (es, es') = List.split es in (E_vector es, E_vector es'))
    ; e_vector_access = (fun ((e1,e1'),(e2,e2')) -> (E_vector_access (e1,e2), E_vector_access (e1',e2')))
    ; e_vector_subrange =  (fun ((e1,e1'),(e2,e2'),(e3,e3')) -> (E_vector_subrange (e1,e2,e3), E_vector_subrange (e1',e2',e3')))
    ; e_vector_update = (fun ((e1,e1'),(e2,e2'),(e3,e3')) -> (E_vector_update (e1,e2,e3), E_vector_update (e1',e2',e3')))
    ; e_vector_update_subrange =  (fun ((e1,e1'),(e2,e2'),(e3,e3'),(e4,e4')) -> (E_vector_update_subrange (e1,e2,e3,e4), E_vector_update_subrange (e1',e2',e3',e4')))
    ; e_vector_append = (fun ((e1,e1'),(e2,e2')) -> (E_vector_append (e1,e2), E_vector_append (e1',e2')))
    ; e_list = (fun es -> let (es, es') = List.split es in (E_list es, E_list es'))
    ; e_cons = (fun ((e1,e1'),(e2,e2')) -> (E_cons (e1,e2), E_cons (e1',e2')))
    ; e_record = (fun (fexps, fexps') -> (E_record fexps, E_record fexps'))
    ; e_record_update = (fun ((e1,e1'),(fexp,fexp')) -> (E_record_update (e1,fexp), E_record_update (e1',fexp')))
    ; e_field = (fun ((e1,e1'),id) -> (E_field (e1,id), E_field (e1',id)))
    ; e_case = (fun ((e1,e1'),pexps) -> let (pexps, pexps') = List.split pexps in (E_case (e1,pexps), E_case (e1',pexps')))
    ; e_try = (fun ((e1,e1'),pexps) -> let (pexps, pexps') = List.split pexps in (E_try (e1,pexps), E_try (e1',pexps')))
    ; e_let = (fun ((lb,lb'),(e2,e2')) -> (E_let (lb,e2), E_let (lb',e2')))
    ; e_assign = (fun ((lexp,lexp'),(e2,e2')) -> (E_assign (lexp,e2), E_assign (lexp',e2')))
    ; e_sizeof = (fun nexp -> (E_sizeof nexp, E_sizeof nexp))
    ; e_constraint = (fun nc -> (E_constraint nc, E_constraint nc))
    ; e_exit = (fun (e1,e1') -> (E_exit (e1), E_exit (e1')))
    ; e_throw = (fun (e1,e1') -> (E_throw (e1), E_throw (e1')))
    ; e_return = (fun (e1,e1') -> (E_return e1, E_return e1'))
    ; e_assert = (fun ((e1,e1'),(e2,e2')) -> (E_assert(e1,e2), E_assert(e1',e2')) )
    ; e_internal_cast = (fun (a,(e1,e1')) -> (E_internal_cast (a,e1), E_internal_cast (a,e1')))
    ; e_internal_exp = (fun a -> (E_internal_exp a, E_internal_exp a))
    ; e_internal_exp_user = (fun (a1,a2) -> (E_internal_exp_user (a1,a2), E_internal_exp_user (a1,a2)))
    ; e_comment = (fun c -> (E_comment c, E_comment c))
    ; e_comment_struc = (fun (e,e') -> (E_comment_struc e, E_comment_struc e'))
    ; e_internal_let = (fun ((lexp,lexp'), (e2,e2'), (e3,e3')) -> (E_var (lexp,e2,e3), E_var (lexp',e2',e3')))
    ; e_internal_plet = (fun (pat, (e1,e1'), (e2,e2')) -> (E_internal_plet (pat,e1,e2), E_internal_plet (pat,e1',e2')))
    ; e_internal_return = (fun (e,e') -> (E_internal_return e, E_internal_return e'))
    ; e_internal_value = (fun v -> (E_internal_value v, E_internal_value v))
    ; e_aux = (fun ((e,e'),annot) -> (E_aux (e,annot), E_aux (e',annot)))
    ; lEXP_id = (fun id -> (LEXP_id id, LEXP_id id))
    ; lEXP_deref = (fun (e, e') -> (LEXP_deref e, LEXP_deref e'))
    ; lEXP_memory = (fun (id,es) -> let (es, es') = List.split es in (LEXP_memory (id,es), LEXP_memory (id,es')))
    ; lEXP_cast = (fun (typ,id) -> (LEXP_cast (typ,id), LEXP_cast (typ,id)))
    ; lEXP_tup = (fun tups -> let (tups,tups') = List.split tups in (LEXP_tup tups, LEXP_tup tups'))
    ; lEXP_vector = (fun ((lexp,lexp'),(e2,e2')) -> (LEXP_vector (lexp,e2), LEXP_vector (lexp',e2')))
    ; lEXP_vector_range = (fun ((lexp,lexp'),(e2,e2'),(e3,e3')) -> (LEXP_vector_range (lexp,e2,e3), LEXP_vector_range (lexp',e2',e3')))
    ; lEXP_field = (fun ((lexp,lexp'),id) -> (LEXP_field (lexp,id), LEXP_field (lexp',id)))
    ; lEXP_aux = (fun ((lexp,lexp'),annot) -> (LEXP_aux (lexp,annot), LEXP_aux (lexp',annot)))
    ; fE_Fexp = (fun (id,(e,e')) -> (FE_Fexp (id,e), FE_Fexp (id,e')))
    ; fE_aux = (fun ((fexp,fexp'),annot) -> (FE_aux (fexp,annot), FE_aux (fexp',annot)))
    ; fES_Fexps = (fun (fexps,b) -> let (fexps, fexps') = List.split fexps in (FES_Fexps (fexps,b), FES_Fexps (fexps',b)))
    ; fES_aux = (fun ((fexp,fexp'),annot) -> (FES_aux (fexp,annot), FES_aux (fexp',annot)))
    ; def_val_empty = (Def_val_empty, Def_val_empty)
    ; def_val_dec = (fun (e,e') -> (Def_val_dec e, Def_val_dec e'))
    ; def_val_aux = (fun ((defval,defval'),aux) -> (Def_val_aux (defval,aux), Def_val_aux (defval',aux)))
    ; pat_exp = (fun (pat,(e,e')) -> (Pat_exp (pat,e), Pat_exp (pat,e')))
    ; pat_when = (fun (pat,(e1,e1'),(e2,e2')) -> (Pat_when (pat,e1,e2), Pat_when (pat,e1',e2')))
    ; pat_aux = (fun ((pexp,pexp'),a) -> (Pat_aux (pexp,a), Pat_aux (pexp',a)))
    ; lB_val = (fun (pat,(e,e')) -> (LB_val (pat,e), LB_val (pat,e')))
    ; lB_aux = (fun ((lb,lb'),annot) -> (LB_aux (lb,annot), LB_aux (lb',annot)))
    ; pat_alg = id_pat_alg
    } in

  let rewrite_sizeof_fun params_map
                         (FD_aux (FD_function (rec_opt,tannot,eff,funcls),((l,_) as annot))) =
    let rewrite_funcl_body (FCL_aux (FCL_Funcl (id,pexp), annot)) (funcls,nvars) =
      let pat,guard,exp,pannot = destruct_pexp pexp in
      let nmap = nexps_from_params pat in
      (* first rewrite calls to other functions... *)
      let exp' = fst (fold_exp { copy_exp_alg with e_aux = e_app_aux params_map } exp) in
      (* ... then rewrite sizeof expressions in current function body *)
      let exp'' = fold_exp { id_exp_alg with e_sizeof = e_sizeof nmap } exp' in
      let guard' = match guard with
        | Some guard ->
           (* As above *)
           let guard' = fst (fold_exp { copy_exp_alg with e_aux = e_app_aux params_map } guard) in
           Some (fold_exp { id_exp_alg with e_sizeof = e_sizeof nmap } guard')
        | None -> None in
      let pexp' = construct_pexp (pat,guard',exp'',pannot) in
      (FCL_aux (FCL_Funcl (id,pexp'), annot) :: funcls,
       KidSet.union nvars (sizeof_frees exp'')) in
    let (funcls, nvars) = List.fold_right rewrite_funcl_body funcls ([], KidSet.empty) in
    (* Add a parameter for each remaining free type-level variable in a
       sizeof expression *)
    let kid_typ kid = atom_typ (nvar kid) in
    let kid_annot kid = simple_annot l (kid_typ kid) in
    let kid_pat kid =
      P_aux (P_typ (kid_typ kid,
                    P_aux (P_id (Id_aux (Id (string_of_id (id_of_kid kid) ^ "__tv"), l)),
                           kid_annot kid)), kid_annot kid) in
    let kid_eaux kid = E_id (Id_aux (Id (string_of_id (id_of_kid kid) ^ "__tv"), l)) in
    let kid_typs = List.map kid_typ (KidSet.elements nvars) in
    let kid_pats = List.map kid_pat (KidSet.elements nvars) in
    let kid_nmap = List.map (fun kid -> (nvar kid, kid_eaux kid)) (KidSet.elements nvars) in
    let rewrite_funcl_params (FCL_aux (FCL_Funcl (id, pexp), annot) as funcl) =
      let rec rewrite_pat (P_aux (pat, ((l, _) as pannot)) as paux) =
        let penv = env_of_annot pannot in
        let peff = effect_of_annot (snd pannot) in
        if KidSet.is_empty nvars then paux else
          match pat_typ_of paux with
          | Typ_aux (Typ_tup typs, _) ->
             let ptyp' = Typ_aux (Typ_tup (kid_typs @ typs), l) in
             (match pat with
              | P_tup pats ->
                 P_aux (P_tup (kid_pats @ pats), (l, Some (penv, ptyp', peff)))
              | P_wild -> P_aux (pat, (l, Some (penv, ptyp', peff)))
              | P_typ (Typ_aux (Typ_tup typs, l), pat) ->
                 P_aux (P_typ (Typ_aux (Typ_tup (kid_typs @ typs), l),
                               rewrite_pat pat), (l, Some (penv, ptyp', peff)))
              | P_as (_, id) | P_id id ->
                 (* adding parameters here would change the type of id;
              we should remove the P_as/P_id here and add a let-binding to the body *)
                 raise (Reporting_basic.err_todo l
                                                 "rewriting as- or id-patterns for sizeof expressions not yet implemented")
              | _ ->
                 raise (Reporting_basic.err_unreachable l
                                                        "unexpected pattern while rewriting function parameters for sizeof expressions"))
          | ptyp ->
             let ptyp' = Typ_aux (Typ_tup (kid_typs @ [ptyp]), l) in
             P_aux (P_tup (kid_pats @ [paux]), (l, Some (penv, ptyp', peff))) in
      let pat,guard,exp,pannot = destruct_pexp pexp in
      let pat' = rewrite_pat pat in
      let guard' = match guard with
        | Some guard -> Some (fold_exp { id_exp_alg with e_sizeof = e_sizeof kid_nmap } guard)
        | None -> None in
      let exp' = fold_exp { id_exp_alg with e_sizeof = e_sizeof kid_nmap } exp in
      let pexp' = construct_pexp (pat',guard',exp',pannot) in
      FCL_aux (FCL_Funcl (id, pexp'), annot) in
    let funcls = List.map rewrite_funcl_params funcls in
    let fd = FD_aux (FD_function (rec_opt,tannot,eff,funcls),annot) in
    let params_map =
      if KidSet.is_empty nvars then params_map else
        Bindings.add (id_of_fundef fd) nvars params_map in
    (params_map, FD_aux (FD_function (rec_opt,tannot,eff,funcls),annot)) in

  let rewrite_sizeof_def (params_map, defs) = function
    | DEF_fundef fd ->
       let (params_map', fd') = rewrite_sizeof_fun params_map fd in
       (params_map', defs @ [DEF_fundef fd'])
    | DEF_internal_mutrec fds ->
       let rewrite_fd (params_map, fds) fd =
         let (params_map', fd') = rewrite_sizeof_fun params_map fd in
         (params_map', fds @ [fd']) in
       (* TODO Split rewrite_sizeof_fun into an analysis and a rewrite pass,
          so that we can call the analysis until a fixpoint is reached and then
          rewrite the mutually recursive functions *)
       let (params_map', fds') = List.fold_left rewrite_fd (params_map, []) fds in
       (params_map', defs @ [DEF_internal_mutrec fds'])
    | DEF_val (LB_aux (lb, annot)) ->
       begin
         let lb' = match lb with
         | LB_val (pat, exp) ->
           let exp' = fst (fold_exp { copy_exp_alg with e_aux = e_app_aux params_map } exp) in
           LB_val (pat, exp') in
         (params_map, defs @ [DEF_val (LB_aux (lb', annot))])
       end
    | def ->
       (params_map, defs @ [def]) in

  let rewrite_sizeof_valspec params_map def =
    let rewrite_typschm (TypSchm_aux (TypSchm_ts (tq, typ), l) as ts) id =
      if Bindings.mem id params_map then
        let kid_typs = List.map (fun kid -> atom_typ (nvar kid))
                                (KidSet.elements (Bindings.find id params_map)) in
        let typ' = match typ with
          | Typ_aux (Typ_fn (vtyp_arg, vtyp_ret, declared_eff), vl) ->
             let vtyp_arg' = begin
                 match vtyp_arg with
                 | Typ_aux (Typ_tup typs, vl) ->
                    Typ_aux (Typ_tup (kid_typs @ typs), vl)
                 | _ -> Typ_aux (Typ_tup (kid_typs @ [vtyp_arg]), vl)
               end in
             Typ_aux (Typ_fn (vtyp_arg', vtyp_ret, declared_eff), vl)
          | _ ->
            raise (Reporting_basic.err_typ l "val spec with non-function type") in
        TypSchm_aux (TypSchm_ts (tq, typ'), l)
      else ts in
    match def with
    | DEF_spec (VS_aux (VS_val_spec (typschm, id, ext, is_cast), a)) ->
       DEF_spec (VS_aux (VS_val_spec (rewrite_typschm typschm id, id, ext, is_cast), a))
    | def -> def
  in

  let (params_map, defs) = List.fold_left rewrite_sizeof_def
                                          (Bindings.empty, []) defs in
  let defs = List.map (rewrite_sizeof_valspec params_map) defs in
  (* Defs defs *)
  fst (check initial_env (Defs defs))

let rewrite_defs_remove_assert defs =
  let e_assert ((E_aux (eaux, (l, _)) as exp), str) = match eaux with
    | E_constraint _ ->
       E_assert (exp, str)
    | _ ->
       E_assert (E_aux (E_lit (mk_lit L_true), simple_annot l bool_typ), str) in
  rewrite_defs_base
    { rewriters_base with
      rewrite_exp = (fun _ -> fold_exp { id_exp_alg with e_assert = e_assert}) }
    defs

let remove_vector_concat_pat pat =

  (* ivc: bool that indicates whether the exp is in a vector_concat pattern *)
  let remove_typed_patterns =
    fold_pat { id_pat_alg with
               p_aux = (function
                        | (P_typ (_,P_aux (p,_)),annot)
                        | (p,annot) -> 
                           P_aux (p,annot)
                       )
             } in
  
  (* let pat = remove_typed_patterns pat in *)

  let fresh_id_v = fresh_id "v__" in

  (* expects that P_typ elements have been removed from AST,
     that the length of all vectors involved is known,
     that we don't have indexed vectors *)

  (* introduce names for all patterns of form P_vector_concat *)
  let name_vector_concat_roots =
    { p_lit = (fun lit -> P_lit lit)
    ; p_typ = (fun (typ,p) -> P_typ (typ,p false)) (* cannot happen *)
    ; p_wild = P_wild
    ; p_as = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_var = (fun (pat,kid) -> P_var (pat true,kid))
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_tup            = (fun ps -> P_tup (List.map (fun p -> p false) ps))
    ; p_list           = (fun ps -> P_list (List.map (fun p -> p false) ps))
    ; p_cons           = (fun (p,ps) -> P_cons (p false, ps false))
    ; p_aux =
        (fun (pat,((l,_) as annot)) contained_in_p_as ->
          match pat with
          | P_vector_concat pats ->
             (if contained_in_p_as
              then P_aux (pat,annot)
              else P_aux (P_as (P_aux (pat,annot),fresh_id_v l),annot))
          | _ -> P_aux (pat,annot)
        )
    ; fP_aux = (fun (fpat,annot) -> FP_aux (fpat,annot))
    ; fP_Fpat = (fun (id,p) -> FP_Fpat (id,p false))
    } in

  let pat = (fold_pat name_vector_concat_roots pat) false in

  (* introduce names for all unnamed child nodes of P_vector_concat *)
  let name_vector_concat_elements =
    let p_vector_concat pats =
      let rec aux ((P_aux (p,((l,_) as a))) as pat) = match p with
        | P_vector _ -> P_aux (P_as (pat,fresh_id_v l),a)
        | P_id id -> P_aux (P_id id,a)
        | P_as (p,id) -> P_aux (P_as (p,id),a)
        | P_typ (typ, pat) -> P_aux (P_typ (typ, aux pat),a)
        | P_wild -> P_aux (P_wild,a)
        | _ ->
           raise
             (Reporting_basic.err_unreachable
                l "name_vector_concat_elements: Non-vector in vector-concat pattern") in
      P_vector_concat (List.map aux pats) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in

  let pat = fold_pat name_vector_concat_elements pat in



  let rec tag_last = function
    | x :: xs -> let is_last = xs = [] in (x,is_last) :: tag_last xs
    | _ -> [] in

  (* remove names from vectors in vector_concat patterns and collect them as declarations for the
     function body or expression *)
  let unname_vector_concat_elements = (* :
        ('a,
         'a pat *      ((tannot exp -> tannot exp) list),
         'a pat_aux *  ((tannot exp -> tannot exp) list),
         'a fpat *     ((tannot exp -> tannot exp) list),
         'a fpat_aux * ((tannot exp -> tannot exp) list))
          pat_alg = *)

    (* build a let-expression of the form "let child = root[i..j] in body" *)
    let letbind_vec typ_opt (rootid,rannot) (child,cannot) (i,j) =
      let (l,_) = cannot in
      let env = env_of_annot rannot in
      let rootname = string_of_id rootid in
      let childname = string_of_id child in
      
      let root = E_aux (E_id rootid, rannot) in
      let index_i = simple_num l i in
      let index_j = simple_num l j in

      (* FIXME *)
      let subv = fix_eff_exp (E_aux (E_vector_subrange (root, index_i, index_j), cannot)) in
      (* let (_, _, ord, _) = vector_typ_args_of (Env.base_typ_of (env_of root) (typ_of root)) in
      let subrange_id = if is_order_inc ord then "bitvector_subrange_inc" else "bitvector_subrange_dec" in
      let subv = fix_eff_exp (E_aux (E_app (mk_id subrange_id, [root; index_i; index_j]), cannot)) in *)

      let id_pat =
        match typ_opt with
        | Some typ -> add_p_typ typ (P_aux (P_id child,cannot))
        | None -> P_aux (P_id child,cannot) in
      let letbind = fix_eff_lb (LB_aux (LB_val (id_pat,subv),cannot)) in
      (letbind,
       (fun body ->
         if IdSet.mem child (find_used_vars body)
         then fix_eff_exp (annot_exp (E_let (letbind,body)) l env (typ_of body))
         else body),
       (rootname,childname)) in

    let p_aux = function
      | ((P_as (P_aux (P_vector_concat pats,rannot'),rootid),decls),rannot) ->
         let rtyp = Env.base_typ_of (env_of_annot rannot') (typ_of_annot rannot') in
         let (start,last_idx) = (match vector_typ_args_of rtyp with
          | (Nexp_aux (Nexp_constant start,_), Nexp_aux (Nexp_constant length,_), ord, _) ->
             (start, if is_order_inc ord
                     then Big_int.sub (Big_int.add start length) (Big_int.of_int 1)
                     else Big_int.add (Big_int.sub start length) (Big_int.of_int 1))
          | _ ->
            raise (Reporting_basic.err_unreachable (fst rannot')
              ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern"))) in
         let rec aux typ_opt (pos,pat_acc,decl_acc) (P_aux (p,cannot),is_last) =
           let ctyp = Env.base_typ_of (env_of_annot cannot) (typ_of_annot cannot) in
           let (_,length,ord,_) = vector_typ_args_of ctyp in
           let (pos',index_j) = match length with
             | Nexp_aux (Nexp_constant i,_) ->
                if is_order_inc ord
                then (Big_int.add pos i, Big_int.sub (Big_int.add pos i) (Big_int.of_int 1))
                else (Big_int.sub pos i, Big_int.add (Big_int.sub pos i) (Big_int.of_int 1))
             | Nexp_aux (_,l) ->
                if is_last then (pos,last_idx)
                else
                  raise
                    (Reporting_basic.err_unreachable
                       l ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern")) in
           (match p with
            (* if we see a named vector pattern, remove the name and remember to
              declare it later *)
            | P_as (P_aux (p,cannot),cname) ->
               let (lb,decl,info) = letbind_vec typ_opt (rootid,rannot) (cname,cannot) (pos,index_j) in
               (pos', pat_acc @ [P_aux (p,cannot)], decl_acc @ [((lb,decl),info)])
            (* if we see a P_id variable, remember to declare it later *)
            | P_id cname ->
               let (lb,decl,info) = letbind_vec typ_opt (rootid,rannot) (cname,cannot) (pos,index_j) in
               (pos', pat_acc @ [P_aux (P_id cname,cannot)], decl_acc @ [((lb,decl),info)])
            | P_typ (typ, pat) -> aux (Some typ) (pos,pat_acc,decl_acc) (pat, is_last)
            (* normal vector patterns are fine *)
            | _ -> (pos', pat_acc @ [P_aux (p,cannot)],decl_acc)) in
          let pats_tagged = tag_last pats in
          let (_,pats',decls') = List.fold_left (aux None) (start,[],[]) pats_tagged in

          (* abuse P_vector_concat as a P_vector_const pattern: it has the of
          patterns as an argument but they're meant to be consed together *)
          (P_aux (P_as (P_aux (P_vector_concat pats',rannot'),rootid),rannot), decls @ decls')
      | ((p,decls),annot) -> (P_aux (p,annot),decls) in

    { p_lit            = (fun lit -> (P_lit lit,[]))
    ; p_wild           = (P_wild,[])
    ; p_as             = (fun ((pat,decls),id) -> (P_as (pat,id),decls))
    ; p_typ            = (fun (typ,(pat,decls)) -> (P_typ (typ,pat),decls))
    ; p_id             = (fun id -> (P_id id,[]))
    ; p_var            = (fun ((pat,decls),kid) -> (P_var (pat,kid),decls))
    ; p_app            = (fun (id,ps) -> let (ps,decls) = List.split ps in
                                         (P_app (id,ps),List.flatten decls))
    ; p_record         = (fun (ps,b) -> let (ps,decls) = List.split ps in
                                        (P_record (ps,b),List.flatten decls))
    ; p_vector         = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector ps,List.flatten decls))
    ; p_vector_concat  = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector_concat ps,List.flatten decls))
    ; p_tup            = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_tup ps,List.flatten decls))
    ; p_list           = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_list ps,List.flatten decls))
    ; p_cons           = (fun ((p,decls),(p',decls')) -> (P_cons (p,p'), decls @ decls'))
    ; p_aux            = (fun ((pat,decls),annot) -> p_aux ((pat,decls),annot))
    ; fP_aux           = (fun ((fpat,decls),annot) -> (FP_aux (fpat,annot),decls))
    ; fP_Fpat          = (fun (id,(pat,decls)) -> (FP_Fpat (id,pat),decls))
    } in

  let (pat,decls) = fold_pat unname_vector_concat_elements pat in

  let decls =
    let module S = Set.Make(String) in

    let roots_needed =
      List.fold_right
        (fun (_,(rootid,childid)) roots_needed ->
         if S.mem childid roots_needed then
           (* let _ = print_endline rootid in *)
           S.add rootid roots_needed
         else if String.length childid >= 3 && String.sub childid 0 2 = String.sub "v__" 0 2 then
           roots_needed
         else
           S.add rootid roots_needed
        ) decls S.empty in
    List.filter
      (fun (_,(_,childid)) ->  
       S.mem childid roots_needed ||
         String.length childid < 3 ||
           not (String.sub childid 0 2 = String.sub "v__" 0 2))
      decls in

  let (letbinds,decls) =
    let (decls,_) = List.split decls in
    List.split decls in

  let decls = List.fold_left (fun f g x -> f (g x)) (fun b -> b) decls in


  (* at this point shouldn't have P_as patterns in P_vector_concat patterns any more,
     all P_as and P_id vectors should have their declarations in decls.
     Now flatten all vector_concat patterns *)
  
  let flatten =
    let p_vector_concat ps =
      let aux p acc = match p with
        | (P_aux (P_vector_concat pats,_)) -> pats @ acc
        | pat -> pat :: acc in
      P_vector_concat (List.fold_right aux ps []) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat flatten pat in

  (* at this point pat should be a flat pattern: no vector_concat patterns
     with vector_concats patterns as direct child-nodes anymore *)

  let range a b =
    let rec aux a b = if Big_int.greater a b then [] else a :: aux (Big_int.add a (Big_int.of_int 1)) b in
    if Big_int.greater a b then List.rev (aux b a) else aux a b in

  let remove_vector_concats =
    let p_vector_concat ps =
      let aux acc (P_aux (p,annot),is_last) =
        let env = env_of_annot annot in
        let typ = Env.base_typ_of env (typ_of_annot annot) in
        let eff = effect_of_annot (snd annot) in
        let (l,_) = annot in
        let wild _ = P_aux (P_wild,(gen_loc l, Some (env, bit_typ, eff))) in
        if is_vector_typ typ then
          match p, vector_typ_args_of typ with
          | P_vector ps,_ -> acc @ ps
          | _, (_,Nexp_aux (Nexp_constant length,_),_,_) ->
             acc @ (List.map wild (range Big_int.zero (Big_int.sub length (Big_int.of_int 1))))
          | _, _ ->
            (*if is_last then*) acc @ [wild Big_int.zero]
        else raise
          (Reporting_basic.err_unreachable l
            ("remove_vector_concats: Non-vector in vector-concat pattern " ^
              string_of_typ (typ_of_annot annot))) in

      let has_length (P_aux (p,annot)) =
        let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
        match vector_typ_args_of typ with
        | (_,Nexp_aux (Nexp_constant length,_),_,_) -> true
        | _ -> false in

      let ps_tagged = tag_last ps in
      let ps' = List.fold_left aux [] ps_tagged in
      let last_has_length ps = List.exists (fun (p,b) -> b && has_length p) ps_tagged in

      if last_has_length ps then
        P_vector ps'
      else
        (* If the last vector pattern in the vector_concat pattern has unknown
        length we misuse the P_vector_concat constructor's argument to place in
        the following way: P_vector_concat [x;y; ... ;z] should be mapped to the
        pattern-match x :: y :: .. z, i.e. if x : 'a, then z : vector 'a. *)
        P_vector_concat ps' in

    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat remove_vector_concats pat in
  
  (pat,letbinds,decls)

(* assumes there are no more E_internal expressions *)
let rewrite_exp_remove_vector_concat_pat rewriters (E_aux (exp,(l,annot)) as full_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_case (e,ps) ->
     let aux = function
     | (Pat_aux (Pat_exp (pat,body),annot')) ->
       let (pat,_,decls) = remove_vector_concat_pat pat in
       Pat_aux (Pat_exp (pat, decls (rewrite_rec body)),annot')
     | (Pat_aux (Pat_when (pat,guard,body),annot')) ->
       let (pat,_,decls) = remove_vector_concat_pat pat in
       Pat_aux (Pat_when (pat, decls (rewrite_rec guard), decls (rewrite_rec body)),annot') in
     rewrap (E_case (rewrite_rec e, List.map aux ps))
  | E_let (LB_aux (LB_val (pat,v),annot'),body) ->
     let (pat,_,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val (pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | exp -> rewrite_base full_exp

let rewrite_fun_remove_vector_concat_pat
      rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pexp),(l,annot))) =
    let pat,guard,exp,pannot = destruct_pexp pexp in
    let (pat',_,decls) = remove_vector_concat_pat pat in
    let guard' = match guard with
      | Some exp -> Some (decls (rewriters.rewrite_exp rewriters exp))
      | None -> None in
    let exp' = decls (rewriters.rewrite_exp rewriters exp) in
    let pexp' = construct_pexp (pat',guard',exp',pannot) in
    (FCL_aux (FCL_Funcl (id,pexp'),(l,annot)))
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_defs_remove_vector_concat (Defs defs) =
  let rewriters =
    {rewrite_exp = rewrite_exp_remove_vector_concat_pat;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun_remove_vector_concat_pat;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} in
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_val (LB_aux (LB_val (pat,exp),a)) ->
       let (pat,letbinds,_) = remove_vector_concat_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val (pat,exp),a))] @ defvals
    | d -> [d] in
  Defs (List.flatten (List.map rewrite_def defs))

(* A few helper functions for rewriting guarded pattern clauses.
   Used both by the rewriting of P_when and separately by the rewriting of
   bitvectors in parameter patterns of function clauses *)

let remove_wildcards pre (P_aux (_,(l,_)) as pat) =
  fold_pat
    {id_pat_alg with
      p_aux = function
        | (P_wild,(l,annot)) -> P_aux (P_id (fresh_id pre l),(l,annot))
        | (p,annot) -> P_aux (p,annot) }
    pat

(* Check if one pattern subsumes the other, and if so, calculate a
   substitution of variables that are used in the same position.
   TODO: Check somewhere that there are no variable clashes (the same variable
   name used in different positions of the patterns)
 *)
let rec subsumes_pat (P_aux (p1,annot1) as pat1) (P_aux (p2,annot2) as pat2) =
  let rewrap p = P_aux (p,annot1) in
  let subsumes_list s pats1 pats2 =
    if List.length pats1 = List.length pats2
    then
      let subs = List.map2 s pats1 pats2 in
      List.fold_right
        (fun p acc -> match p, acc with
          | Some subst, Some substs -> Some (subst @ substs)
          | _ -> None)
        subs (Some [])
    else None in
  match p1, p2 with
  | P_lit (L_aux (lit1,_)), P_lit (L_aux (lit2,_)) ->
      if lit1 = lit2 then Some [] else None
  | P_as (pat1,_), _ -> subsumes_pat pat1 pat2
  | _, P_as (pat2,_) -> subsumes_pat pat1 pat2
  | P_typ (_,pat1), _ -> subsumes_pat pat1 pat2
  | _, P_typ (_,pat2) -> subsumes_pat pat1 pat2
  | P_id (Id_aux (id1,_) as aid1), P_id (Id_aux (id2,_) as aid2) ->
    if id1 = id2 then Some []
    else if Env.lookup_id aid1 (env_of_annot annot1) = Unbound &&
            Env.lookup_id aid2 (env_of_annot annot2) = Unbound
           then Some [(id2,id1)] else None
  | P_id id1, _ ->
    if Env.lookup_id id1 (env_of_annot annot1) = Unbound then Some [] else None
  | P_wild, _ -> Some []
  | P_app (Id_aux (id1,l1),args1), P_app (Id_aux (id2,_),args2) ->
    if id1 = id2 then subsumes_list subsumes_pat args1 args2 else None
  | P_record (fps1,b1), P_record (fps2,b2) ->
    if b1 = b2 then subsumes_list subsumes_fpat fps1 fps2 else None
  | P_vector pats1, P_vector pats2
  | P_vector_concat pats1, P_vector_concat pats2
  | P_tup pats1, P_tup pats2
  | P_list pats1, P_list pats2 ->
    subsumes_list subsumes_pat pats1 pats2
  | P_list (pat1 :: pats1), P_cons _ ->
    subsumes_pat (rewrap (P_cons (pat1, rewrap (P_list pats1)))) pat2
  | P_cons _, P_list (pat2 :: pats2)->
    subsumes_pat pat1 (rewrap (P_cons (pat2, rewrap (P_list pats2))))
  | P_cons (pat1, pats1), P_cons (pat2, pats2) ->
    (match subsumes_pat pat1 pat2, subsumes_pat pats1 pats2 with
    | Some substs1, Some substs2 -> Some (substs1 @ substs2)
    | _ -> None)
  | _ -> None
and subsumes_fpat (FP_aux (FP_Fpat (id1,pat1),_)) (FP_aux (FP_Fpat (id2,pat2),_)) =
  if id1 = id2 then subsumes_pat pat1 pat2 else None

let equiv_pats pat1 pat2 =
  match subsumes_pat pat1 pat2, subsumes_pat pat2 pat1 with
  | Some _, Some _ -> true
  | _, _ -> false

let subst_id_pat pat (id1,id2) =
  let p_id (Id_aux (id,l)) = (if id = id1 then P_id (Id_aux (id2,l)) else P_id (Id_aux (id,l))) in
  fold_pat {id_pat_alg with p_id = p_id} pat

let subst_id_exp exp (id1,id2) =
  Ast_util.subst (Id_aux (id1,Parse_ast.Unknown)) (E_aux (E_id (Id_aux (id2,Parse_ast.Unknown)),(Parse_ast.Unknown,None))) exp

let rec pat_to_exp (P_aux (pat,(l,annot))) =
  let rewrap e = E_aux (e,(l,annot)) in
  match pat with
  | P_lit lit -> rewrap (E_lit lit)
  | P_wild -> raise (Reporting_basic.err_unreachable l
      "pat_to_exp given wildcard pattern")
  | P_as (pat,id) -> rewrap (E_id id)
  | P_var (pat, _) -> pat_to_exp pat
  | P_typ (_,pat) -> pat_to_exp pat
  | P_id id -> rewrap (E_id id)
  | P_app (id,pats) -> rewrap (E_app (id, List.map pat_to_exp pats))
  | P_record (fpats,b) ->
      rewrap (E_record (FES_aux (FES_Fexps (List.map fpat_to_fexp fpats,b),(l,annot))))
  | P_vector pats -> rewrap (E_vector (List.map pat_to_exp pats))
  | P_vector_concat pats -> raise (Reporting_basic.err_unreachable l
      "pat_to_exp not implemented for P_vector_concat")
      (* We assume that vector concatenation patterns have been transformed
         away already *)
  | P_tup pats -> rewrap (E_tuple (List.map pat_to_exp pats))
  | P_list pats -> rewrap (E_list (List.map pat_to_exp pats))
  | P_cons (p,ps) -> rewrap (E_cons (pat_to_exp p, pat_to_exp ps))
and fpat_to_fexp (FP_aux (FP_Fpat (id,pat),(l,annot))) =
  FE_aux (FE_Fexp (id, pat_to_exp pat),(l,annot))

let case_exp e t cs =
  let l = get_loc_exp e in
  let env = env_of e in
  let annot = (get_loc_exp e, Some (env_of e, t, no_effect)) in
  match cs with
  | [(P_aux (P_id id, pannot) as pat, body, _)] ->
    fix_eff_exp (annot_exp (E_let (LB_aux (LB_val (pat, e), pannot), body)) l env t)
  | _ ->
    let pexp (pat,body,annot) = Pat_aux (Pat_exp (pat,body),annot) in
    let ps = List.map pexp cs in
    (* let efr = union_effs (List.map effect_of_pexp ps) in *)
    fix_eff_exp (annot_exp (E_case (e,ps)) l env t)

let rewrite_guarded_clauses l cs =
  let rec group clauses =
    let add_clause (pat,cls,annot) c = (pat,cls @ [c],annot) in
    let rec group_aux current acc = (function
      | ((pat,guard,body,annot) as c) :: cs ->
          let (current_pat,_,_) = current in
          (match subsumes_pat current_pat pat with
            | Some substs ->
                let pat' = List.fold_left subst_id_pat pat substs in
                let guard' = (match guard with
                  | Some exp -> Some (List.fold_left subst_id_exp exp substs)
                  | None -> None) in
                let body' = List.fold_left subst_id_exp body substs in
                let c' = (pat',guard',body',annot) in
                group_aux (add_clause current c') acc cs
            | None ->
                let pat = remove_wildcards "g__" pat in
                group_aux (pat,[c],annot) (acc @ [current]) cs)
      | [] -> acc @ [current]) in
    let groups = match clauses with
      | ((pat,guard,body,annot) as c) :: cs ->
          group_aux (remove_wildcards "g__" pat, [c], annot) [] cs
      | _ ->
          raise (Reporting_basic.err_unreachable l
            "group given empty list in rewrite_guarded_clauses") in
    List.map (fun cs -> if_pexp cs) groups
  and if_pexp (pat,cs,annot) = (match cs with
    | c :: _ ->
        (* fix_eff_pexp (pexp *)
        let body = if_exp pat cs in
        let pexp = fix_eff_pexp (Pat_aux (Pat_exp (pat,body),annot)) in
        let (Pat_aux (_,annot)) = pexp in
        (pat, body, annot)
    | [] ->
        raise (Reporting_basic.err_unreachable l
            "if_pexp given empty list in rewrite_guarded_clauses"))
  and if_exp current_pat = (function
    | (pat,guard,body,annot) :: ((pat',guard',body',annot') as c') :: cs ->
        (match guard with
          | Some exp ->
              let else_exp =
                if equiv_pats current_pat pat'
                then if_exp current_pat (c' :: cs)
                else case_exp (pat_to_exp current_pat) (typ_of body') (group (c' :: cs)) in
              fix_eff_exp (annot_exp (E_if (exp,body,else_exp)) (fst annot) (env_of exp) (typ_of body))
          | None -> body)
    | [(pat,guard,body,annot)] -> body
    | [] ->
        raise (Reporting_basic.err_unreachable l
            "if_exp given empty list in rewrite_guarded_clauses")) in
  group cs

let bitwise_and_exp exp1 exp2 =
  let (E_aux (_,(l,_))) = exp1 in
  let andid = Id_aux (Id "and_bool", gen_loc l) in
  annot_exp (E_app(andid,[exp1;exp2])) l (env_of exp1) bool_typ

let compose_guard_opt g1 g2 = match g1, g2 with
  | Some g1, Some g2 -> Some (bitwise_and_exp g1 g2)
  | Some g1, None -> Some g1
  | None, Some g2 -> Some g2
  | None, None -> None

let rec contains_bitvector_pat (P_aux (pat,annot)) = match pat with
| P_lit _ | P_wild | P_id _ -> false
| P_as (pat,_) | P_typ (_,pat) | P_var (pat,_) -> contains_bitvector_pat pat
| P_vector _ | P_vector_concat _ ->
    let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
    is_bitvector_typ typ
| P_app (_,pats) | P_tup pats | P_list pats ->
    List.exists contains_bitvector_pat pats
| P_cons (p,ps) -> contains_bitvector_pat p || contains_bitvector_pat ps
| P_record (fpats,_) ->
    List.exists (fun (FP_aux (FP_Fpat (_,pat),_)) -> contains_bitvector_pat pat) fpats

let contains_bitvector_pexp = function
| Pat_aux (Pat_exp (pat,_),_) | Pat_aux (Pat_when (pat,_,_),_) ->
  contains_bitvector_pat pat

(* Rewrite bitvector patterns to guarded patterns *)

let remove_bitvector_pat (P_aux (_, (l, _)) as pat) =

  let env = try pat_env_of pat with _ -> Env.empty in

  (* first introduce names for bitvector patterns *)
  let name_bitvector_roots =
    { p_lit = (fun lit -> P_lit lit)
    ; p_typ = (fun (typ,p) -> P_typ (typ,p false))
    ; p_wild = P_wild
    ; p_as = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_var = (fun (pat,kid) -> P_var (pat true,kid))
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_tup            = (fun ps -> P_tup (List.map (fun p -> p false) ps))
    ; p_list           = (fun ps -> P_list (List.map (fun p -> p false) ps))
    ; p_cons           = (fun (p,ps) -> P_cons (p false, ps false))
    ; p_aux =
        (fun (pat,annot) contained_in_p_as ->
          let env = env_of_annot annot in
          let t = Env.base_typ_of env (typ_of_annot annot) in
          let (l,_) = annot in
          match pat, is_bitvector_typ t, contained_in_p_as with
          | P_vector _, true, false ->
            P_aux (P_as (P_aux (pat,annot),fresh_id "b__" l), annot)
          | _ -> P_aux (pat,annot)
        )
    ; fP_aux = (fun (fpat,annot) -> FP_aux (fpat,annot))
    ; fP_Fpat = (fun (id,p) -> FP_Fpat (id,p false))
    } in
  let pat, env = bind_pat_no_guard env
    (strip_pat ((fold_pat name_bitvector_roots pat) false))
    (pat_typ_of pat) in

  (* Then collect guard expressions testing whether the literal bits of a
     bitvector pattern match those of a given bitvector, and collect let
     bindings for the bits bound by P_id or P_as patterns *)

  (* Helper functions for generating guard expressions *)
  let mk_exp e_aux = E_aux (e_aux, (l, ())) in
  let mk_num_exp i = mk_lit_exp (L_num i) in
  let check_eq_exp l r =
    let exp = mk_exp (E_app_infix (l, Id_aux (DeIid "==", Parse_ast.Unknown), r)) in
    check_exp env exp bool_typ in

  let access_bit_exp rootid l typ idx =
    let access_aux = E_vector_access (mk_exp (E_id rootid), mk_num_exp idx) in
    check_exp env (mk_exp access_aux) bit_typ in

  let test_bit_exp rootid l typ idx exp =
    let elem = access_bit_exp rootid l typ idx in
    Some (check_eq_exp (strip_exp elem) (strip_exp exp)) in

  let test_subvec_exp rootid l typ i j lits =
    let (start, length, ord, _) = vector_typ_args_of typ in
    let subvec_exp =
      match start, length with
      | Nexp_aux (Nexp_constant s, _), Nexp_aux (Nexp_constant l, _)
        when Big_int.equal s i && Big_int.equal l (Big_int.of_int (List.length lits)) ->
         mk_exp (E_id rootid)
      | _ ->
         mk_exp (E_vector_subrange (mk_exp (E_id rootid), mk_num_exp i, mk_num_exp j)) in
    check_eq_exp subvec_exp (mk_exp (E_vector (List.map strip_exp lits))) in

  let letbind_bit_exp rootid l typ idx id =
    let rannot = simple_annot l typ in
    let elem = access_bit_exp rootid l typ idx in
    let e = annot_pat (P_id id) l env bit_typ in
    let letbind = LB_aux (LB_val (e,elem), (l, Some (env, bit_typ, no_effect))) in
    let letexp = (fun body ->
      let (E_aux (_,(_,bannot))) = body in
      if IdSet.mem id (find_used_vars body)
      then annot_exp (E_let (letbind,body)) l env (typ_of body)
      else body) in
    (letexp, letbind) in

  let compose_guards guards = List.fold_right compose_guard_opt guards None in

  let flatten_guards_decls gd =
    let (guards,decls,letbinds) = Util.split3 gd in
    (compose_guards guards, (List.fold_right (@@) decls), List.flatten letbinds) in

  (* Collect guards and let bindings *)
  let guard_bitvector_pat =
    let collect_guards_decls ps rootid t =
      let (start,_,ord,_) = vector_typ_args_of t in
      let start_idx = match start with
      | Nexp_aux (Nexp_constant s, _) -> s
      | _ ->
        raise (Reporting_basic.err_unreachable l
          "guard_bitvector_pat called on pattern with non-constant start index") in
      let add_bit_pat (idx, current, guards, dls) pat =
        let idx' =
          if is_order_inc ord
          then Big_int.add idx (Big_int.of_int 1)
          else Big_int.sub idx (Big_int.of_int 1) in
        let ids = fst (fold_pat
          { (compute_pat_alg IdSet.empty IdSet.union) with
            p_id = (fun id -> IdSet.singleton id, P_id id);
            p_as = (fun ((ids, pat), id) -> IdSet.add id ids, P_as (pat, id)) }
          pat) in
        let lits = fst (fold_pat
          { (compute_pat_alg [] (@)) with
            p_aux = (fun ((lits, paux), (l, annot)) ->
                       let lits = match paux with
                         | P_lit lit -> E_aux (E_lit lit, (l, annot)) :: lits
                         | _ -> lits in
                       lits, P_aux (paux, (l, annot))) }
          pat) in
        let add_letbind id dls = dls @ [letbind_bit_exp rootid l t idx id] in
        let dls' = IdSet.fold add_letbind ids dls in
        let current', guards' =
          match current with
          | Some (l, i, j, lits') ->
             if lits = []
             then None, guards @ [Some (test_subvec_exp rootid l t i j lits')]
             else Some (l, i, idx, lits' @ lits), guards
          | None ->
             begin
               match lits with
               | E_aux (_, (l, _)) :: _ -> Some (l, idx, idx, lits), guards
               | [] -> None, guards
             end
          in
        (idx', current', guards', dls') in
      let (_, final, guards, dls) = List.fold_left add_bit_pat (start_idx, None, [], []) ps in
      let guards = match final with
        | Some (l,i,j,lits) ->
           guards @ [Some (test_subvec_exp rootid l t i j lits)]
        | None -> guards in
      let (decls,letbinds) = List.split dls in
      (compose_guards guards, List.fold_right (@@) decls, letbinds) in

    let collect_guards_decls_indexed ips rootid t =
      let rec guard_decl (idx,pat) = (match pat with
        | P_aux (P_lit lit, (l,annot)) ->
          let exp = E_aux (E_lit lit, (l,annot)) in
          (test_bit_exp rootid l t idx exp, (fun b -> b), [])
        | P_aux (P_as (pat',id), (l,annot)) ->
          let (guard,decls,letbinds) = guard_decl (idx,pat') in
          let (letexp,letbind) = letbind_bit_exp rootid l t idx id in
          (guard, decls >> letexp, letbind :: letbinds)
        | P_aux (P_id id, (l,annot)) ->
          let (letexp,letbind) = letbind_bit_exp rootid l t idx id in
          (None, letexp, [letbind])
        | _ -> (None, (fun b -> b), [])) in
      let (guards,decls,letbinds) = Util.split3 (List.map guard_decl ips) in
      (compose_guards guards, List.fold_right (@@) decls, List.flatten letbinds) in

    { p_lit            = (fun lit -> (P_lit lit, (None, (fun b -> b), [])))
    ; p_wild           = (P_wild, (None, (fun b -> b), []))
    ; p_as             = (fun ((pat,gdls),id) -> (P_as (pat,id), gdls))
    ; p_typ            = (fun (typ,(pat,gdls)) -> (P_typ (typ,pat), gdls))
    ; p_id             = (fun id -> (P_id id, (None, (fun b -> b), [])))
    ; p_var            = (fun ((pat,gdls),kid) -> (P_var (pat,kid), gdls))
    ; p_app            = (fun (id,ps) -> let (ps,gdls) = List.split ps in
                                         (P_app (id,ps), flatten_guards_decls gdls))
    ; p_record         = (fun (ps,b) -> let (ps,gdls) = List.split ps in
                                        (P_record (ps,b), flatten_guards_decls gdls))
    ; p_vector         = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_vector ps, flatten_guards_decls gdls))
    ; p_vector_concat  = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_vector_concat ps, flatten_guards_decls gdls))
    ; p_tup            = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_tup ps, flatten_guards_decls gdls))
    ; p_list           = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_list ps, flatten_guards_decls gdls))
    ; p_cons           = (fun ((p,gdls),(p',gdls')) ->
                          (P_cons (p,p'), flatten_guards_decls [gdls;gdls']))
    ; p_aux            = (fun ((pat,gdls),annot) ->
                           let env = env_of_annot annot in
                           let t = Env.base_typ_of env (typ_of_annot annot) in
                           (match pat, is_bitvector_typ t with
                           | P_as (P_aux (P_vector ps, _), id), true ->
                             (P_aux (P_id id, annot), collect_guards_decls ps id t)
                           | _, _ -> (P_aux (pat,annot), gdls)))
    ; fP_aux           = (fun ((fpat,gdls),annot) -> (FP_aux (fpat,annot), gdls))
    ; fP_Fpat          = (fun (id,(pat,gdls)) -> (FP_Fpat (id,pat), gdls))
    } in
  fold_pat guard_bitvector_pat pat

let rewrite_exp_remove_bitvector_pat rewriters (E_aux (exp,(l,annot)) as full_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_case (e,ps)
    when List.exists contains_bitvector_pexp ps ->
    let rewrite_pexp = function
     | Pat_aux (Pat_exp (pat,body),annot') ->
       let (pat',(guard',decls,_)) = remove_bitvector_pat pat in
       let body' = decls (rewrite_rec body) in
       (match guard' with
       | Some guard' -> Pat_aux (Pat_when (pat', guard', body'), annot')
       | None -> Pat_aux (Pat_exp (pat', body'), annot'))
     | Pat_aux (Pat_when (pat,guard,body),annot') ->
       let (pat',(guard',decls,_)) = remove_bitvector_pat pat in
       let body' = decls (rewrite_rec body) in
       (match guard' with
       | Some guard' -> Pat_aux (Pat_when (pat', bitwise_and_exp (decls guard) guard', body'), annot')
       | None -> Pat_aux (Pat_when (pat', (decls guard), body'), annot')) in
    rewrap (E_case (e, List.map rewrite_pexp ps))
  | E_let (LB_aux (LB_val (pat,v),annot'),body) ->
     let (pat,(_,decls,_)) = remove_bitvector_pat pat in
     rewrap (E_let (LB_aux (LB_val (pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | _ -> rewrite_base full_exp

let rewrite_fun_remove_bitvector_pat
      rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) =
  let _ = reset_fresh_name_counter () in
  let funcls = match funcls with
    | (FCL_aux (FCL_Funcl(id,_),_) :: _) ->
        let clause (FCL_aux (FCL_Funcl(_,pexp),annot)) =
          let pat,fguard,exp,pannot = destruct_pexp pexp in
          let (pat,(guard,decls,_)) = remove_bitvector_pat pat in
          let guard = match guard,fguard with
            | None,e | e,None -> e
            | Some g, Some wh ->
               Some (bitwise_and_exp g (decls (rewriters.rewrite_exp rewriters wh)))
          in
          let exp = decls (rewriters.rewrite_exp rewriters exp) in
          FCL_aux (FCL_Funcl (id,construct_pexp (pat,guard,exp,annot)),annot) in
        List.map clause funcls
    | _ -> funcls in
  FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))

let rewrite_defs_remove_bitvector_pats (Defs defs) =
  let rewriters =
    {rewrite_exp = rewrite_exp_remove_bitvector_pat;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun_remove_bitvector_pat;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base } in
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_val (LB_aux (LB_val (pat,exp),a)) ->
       let (pat',(_,_,letbinds)) = remove_bitvector_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val (pat',exp),a))] @ defvals
    | d -> [d] in
  (* FIXME See above in rewrite_sizeof *)
  (* fst (check initial_env ( *)
    Defs (List.flatten (List.map rewrite_def defs))
    (* )) *)

(* Rewrite literal number patterns to guarded patterns
   Those numeral patterns are not handled very well by Lem (or Isabelle)
 *)
let rewrite_defs_remove_numeral_pats =
  let p_lit = function
    | L_aux (L_num n, l) ->
       let id = fresh_id "l__" Parse_ast.Unknown in
       let annot_exp e_aux typ = E_aux (e_aux, simple_annot l typ) in
       let guard =
         annot_exp (E_app_infix (
           annot_exp (E_id id) (atom_typ (nconstant n)),
           mk_id "==",
           simple_num l n
         )) bool_typ in
       (Some guard, P_id id)
    | lit -> (None, P_lit lit) in
  let guard_pat =
    fold_pat { (compute_pat_alg None compose_guard_opt) with p_lit = p_lit } in
  let pat_aux (pexp_aux, a) =
    let pat,guard,exp,a = destruct_pexp (Pat_aux (pexp_aux, a)) in
    let guard',pat = match guard_pat pat with
      | Some g, pat ->
         let pat, env = bind_pat_no_guard (env_of exp) (strip_pat pat) (pat_typ_of pat) in
         Some (check_exp env (strip_exp g) (typ_of g)), pat
      | None, pat -> None, pat in
    match compose_guard_opt guard guard' with
    | Some g -> Pat_aux (Pat_when (pat, g, exp), a)
    | None -> Pat_aux (Pat_exp (pat, exp), a) in
  let exp_alg = { id_exp_alg with pat_aux = pat_aux } in
  let rewrite_exp _ = fold_exp exp_alg in
  let rewrite_funcl (FCL_aux (FCL_Funcl (id, pexp), annot)) =
    FCL_aux (FCL_Funcl (id, fold_pexp exp_alg pexp), annot) in
  let rewrite_fun _ (FD_aux (FD_function (r_o, t_o, e_o, funcls), a)) =
    FD_aux (FD_function (r_o, t_o, e_o, List.map rewrite_funcl funcls), a) in
  rewrite_defs_base
    { rewriters_base with rewrite_exp = rewrite_exp; rewrite_fun = rewrite_fun }

(* Remove pattern guards by rewriting them to if-expressions within the
   pattern expression. *)
let rewrite_exp_guarded_pats rewriters (E_aux (exp,(l,annot)) as full_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  let is_guarded_pexp = function
  | Pat_aux (Pat_when (_,_,_),_) -> true
  | _ -> false in
  match exp with
  | E_case (e,ps)
    when List.exists is_guarded_pexp ps ->
    let clause = function
    | Pat_aux (Pat_exp (pat, body), annot) ->
      (pat, None, rewrite_rec body, annot)
    | Pat_aux (Pat_when (pat, guard, body), annot) ->
      (pat, Some guard, rewrite_rec body, annot) in
    let clauses = rewrite_guarded_clauses l (List.map clause ps) in
    if (effectful e) then
      let e = rewrite_rec e in
      let (E_aux (_,(el,eannot))) = e in
      let pat_e' = fresh_id_pat "p__" (el, Some (env_of e, typ_of e, no_effect)) in
      let exp_e' = pat_to_exp pat_e' in
      let letbind_e = LB_aux (LB_val (pat_e',e), (el,eannot)) in
      let exp' = case_exp exp_e' (typ_of full_exp) clauses in
      rewrap (E_let (letbind_e, exp'))
    else case_exp e (typ_of full_exp) clauses
  | _ -> rewrite_base full_exp

let rewrite_fun_guarded_pats rewriters (FD_aux (FD_function (r,t,e,funcls),(l,fdannot))) =
   let funcls = match funcls with
    | (FCL_aux (FCL_Funcl(id,_),_) :: _) ->
       let clause (FCL_aux (FCL_Funcl(_,pexp),annot)) =
         let pat,guard,exp,_ = destruct_pexp pexp in
         let exp = rewriters.rewrite_exp rewriters exp in
         (pat,guard,exp,annot) in
       let cs = rewrite_guarded_clauses l (List.map clause funcls) in
       List.map (fun (pat,exp,annot) ->
         FCL_aux (FCL_Funcl(id,construct_pexp (pat,None,exp,(Parse_ast.Unknown,None))),annot)) cs
     | _ -> funcls (* TODO is the empty list possible here? *) in
   FD_aux (FD_function(r,t,e,funcls),(l,fdannot))

let rewrite_defs_guarded_pats =
  rewrite_defs_base { rewriters_base with rewrite_exp = rewrite_exp_guarded_pats;
                    rewrite_fun = rewrite_fun_guarded_pats }


let rec rewrite_lexp_to_rhs ((LEXP_aux(lexp,((l,_) as annot))) as le) =
  match lexp with
  | LEXP_id _ | LEXP_cast (_, _) | LEXP_tup _ | LEXP_deref _ -> (le, (fun exp -> exp))
  | LEXP_vector (lexp, e) ->
     let (lhs, rhs) = rewrite_lexp_to_rhs lexp in
     (lhs, (fun exp -> rhs (E_aux (E_vector_update (lexp_to_exp lexp, e, exp), annot))))
  | LEXP_vector_range (lexp, e1, e2) ->
     let (lhs, rhs) = rewrite_lexp_to_rhs lexp in
     (lhs, (fun exp -> rhs (E_aux (E_vector_update_subrange (lexp_to_exp lexp, e1, e2, exp), annot))))
  | LEXP_field (lexp, id) ->
     begin
       let (lhs, rhs) = rewrite_lexp_to_rhs lexp in
       let (LEXP_aux (_, lannot)) = lexp in
       let env = env_of_annot lannot in
       match Env.expand_synonyms env (typ_of_annot lannot) with
       | Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _) when Env.is_record rectyp_id env ->
          let field_update exp = FES_aux (FES_Fexps ([FE_aux (FE_Fexp (id, exp), annot)], false), annot) in
          (lhs, (fun exp -> rhs (E_aux (E_record_update (lexp_to_exp lexp, field_update exp), lannot))))
       | _ -> raise (Reporting_basic.err_unreachable l ("Unsupported lexp: " ^ string_of_lexp le))
     end
  | _ -> raise (Reporting_basic.err_unreachable l ("Unsupported lexp: " ^ string_of_lexp le))

let updates_vars exp =
  let e_assign ((_, lexp), (u, exp)) =
    (u || lexp_is_local lexp (env_of exp), E_assign (lexp, exp)) in
  fst (fold_exp { (compute_exp_alg false (||)) with e_assign = e_assign } exp)

(*Expects to be called after rewrite_defs; thus the following should not appear:
  internal_exp of any form
  lit vectors in patterns or expressions
 *)
let rewrite_exp_lift_assign_intro rewriters ((E_aux (exp,((l,_) as annot))) as full_exp) =
  let rewrap e = E_aux (e,annot) in
  let rewrap_effects e eff =
    E_aux (e, (l,Some (env_of_annot annot, typ_of_annot annot, eff))) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_block exps ->
    let rec walker exps = match exps with
      | [] -> []
      | (E_aux(E_assign(le,e), ((l, Some (env,typ,eff)) as annot)) as exp)::exps
        when lexp_is_local_intro le env && not (lexp_is_effectful le) ->
        let (le', re') = rewrite_lexp_to_rhs le in
        let e' = re' (rewrite_base e) in
        let exps' = walker exps in
        let effects = union_eff_exps exps' in
        let block = E_aux (E_block exps', (l, Some (env, unit_typ, effects))) in
        [fix_eff_exp (E_aux (E_var(le', e', block), annot))]
      (*| ((E_aux(E_if(c,t,e),(l,annot))) as exp)::exps ->
        let vars_t = introduced_variables t in
        let vars_e = introduced_variables e in
        let new_vars = Envmap.intersect vars_t vars_e in
        if Envmap.is_empty new_vars
         then (rewrite_base exp)::walker exps
         else
           let new_nmap = match nmap with
             | None -> Some(Nexpmap.empty,new_vars)
             | Some(nm,s) -> Some(nm, Envmap.union new_vars s) in
           let c' = rewrite_base c in
           let t' = rewriters.rewrite_exp rewriters new_nmap t in
           let e' = rewriters.rewrite_exp rewriters new_nmap e in
           let exps' = walker exps in
           fst ((Envmap.fold 
                  (fun (res,effects) i (t,e) ->
                let bitlit =  E_aux (E_lit (L_aux(L_zero, Parse_ast.Generated l)),
                                     (Parse_ast.Generated l, simple_annot bit_t)) in
                let rangelit = E_aux (E_lit (L_aux (L_num 0, Parse_ast.Generated l)),
                                      (Parse_ast.Generated l, simple_annot nat_t)) in
                let set_exp =
                  match t.t with
                  | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) -> bitlit
                  | Tapp("range", _) | Tapp("atom", _) -> rangelit
                  | Tapp("vector", [_;_;_;TA_typ ( {t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})})])
                  | Tapp(("reg"|"register"),[TA_typ ({t = Tapp("vector",
                                                               [_;_;_;TA_typ ( {t=Tid "bit"}
                                                                             | {t=Tabbrev(_,{t=Tid "bit"})})])})])
                  | Tabbrev(_,{t = Tapp("vector",
                                        [_;_;_;TA_typ ( {t=Tid "bit"}
                                                      | {t=Tabbrev(_,{t=Tid "bit"})})])}) ->
                    E_aux (E_vector_indexed([], Def_val_aux(Def_val_dec bitlit,
                                                            (Parse_ast.Generated l,simple_annot bit_t))),
                           (Parse_ast.Generated l, simple_annot t))
                  | _ -> e in
                let unioneffs = union_effects effects (get_effsum_exp set_exp) in
                ([E_aux (E_var (LEXP_aux (LEXP_id (Id_aux (Id i, Parse_ast.Generated l)),
                                                  (Parse_ast.Generated l, (tag_annot t Emp_intro))),
                                        set_exp,
                                        E_aux (E_block res, (Parse_ast.Generated l, (simple_annot_efr unit_t effects)))),
                        (Parse_ast.Generated l, simple_annot_efr unit_t unioneffs))],unioneffs)))
             (E_aux(E_if(c',t',e'),(Parse_ast.Generated l, annot))::exps',eff_union_exps (c'::t'::e'::exps')) new_vars)*)
      | e::exps -> (rewrite_rec e)::(walker exps)
    in
    check_exp (env_of full_exp)
      (E_aux (E_block (List.map strip_exp (walker exps)), (l, ()))) (typ_of full_exp)
  | E_assign(le,e)
    when lexp_is_local_intro le (env_of full_exp) && not (lexp_is_effectful le) ->
    let (le', re') = rewrite_lexp_to_rhs le in
    let e' = re' (rewrite_base e) in
    let block = annot_exp (E_block []) l (env_of full_exp) unit_typ in
    check_exp (env_of full_exp)
      (strip_exp (E_aux (E_var(le', e', block), annot))) (typ_of full_exp)
  | _ -> rewrite_base full_exp

let rewrite_lexp_lift_assign_intro rewriters ((LEXP_aux(lexp,annot)) as le) =
  let rewrap le = LEXP_aux(le,annot) in
  let rewrite_base = rewrite_lexp rewriters in
  match lexp, annot with
  | (LEXP_id id | LEXP_cast (_,id)), (l, Some (env, typ, eff)) ->
    (match Env.lookup_id id env with
    | Unbound | Local _ ->
      LEXP_aux (lexp, (l, Some (env, typ, union_effects eff (mk_effect [BE_lset]))))
    | _ -> rewrap lexp)
  | _ -> rewrite_base le


let rewrite_defs_exp_lift_assign defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_lift_assign_intro;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp_lift_assign_intro;
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs


(* Rewrite assignments to register references into calls to a builtin function
   "write_reg_ref" (in the Lem shallow embedding). For example, if GPR is a
   vector of register references, then
     GPR[i] := exp;
   becomes
     write_reg_ref (vector_access (GPR, i)) exp
 *)
let rewrite_register_ref_writes (Defs defs) =
  let (Defs write_reg_spec) = fst (check Env.empty (Defs (List.map gen_vs
    [("write_reg_ref", "forall ('a : Type). (register('a), 'a) -> unit effect {wreg}")]))) in
  let lexp_ref_exp (LEXP_aux (_, annot) as lexp) =
    try
      let exp = infer_exp (env_of_annot annot) (strip_exp (lexp_to_exp lexp)) in
      if is_reftyp (typ_of exp) then Some exp else None
    with | _ -> None in
  let e_assign (lexp, exp) =
    let (lhs, rhs) = rewrite_lexp_to_rhs lexp in
    match lexp_ref_exp lhs with
    | Some (E_aux (_, annot) as lhs_exp) ->
       let lhs = LEXP_aux (LEXP_memory (mk_id "write_reg_ref", [lhs_exp]), annot) in
       E_assign (lhs, rhs exp)
    | None -> E_assign (lexp, exp) in
  let rewrite_exp _ = fold_exp { id_exp_alg with e_assign = e_assign } in

  let rewriters = { rewriters_base with rewrite_exp = rewrite_exp } in
  let rec rewrite ds = match ds with
    | d::ds -> (rewriters.rewrite_def rewriters d)::(rewrite ds)
    | [] -> [] in
  Defs (rewrite (write_reg_spec @ defs))

  (* rewrite_defs_base { rewriters_base with rewrite_exp = rewrite_exp }
    (Defs (write_reg_spec @ defs)) *)


(*let rewrite_exp_separate_ints rewriters ((E_aux (exp,((l,_) as annot))) as full_exp) =
  (*let tparms,t,tag,nexps,eff,cum_eff,bounds = match annot with
    | Base((tparms,t),tag,nexps,eff,cum_eff,bounds) -> tparms,t,tag,nexps,eff,cum_eff,bounds
    | _ -> [],unit_t,Emp_local,[],pure_e,pure_e,nob in*)
  let rewrap e = E_aux (e,annot) in
  (*let rewrap_effects e effsum =
    E_aux (e,(l,Base ((tparms,t),tag,nexps,eff,effsum,bounds))) in*)
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_lit (L_aux (((L_num _) as lit),_)) ->
    (match (is_within_machine64 t nexps) with
     | Yes -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int yes\n" in rewrite_base full_exp
     | Maybe -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int maybe\n" in rewrite_base full_exp
     | No -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int no\n" in E_aux(E_app(Id_aux (Id "integer_of_int",l),[rewrite_base full_exp]),
                   (l, Base((tparms,t),External(None),nexps,eff,cum_eff,bounds))))
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite_rec exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite_rec exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite_rec el,id,rewrite_rec er))
  | E_for (id, e1, e2, e3, o, body) ->
      rewrap (E_for (id, rewrite_rec e1, rewrite_rec e2, rewrite_rec e3, o, rewrite_rec body))
  | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite_rec vec,rewrite_rec index))
  | E_vector_subrange (vec,i1,i2) ->
    rewrap (E_vector_subrange (rewrite_rec vec,rewrite_rec i1,rewrite_rec i2))
  | E_vector_update (vec,index,new_v) -> 
    rewrap (E_vector_update (rewrite_rec vec,rewrite_rec index,rewrite_rec new_v))
  | E_vector_update_subrange (vec,i1,i2,new_v) ->
    rewrap (E_vector_update_subrange (rewrite_rec vec,rewrite_rec i1,rewrite_rec i2,rewrite_rec new_v))
  | E_case (exp ,pexps) -> 
    rewrap (E_case (rewrite_rec exp,
                    (List.map 
                       (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
                          Pat_aux (Pat_exp(rewriters.rewrite_pat rewriters nmap p,rewrite_rec e),pannot)) pexps)))
  | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters nmap letbind,rewrite_rec body))
  | E_var (lexp,exp,body) ->
    rewrap (E_var (rewriters.rewrite_lexp rewriters nmap lexp, rewrite_rec exp, rewrite_rec body))
  | _ -> rewrite_base full_exp

let rewrite_defs_separate_numbs defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_separate_ints;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let; (*will likely need a new one?*)
     rewrite_lexp = rewrite_lexp; (*will likely need a new one?*)
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs*)

(* Remove redundant return statements, and translate remaining ones into an
   (effectful) call to builtin function "early_return" (in the Lem shallow
   embedding).

   TODO: Maybe separate generic removal of redundant returns, and Lem-specific
   rewriting of early returns
 *)
let rewrite_defs_early_return (Defs defs) =
  let is_unit (E_aux (exp, _)) = match exp with
  | E_lit (L_aux (L_unit, _)) -> true
  | _ -> false in

  let is_return (E_aux (exp, _)) = match exp with
  | E_return _ -> true
  | _ -> false in

  let get_return (E_aux (e, (l, _)) as exp) = match e with
  | E_return e -> e
  | _ -> exp in

  let e_if (e1, e2, e3) =
    if is_return e2 && is_return e3 then
      let (E_aux (_, annot)) = get_return e2 in
      E_return (E_aux (E_if (e1, get_return e2, get_return e3), annot))
    else E_if (e1, e2, e3) in

  let rec e_block es =
    (* If one of the branches of an if-expression in a block is an early
       return, fold the rest of the block after the if-expression into the
       other branch *)
    let fold_if_return exp block = match exp with
      | E_aux (E_if (c, t, (E_aux (_, annot) as e)), _) when is_return t ->
         let annot = match block with
           | [] -> annot
           | _ -> let (E_aux (_, annot)) = Util.last block in annot
         in
         let block = if is_unit e then block else e :: block in
         let e' = E_aux (e_block block, annot) in
         [E_aux (e_if (c, t, e'), annot)]
      | E_aux (E_if (c, (E_aux (_, annot) as t), e), _) when is_return e ->
         let annot = match block with
           | [] -> annot
           | _ -> let (E_aux (_, annot)) = Util.last block in annot
         in
         let block = if is_unit t then block else t :: block in
         let t' = E_aux (e_block block, annot) in
         [E_aux (e_if (c, t', e), annot)]
      | _ -> exp :: block in
    let es = List.fold_right fold_if_return es [] in
    match es with
    | [E_aux (e, _)] -> e
    | _ :: _ when is_return (Util.last es) ->
       let (E_aux (_, annot) as e) = get_return (Util.last es) in
       E_return (E_aux (E_block (Util.butlast es @ [get_return e]), annot))
    | _ -> E_block es in

  let e_case (e, pes) =
    let is_return_pexp (Pat_aux (pexp, _)) = match pexp with
    | Pat_exp (_, e) | Pat_when (_, _, e) -> is_return e in
    let get_return_pexp (Pat_aux (pexp, a)) = match pexp with
    | Pat_exp (p, e) -> Pat_aux (Pat_exp (p, get_return e), a)
    | Pat_when (p, g, e) -> Pat_aux (Pat_when (p, g, get_return e), a) in
    let annot = match List.map get_return_pexp pes with
    | Pat_aux (Pat_exp (_, E_aux (_, annot)), _) :: _ -> annot
    | Pat_aux (Pat_when (_, _, E_aux (_, annot)), _) :: _ -> annot
    | [] -> (Parse_ast.Unknown, None) in
    if List.for_all is_return_pexp pes
    then E_return (E_aux (E_case (e, List.map get_return_pexp pes), annot))
    else E_case (e, pes) in

  let e_let (lb, exp) =
    let (E_aux (_, annot) as ret_exp) = get_return exp in
    if is_return exp then E_return (E_aux (E_let (lb, ret_exp), annot))
    else E_let (lb, exp) in

  let e_internal_let (lexp, exp1, exp2) =
    let (E_aux (_, annot) as ret_exp2) = get_return exp2 in
    if is_return exp2 then
      E_return (E_aux (E_var (lexp, exp1, ret_exp2), annot))
    else E_var (lexp, exp1, exp2) in

  let e_aux (exp, (l, annot)) =
    let full_exp = propagate_exp_effect (E_aux (exp, (l, annot))) in
    let env = env_of full_exp in
    match full_exp with
    | E_aux (E_return exp, (l, Some (env, typ, eff))) ->
      (* Add escape effect annotation, since we use the exception mechanism
         of the state monad to implement early return in the Lem backend *)
      let annot' = Some (env, typ, union_effects eff (mk_effect [BE_escape])) in
      let exp' = annot_exp (E_cast (typ_of exp, exp)) l env (typ_of exp) in
      E_aux (E_app (mk_id "early_return", [exp']), (l, annot'))
    | _ -> full_exp in

  let rewrite_funcl_early_return _ (FCL_aux (FCL_Funcl (id, pexp), a)) =
    let pat,guard,exp,pannot = destruct_pexp pexp in
    (* Try to pull out early returns as far as possible *)
    let exp' =
      fold_exp
        { id_exp_alg with e_block = e_block; e_if = e_if; e_case = e_case;
          e_let = e_let; e_internal_let = e_internal_let }
        exp in
    (* Remove early return if we can pull it out completely, and rewrite
       remaining early returns to "early_return" calls *)
    let exp =
      fold_exp
        { id_exp_alg with e_aux = e_aux }
        (if is_return exp' then get_return exp' else exp) in
    let a = match a with
    | (l, Some (env, typ, eff)) ->
      (l, Some (env, typ, union_effects eff (effect_of exp)))
    | _ -> a in
    FCL_aux (FCL_Funcl (id, construct_pexp (pat, guard, exp, pannot)), a) in

  let rewrite_fun_early_return rewriters
    (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), a)) =
    FD_aux (FD_function (rec_opt, tannot_opt, effect_opt,
      List.map (rewrite_funcl_early_return rewriters) funcls), a) in

  let (Defs early_ret_spec) = fst (check Env.empty (Defs [gen_vs
    ("early_return", "forall ('a : Type) ('b : Type). 'a -> 'b effect {escape}")])) in

  rewrite_defs_base
    { rewriters_base with rewrite_fun = rewrite_fun_early_return }
    (Defs (early_ret_spec @ defs))

(* Propagate effects of functions, if effect checking and propagation
   have not been performed already by the type checker. *)
let rewrite_fix_val_specs (Defs defs) =
  let find_vs env val_specs id =
    try Bindings.find id val_specs with
    | Not_found ->
       begin
         try Env.get_val_spec id env with
         | _ ->
            raise (Reporting_basic.err_unreachable (Parse_ast.Unknown)
              ("No val spec found for " ^ string_of_id id))
       end
  in

  let add_eff_to_vs eff = function
    | (tq, Typ_aux (Typ_fn (args_t, ret_t, eff'), a)) ->
      (tq, Typ_aux (Typ_fn (args_t, ret_t, union_effects eff eff'), a))
    | vs -> vs
  in

  let eff_of_vs = function
    | (tq, Typ_aux (Typ_fn (args_t, ret_t, eff), a)) -> eff
    | _ -> no_effect
  in

  let e_aux val_specs (exp, (l, annot)) =
    match fix_eff_exp (E_aux (exp, (l, annot))) with
    | E_aux (E_app_infix (_, f, _) as exp, (l, Some (env, typ, eff)))
    | E_aux (E_app (f, _) as exp, (l, Some (env, typ, eff))) ->
       let vs = find_vs env val_specs f in
       let env = Env.update_val_spec f vs env in
       E_aux (exp, (l, Some (env, typ, union_effects eff (eff_of_vs vs))))
    | e_aux -> e_aux
  in

  let rewrite_exp val_specs = fold_exp { id_exp_alg with e_aux = e_aux val_specs } in

  let rewrite_funcl (val_specs, funcls) (FCL_aux (FCL_Funcl (id, pexp), (l, annot))) =
    let pat,guard,exp,pannot = destruct_pexp pexp in
    (* Assumes there are no effects in guards *)
    let exp = propagate_exp_effect (rewrite_exp val_specs exp) in
    let vs, eff = match find_vs (env_of_annot (l, annot)) val_specs id with
      | (tq, Typ_aux (Typ_fn (args_t, ret_t, eff), a)) ->
         let eff' = union_effects eff (effect_of exp) in
         let args_t' = rewrite_typ_nexp_ids (env_of exp) (pat_typ_of pat) in
         let ret_t' = rewrite_typ_nexp_ids (env_of exp) (typ_of exp) in
         (tq, Typ_aux (Typ_fn (args_t', ret_t', eff'), a)), eff'
      | _ -> assert false (* find_vs must return a function type *)
    in
    let annot = add_effect_annot annot eff in
    (Bindings.add id vs val_specs,
     funcls @ [FCL_aux (FCL_Funcl (id, construct_pexp (pat, guard, exp, pannot)), (l, annot))])
  in

  let rewrite_fundef (val_specs, FD_aux (FD_function (recopt, tannotopt, effopt, funcls), a)) =
    let (val_specs, funcls) = List.fold_left rewrite_funcl (val_specs, []) funcls in
    (* Repeat once to cross-propagate effects between clauses *)
    let (val_specs, funcls) = List.fold_left rewrite_funcl (val_specs, []) funcls in
    let is_funcl_rec (FCL_aux (FCL_Funcl (id, pexp), _)) =
      let pat,guard,exp,pannot = destruct_pexp pexp in
      let exp = match guard with None -> exp
        | Some exp' -> E_aux (E_block [exp';exp],(Parse_ast.Unknown,None)) in
      fst (fold_exp
        { (compute_exp_alg false (||) ) with
          e_app = (fun (f, es) ->
            let (rs, es) = List.split es in
            (List.fold_left (||) (string_of_id f = string_of_id id) rs,
             E_app (f, es)));
          e_app_infix = (fun ((r1,e1), f, (r2,e2)) ->
            (r1 || r2 || (string_of_id f = string_of_id id),
             E_app_infix (e1, f, e2))) }
        exp)
    in
    let recopt =
      if List.exists is_funcl_rec funcls then
        Rec_aux (Rec_rec, Parse_ast.Unknown)
      else recopt
    in
    let tannotopt = match tannotopt, funcls with
    | Typ_annot_opt_aux (Typ_annot_opt_some (typq, typ), l),
      FCL_aux (FCL_Funcl (_, Pat_aux ((Pat_exp (_, exp) | Pat_when (_, _, exp)), _)), _) :: _ ->
       Typ_annot_opt_aux (Typ_annot_opt_some (typq, rewrite_typ_nexp_ids (env_of exp) typ), l)
    | _ -> tannotopt in
    (val_specs, FD_aux (FD_function (recopt, tannotopt, effopt, funcls), a)) in

  let rec rewrite_fundefs (val_specs, fundefs) =
    match fundefs with
    | fundef :: fundefs ->
      let (val_specs, fundef) = rewrite_fundef (val_specs, fundef) in
      let (val_specs, fundefs) = rewrite_fundefs (val_specs, fundefs) in
      (val_specs, fundef :: fundefs)
    | [] -> (val_specs, []) in

  let rewrite_def (val_specs, defs) = function
    | DEF_fundef fundef ->
       let (val_specs, fundef) = rewrite_fundef (val_specs, fundef) in
       (val_specs, defs @ [DEF_fundef fundef])
    | DEF_internal_mutrec fundefs ->
       let (val_specs, fundefs) = rewrite_fundefs (val_specs, fundefs) in
       (val_specs, defs @ [DEF_internal_mutrec fundefs])
    | DEF_val (LB_aux (LB_val (pat, exp), a)) ->
       (val_specs, defs @ [DEF_val (LB_aux (LB_val (pat, rewrite_exp val_specs exp), a))])
    | DEF_spec (VS_aux (VS_val_spec (typschm, id, ext_opt, is_cast), a)) ->
       let typschm, val_specs =
         if Bindings.mem id val_specs then begin
           let (tq, typ) = Bindings.find id val_specs in
           TypSchm_aux (TypSchm_ts (tq, typ), Parse_ast.Unknown), val_specs
         end else begin
           let (TypSchm_aux (TypSchm_ts (tq, typ), _)) = typschm in
           (* Add rreg effect to internal _reg_deref function (cf. bitfield.ml) *)
           let vs =
             if string_of_id id = "_reg_deref" then
               add_eff_to_vs (mk_effect [BE_rreg]) (tq, typ)
             else (tq, typ) in
           typschm, Bindings.add id vs val_specs
         end
       in
       (val_specs, defs @ [DEF_spec (VS_aux (VS_val_spec (typschm, id, ext_opt, is_cast), a))])
    | def -> (val_specs, defs @ [def])
  in

  let rewrite_val_specs val_specs = function
    | DEF_spec (VS_aux (VS_val_spec (typschm, id, ext_opt, is_cast), a))
      when Bindings.mem id val_specs ->
       let typschm = match typschm with
         | TypSchm_aux (TypSchm_ts (tq, typ), l) ->
            let (tq, typ) = Bindings.find id val_specs in
            TypSchm_aux (TypSchm_ts (tq, typ), l)
       in
       DEF_spec (VS_aux (VS_val_spec (typschm, id, ext_opt, is_cast), a))
    | def -> def
  in

  let (val_specs, defs) = List.fold_left rewrite_def (Bindings.empty, []) defs in
  let defs = List.map (rewrite_val_specs val_specs) defs in

  (* if !Type_check.opt_no_effects
  then *)
  Defs defs
  (* else Defs defs *)

(* Turn constraints into numeric expressions with sizeof *)
let rewrite_constraint =
  let rec rewrite_nc (NC_aux (nc_aux, l)) = mk_exp (rewrite_nc_aux nc_aux)
  and rewrite_nc_aux = function
    | NC_bounded_ge (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id ">=", mk_exp (E_sizeof n2))
    | NC_bounded_le (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "<=", mk_exp (E_sizeof n2))
    | NC_equal (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "==", mk_exp (E_sizeof n2))
    | NC_not_equal (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "!=", mk_exp (E_sizeof n2))
    | NC_and (nc1, nc2) -> E_app_infix (rewrite_nc nc1, mk_id "&", rewrite_nc nc2)
    | NC_or (nc1, nc2) -> E_app_infix (rewrite_nc nc1, mk_id "|", rewrite_nc nc2)
    | NC_false -> E_lit (mk_lit L_false)
    | NC_true -> E_lit (mk_lit L_true)
    | NC_set (kid, []) -> E_lit (mk_lit (L_false))
    | NC_set (kid, int :: ints) ->
       let kid_eq kid int = nc_eq (nvar kid) (nconstant int) in
       unaux_exp (rewrite_nc (List.fold_left (fun nc int -> nc_or nc (kid_eq kid int)) (kid_eq kid int) ints))
  in
  let rewrite_e_aux (E_aux (e_aux, _) as exp) =
    match e_aux with
    | E_constraint nc ->
       check_exp (env_of exp) (rewrite_nc nc) bool_typ
    | _ -> exp
  in

  let rewrite_e_constraint = { id_exp_alg with e_aux = (fun (exp, annot) -> rewrite_e_aux (E_aux (exp, annot))) } in

  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_e_constraint) }

let rewrite_type_union_typs rw_typ (Tu_aux (tu, annot)) =
  match tu with
  | Tu_id id -> Tu_aux (Tu_id id, annot)
  | Tu_ty_id (typ, id) -> Tu_aux (Tu_ty_id (rw_typ typ, id), annot)

let rewrite_type_def_typs rw_typ rw_typquant rw_typschm (TD_aux (td, annot)) =
  match td with
  | TD_abbrev (id, nso, typschm) -> TD_aux (TD_abbrev (id, nso, rw_typschm typschm), annot)
  | TD_record (id, nso, typq, typ_ids, flag) ->
     TD_aux (TD_record (id, nso, rw_typquant typq, List.map (fun (typ, id) -> (rw_typ typ, id)) typ_ids, flag), annot)
  | TD_variant (id, nso, typq, tus, flag) ->
     TD_aux (TD_variant (id, nso, rw_typquant typq, List.map (rewrite_type_union_typs rw_typ) tus, flag), annot)
  | TD_enum (id, nso, ids, flag) -> TD_aux (TD_enum (id, nso, ids, flag), annot)
  | TD_bitfield _ -> assert false (* Processed before re-writing *)

(* FIXME: other reg_dec types *)
let rewrite_dec_spec_typs rw_typ (DEC_aux (ds, annot)) =
  match ds with
  | DEC_reg (typ, id) -> DEC_aux (DEC_reg (rw_typ typ, id), annot)
  | _ -> assert false

(* Remove overload definitions and cast val specs from the
   specification because the interpreter doesn't know about them.*)
let rewrite_overload_cast (Defs defs) =
  let remove_cast_vs (VS_aux (vs_aux, annot)) =
    match vs_aux with
    | VS_val_spec (typschm, id, ext, _) -> VS_aux (VS_val_spec (typschm, id, ext, false), annot)
  in
  let simple_def = function
    | DEF_spec vs -> DEF_spec (remove_cast_vs vs)
    | def -> def
  in
  let is_overload = function
    | DEF_overload _ -> true
    | _ -> false
  in
  let defs = List.map simple_def defs in
  Defs (List.filter (fun def -> not (is_overload def)) defs)


let rewrite_undefined mwords =
  let rewrite_e_aux (E_aux (e_aux, _) as exp) =
    match e_aux with
    | E_lit (L_aux (L_undef, l)) ->
       check_exp (env_of exp) (undefined_of_typ mwords l (fun _ -> ()) (Env.expand_synonyms (env_of exp) (typ_of exp))) (typ_of exp)
    | _ -> exp
  in
  let rewrite_exp_undefined = { id_exp_alg with e_aux = (fun (exp, annot) -> rewrite_e_aux (E_aux (exp, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp_undefined) }

let rec simple_typ (Typ_aux (typ_aux, l) as typ) = Typ_aux (simple_typ_aux typ_aux, l)
and simple_typ_aux = function
  | Typ_id id -> Typ_id id
  | Typ_app (id, [_; _; Typ_arg_aux (Typ_arg_typ typ, l)]) when Id.compare id (mk_id "vector") = 0 ->
     Typ_app (mk_id "list", [Typ_arg_aux (Typ_arg_typ (simple_typ typ), l)])
  | Typ_app (id, [_]) when Id.compare id (mk_id "atom") = 0 ->
     Typ_id (mk_id "int")
  | Typ_app (id, [_; _]) when Id.compare id (mk_id "range") = 0 ->
     Typ_id (mk_id "int")
  | Typ_app (id, args) -> Typ_app (id, List.concat (List.map simple_typ_arg args))
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (simple_typ typ1, simple_typ typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map simple_typ typs)
  | Typ_exist (_, _, Typ_aux (typ, l)) -> simple_typ_aux typ
  | typ_aux -> typ_aux
and simple_typ_arg (Typ_arg_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | Typ_arg_typ typ -> [Typ_arg_aux (Typ_arg_typ (simple_typ typ), l)]
  | _ -> []

(* This pass aims to remove all the Num quantifiers from the specification. *)
let rewrite_simple_types (Defs defs) =
  let is_simple = function
    | QI_aux (QI_id kopt, annot) as qi when is_typ_kopt kopt || is_order_kopt kopt -> true
    | _ -> false
  in
  let simple_typquant (TypQ_aux (tq_aux, annot)) =
    match tq_aux with
    | TypQ_no_forall -> TypQ_aux (TypQ_no_forall, annot)
    | TypQ_tq quants -> TypQ_aux (TypQ_tq (List.filter (fun q -> is_simple q) quants), annot)
  in
  let simple_typschm (TypSchm_aux (TypSchm_ts (typq, typ), annot)) =
    TypSchm_aux (TypSchm_ts (simple_typquant typq, simple_typ typ), annot)
  in
  let simple_vs (VS_aux (vs_aux, annot)) =
    match vs_aux with
    | VS_val_spec (typschm, id, ext, is_cast) -> VS_aux (VS_val_spec (simple_typschm typschm, id, ext, is_cast), annot)
  in
  let rec simple_lit (L_aux (lit_aux, l) as lit) =
    match lit_aux with
    | L_bin _ | L_hex _ ->
       E_list (List.map (fun b -> E_aux (E_lit b, simple_annot l bit_typ)) (vector_string_to_bit_list l lit_aux))
    | _ -> E_lit lit
  in
  let simple_def = function
    | DEF_spec vs -> DEF_spec (simple_vs vs)
    | DEF_type td -> DEF_type (rewrite_type_def_typs simple_typ simple_typquant simple_typschm td)
    | DEF_reg_dec ds -> DEF_reg_dec (rewrite_dec_spec_typs simple_typ ds)
    | def -> def
  in
  let simple_pat = {
      id_pat_alg with
      p_typ = (fun (typ, pat) -> P_typ (simple_typ typ, pat));
      p_var = (fun (pat, kid) -> unaux_pat pat);
      p_vector = (fun pats -> P_list pats)
    } in
  let simple_exp = {
      id_exp_alg with
      e_lit = simple_lit;
      e_vector = (fun exps -> E_list exps);
      e_cast = (fun (typ, exp) -> E_cast (simple_typ typ, exp));
      (* e_assert = (fun (E_aux (_, annot), str) -> E_assert (E_aux (E_lit (mk_lit L_true), annot), str)); *)
      lEXP_cast = (fun (typ, lexp) -> LEXP_cast (simple_typ typ, lexp));
      pat_alg = simple_pat
    } in
  let simple_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp simple_exp);
                                          rewrite_pat = (fun _ -> fold_pat simple_pat) }
  in
  let defs = Defs (List.map simple_def defs) in
  rewrite_defs_base simple_defs defs

let rewrite_tuple_vector_assignments defs =
  let assign_tuple e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (LEXP_aux (LEXP_tup lexps, lannot), exp) ->
       let typ = Env.base_typ_of env (typ_of exp) in
       if is_vector_typ typ then
         (* let _ = Pretty_print_common.print stderr (Pretty_print_sail.doc_exp (E_aux (e_aux, annot))) in *)
         let (start, _, ord, etyp) = vector_typ_args_of typ in
         let len (LEXP_aux (le, lannot)) =
           let ltyp = Env.base_typ_of env (typ_of_annot lannot) in
           if is_vector_typ ltyp then
             let (_, len, _, _) = vector_typ_args_of ltyp in
             match nexp_simp len with
             | Nexp_aux (Nexp_constant len, _) -> len
             | _ -> (Big_int.of_int 1)
           else (Big_int.of_int 1) in
         let next i step =
           if is_order_inc ord
           then (Big_int.sub (Big_int.add i step) (Big_int.of_int 1), Big_int.add i step)
           else (Big_int.add (Big_int.sub i step) (Big_int.of_int 1), Big_int.sub i step) in
         let i = match nexp_simp start with
         | (Nexp_aux (Nexp_constant i, _)) -> i
         | _ -> if is_order_inc ord then Big_int.zero else Big_int.of_int (List.length lexps - 1) in
         let l = gen_loc (fst annot) in
         let exp' =
           if small exp then strip_exp exp
           else mk_exp (E_id (mk_id "split_vec")) in
         let lexp_to_exp (i, exps) lexp =
           let (j, i') = next i (len lexp) in
           let i_exp = mk_exp (E_lit (mk_lit (L_num i))) in
           let j_exp = mk_exp (E_lit (mk_lit (L_num j))) in
           let sub = mk_exp (E_vector_subrange (exp', i_exp, j_exp)) in
           (i', exps @ [sub]) in
         let (_, exps) = List.fold_left lexp_to_exp (i, []) lexps in
         let tup = mk_exp (E_tuple exps) in
         let lexp = LEXP_aux (LEXP_tup (List.map strip_lexp lexps), (l, ())) in
         let e_aux =
           if small exp then mk_exp (E_assign (lexp, tup))
           else mk_exp (
             E_let (
               mk_letbind (mk_pat (P_id (mk_id "split_vec"))) (strip_exp exp),
               mk_exp (E_assign (lexp, tup)))) in
         begin
           try check_exp env e_aux unit_typ with
           | Type_error (l, err) ->
             raise (Reporting_basic.err_typ l (string_of_type_error err))
         end
       else E_aux (e_aux, annot)
    | _ -> E_aux (e_aux, annot)
  in
  let assign_exp = {
      id_exp_alg with
      e_aux = (fun (e_aux, annot) -> assign_tuple e_aux annot)
    } in
  let assign_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp assign_exp) } in
  rewrite_defs_base assign_defs defs

let rewrite_tuple_assignments defs =
  let assign_tuple e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (LEXP_aux (LEXP_tup lexps, _), exp) ->
       (* let _ = Pretty_print_common.print stderr (Pretty_print_sail.doc_exp (E_aux (e_aux, annot))) in *)
       let (_, ids) = List.fold_left (fun (n, ids) _ -> (n + 1, ids @ [mk_id ("tup__" ^ string_of_int n)])) (0, []) lexps in
       let block_assign i lexp = mk_exp (E_assign (strip_lexp lexp, mk_exp (E_id (mk_id ("tup__" ^ string_of_int i))))) in
       let block = mk_exp (E_block (List.mapi block_assign lexps)) in
       let letbind = mk_letbind (mk_pat (P_tup (List.map (fun id -> mk_pat (P_id id)) ids))) (strip_exp exp) in
       let let_exp = mk_exp (E_let (letbind, block)) in
       begin
         try check_exp env let_exp unit_typ with
         | Type_error (l, err) ->
           raise (Reporting_basic.err_typ l (string_of_type_error err))
       end
    | _ -> E_aux (e_aux, annot)
  in
  let assign_exp = {
      id_exp_alg with
      e_aux = (fun (e_aux, annot) -> assign_tuple e_aux annot)
    } in
  let assign_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp assign_exp) } in
  rewrite_defs_base assign_defs defs

let rewrite_simple_assignments defs =
  let assign_e_aux e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (lexp, exp) ->
       let (lexp, rhs) = rewrite_lexp_to_rhs lexp in
       let assign = mk_exp (E_assign (strip_lexp lexp, strip_exp (rhs exp))) in
       check_exp env assign unit_typ
    | _ -> E_aux (e_aux, annot)
  in
  let assign_exp = {
      id_exp_alg with
      e_aux = (fun (e_aux, annot) -> assign_e_aux e_aux annot)
    } in
  let assign_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp assign_exp) } in
  rewrite_defs_base assign_defs defs

let rewrite_defs_remove_blocks =
  let letbind_wild v body =
    let l = get_loc_exp v in
    let env = env_of v in
    let typ = typ_of v in
    let wild = add_p_typ typ (annot_pat P_wild l env typ) in
    let e_aux = E_let (annot_letbind (unaux_pat wild, v) l env typ, body) in
    propagate_exp_effect (annot_exp e_aux l env (typ_of body)) in

  let rec f l = function
    | [] -> E_aux (E_lit (L_aux (L_unit,gen_loc l)), (simple_annot l unit_typ))
    | [e] -> e  (* check with Kathy if that annotation is fine *)
    | e :: es -> letbind_wild e (f l es) in

  let e_aux = function
    | (E_block es,(l,_)) -> f l es
    | (e,annot) -> E_aux (e,annot) in
    
  let alg = { id_exp_alg with e_aux = e_aux } in

  rewrite_defs_base
    {rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let letbind (v : 'a exp) (body : 'a exp -> 'a exp) : 'a exp =
  (* body is a function : E_id variable -> actual body *)
  let (E_aux (_,(l,annot))) = v in
  match annot with
  | Some (env, Typ_aux (Typ_id tid, _), eff) when string_of_id tid = "unit" ->
     let body = body (annot_exp (E_lit (mk_lit L_unit)) l env unit_typ) in
     let body_typ = try typ_of body with _ -> unit_typ in
     let wild = add_p_typ (typ_of v) (annot_pat P_wild l env (typ_of v)) in
     let lb = annot_letbind (unaux_pat wild, v) l env unit_typ in
     propagate_exp_effect (annot_exp (E_let (lb, body)) l env body_typ)
  | Some (env, typ, eff) ->
     let id = fresh_id "w__" l in
     let pat = add_p_typ (typ_of v) (annot_pat (P_id id) l env (typ_of v)) in
     let lb = annot_letbind (unaux_pat pat, v) l env typ in
     let body = body (annot_exp (E_id id) l env typ) in
     propagate_exp_effect (annot_exp (E_let (lb, body)) l env (typ_of body))
  | None ->
     raise (Reporting_basic.err_unreachable l "no type information")


let rec mapCont (f : 'b -> ('b -> 'a exp) -> 'a exp) (l : 'b list) (k : 'b list -> 'a exp) : 'a exp = 
  match l with
  | [] -> k []
  | exp :: exps -> f exp (fun exp -> mapCont f exps (fun exps -> k (exp :: exps)))

let rewrite_defs_letbind_effects =

  let rec value ((E_aux (exp_aux,_)) as exp) =
    not (effectful exp || updates_vars exp)
  and value_optdefault (Def_val_aux (o,_)) = match o with
    | Def_val_empty -> true
    | Def_val_dec e -> value e
  and value_fexps (FES_aux (FES_Fexps (fexps,_),_)) =
    List.fold_left (fun b (FE_aux (FE_Fexp (_,e),_)) -> b && value e) true fexps in


  let rec n_exp_name (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else letbind exp k)

  and n_exp_pure (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else letbind exp k)

  and n_exp_nameL (exps : 'a exp list) (k : 'a exp list -> 'a exp) : 'a exp =
    mapCont n_exp_name exps k

  and n_fexp (fexp : 'a fexp) (k : 'a fexp -> 'a exp) : 'a exp =
    let (FE_aux (FE_Fexp (id,exp),annot)) = fexp in
    n_exp_name exp (fun exp ->
    k (fix_eff_fexp (FE_aux (FE_Fexp (id,exp),annot))))

  and n_fexpL (fexps : 'a fexp list) (k : 'a fexp list -> 'a exp) : 'a exp =
    mapCont n_fexp fexps k

  and n_pexp : 'b. bool -> 'a pexp -> ('a pexp -> 'b) -> 'b = fun newreturn pexp k ->
    match pexp with
    | Pat_aux (Pat_exp (pat,exp),annot) ->
      k (fix_eff_pexp (Pat_aux (Pat_exp (pat,n_exp_term newreturn exp), annot)))
    | Pat_aux (Pat_when (pat,guard,exp),annot) ->
      k (fix_eff_pexp (Pat_aux (Pat_when (pat,n_exp_term newreturn guard,n_exp_term newreturn exp), annot)))

  and n_pexpL (newreturn : bool) (pexps : 'a pexp list) (k : 'a pexp list -> 'a exp) : 'a exp =
    mapCont (n_pexp newreturn) pexps k

  and n_fexps (fexps : 'a fexps) (k : 'a fexps -> 'a exp) : 'a exp = 
    let (FES_aux (FES_Fexps (fexps_aux,b),annot)) = fexps in
    n_fexpL fexps_aux (fun fexps_aux -> 
    k (fix_eff_fexps (FES_aux (FES_Fexps (fexps_aux,b),annot))))

  and n_opt_default (opt_default : 'a opt_default) (k : 'a opt_default -> 'a exp) : 'a exp = 
    let (Def_val_aux (opt_default,annot)) = opt_default in
    match opt_default with
    | Def_val_empty -> k (Def_val_aux (Def_val_empty,annot))
    | Def_val_dec exp ->
       n_exp_name exp (fun exp -> 
       k (fix_eff_opt_default (Def_val_aux (Def_val_dec exp,annot))))

  and n_lb (lb : 'a letbind) (k : 'a letbind -> 'a exp) : 'a exp =
    let (LB_aux (lb,annot)) = lb in
    match lb with
    | LB_val (pat,exp1) ->
       n_exp exp1 (fun exp1 -> 
       k (fix_eff_lb (LB_aux (LB_val (pat,exp1),annot))))

  and n_lexp (lexp : 'a lexp) (k : 'a lexp -> 'a exp) : 'a exp =
    let (LEXP_aux (lexp_aux,annot)) = lexp in
    match lexp_aux with
    | LEXP_id _ -> k lexp
    | LEXP_deref exp ->
       n_exp exp (fun exp ->
       k (fix_eff_lexp (LEXP_aux (LEXP_deref exp, annot))))
    | LEXP_memory (id,es) ->
       n_exp_nameL es (fun es -> 
       k (fix_eff_lexp (LEXP_aux (LEXP_memory (id,es),annot))))
    | LEXP_tup es ->
       n_lexpL es (fun es ->
       k (fix_eff_lexp (LEXP_aux (LEXP_tup es,annot))))
    | LEXP_cast (typ,id) -> 
       k (fix_eff_lexp (LEXP_aux (LEXP_cast (typ,id),annot)))
    | LEXP_vector (lexp,e) ->
       n_lexp lexp (fun lexp -> 
       n_exp_name e (fun e -> 
       k (fix_eff_lexp (LEXP_aux (LEXP_vector (lexp,e),annot)))))
    | LEXP_vector_range (lexp,e1,e2) ->
       n_lexp lexp (fun lexp ->
       n_exp_name e1 (fun e1 ->
    n_exp_name e2 (fun e2 ->
       k (fix_eff_lexp (LEXP_aux (LEXP_vector_range (lexp,e1,e2),annot))))))
    | LEXP_field (lexp,id) ->
       n_lexp lexp (fun lexp ->
       k (fix_eff_lexp (LEXP_aux (LEXP_field (lexp,id),annot))))

  and n_lexpL (lexps : 'a lexp list) (k : 'a lexp list -> 'a exp) : 'a exp =
    mapCont n_lexp lexps k

  and n_exp_term (newreturn : bool) (exp : 'a exp) : 'a exp =
    let (E_aux (_,(l,tannot))) = exp in
    let exp =
      if newreturn then
        (* let typ = try typ_of exp with _ -> unit_typ in *)
        let exp = annot_exp (E_cast (typ_of exp, exp)) l (env_of exp) (typ_of exp) in
        annot_exp (E_internal_return exp) l (env_of exp) (typ_of exp)
      else
        exp in
    (* n_exp_term forces an expression to be translated into a form 
       "let .. let .. let .. in EXP" where EXP has no effect and does not update
       variables *)
    n_exp_pure exp (fun exp -> exp)

  and n_exp (E_aux (exp_aux,annot) as exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp = 

    let rewrap e = fix_eff_exp (E_aux (e,annot)) in

    match exp_aux with
    | E_block es -> failwith "E_block should have been removed till now"
    | E_nondet _ -> failwith "E_nondet not supported"
    | E_id id -> k exp
    | E_ref id -> k exp
    | E_lit _ -> k exp
    | E_cast (typ,exp') ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_cast (typ,exp'))))
    | E_app (id,exps) ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_app (id,exps))))
    | E_app_infix (exp1,id,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_app_infix (exp1,id,exp2)))))
    | E_tuple exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_tuple exps)))
    | E_if (exp1,exp2,exp3) ->
       let e_if exp1 =
         let (E_aux (_,annot2)) = exp2 in
         let (E_aux (_,annot3)) = exp3 in
         let newreturn = effectful exp2 || effectful exp3 in
         let exp2 = n_exp_term newreturn exp2 in
         let exp3 = n_exp_term newreturn exp3 in
         k (rewrap (E_if (exp1,exp2,exp3))) in
       if value exp1 then e_if (n_exp_term false exp1) else n_exp_name exp1 e_if
    | E_for (id,start,stop,by,dir,body) ->
       n_exp_name start (fun start ->
       n_exp_name stop (fun stop ->
       n_exp_name by (fun by ->
       let body = n_exp_term (effectful body) body in
       k (rewrap (E_for (id,start,stop,by,dir,body))))))
    | E_loop (loop, cond, body) ->
       let cond = n_exp_term (effectful cond) cond in
       let body = n_exp_term (effectful body) body in
       k (rewrap (E_loop (loop,cond,body)))
    | E_vector exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_vector exps)))
    | E_vector_access (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_vector_access (exp1,exp2)))))
    | E_vector_subrange (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       n_exp_name exp3 (fun exp3 ->
       k (rewrap (E_vector_subrange (exp1,exp2,exp3))))))
    | E_vector_update (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       n_exp_name exp3 (fun exp3 ->
       k (rewrap (E_vector_update (exp1,exp2,exp3))))))
    | E_vector_update_subrange (exp1,exp2,exp3,exp4) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       n_exp_name exp3 (fun exp3 ->
       n_exp_name exp4 (fun exp4 ->
       k (rewrap (E_vector_update_subrange (exp1,exp2,exp3,exp4)))))))
    | E_vector_append (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_vector_append (exp1,exp2)))))
    | E_list exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_list exps)))
    | E_cons (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_cons (exp1,exp2)))))
    | E_record fexps ->
       n_fexps fexps (fun fexps ->
       k (rewrap (E_record fexps)))
    | E_record_update (exp1,fexps) ->
       n_exp_name exp1 (fun exp1 ->
       n_fexps fexps (fun fexps ->
       k (rewrap (E_record_update (exp1,fexps)))))
    | E_field (exp1,id) ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_field (exp1,id))))
    | E_case (exp1,pexps) ->
       let newreturn = List.exists effectful_pexp pexps in
       n_exp_name exp1 (fun exp1 ->
       n_pexpL newreturn pexps (fun pexps ->
       k (rewrap (E_case (exp1,pexps)))))
    | E_try (exp1,pexps) ->
       let newreturn = effectful exp1 || List.exists effectful_pexp pexps in
       n_exp_name exp1 (fun exp1 ->
       n_pexpL newreturn pexps (fun pexps ->
       k (rewrap (E_try (exp1,pexps)))))
    | E_let (lb,body) ->
       n_lb lb (fun lb ->
       rewrap (E_let (lb,n_exp body k)))
    | E_sizeof nexp ->
       k (rewrap (E_sizeof nexp))
    | E_constraint nc ->
       k (rewrap (E_constraint nc))
    | E_sizeof_internal annot ->
       k (rewrap (E_sizeof_internal annot))
    | E_assign (lexp,exp1) ->
       n_lexp lexp (fun lexp ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_assign (lexp,exp1)))))
    | E_exit exp' -> k (E_aux (E_exit (n_exp_term (effectful exp') exp'),annot))
    | E_assert (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_assert (exp1,exp2)))))
    | E_internal_cast (annot',exp') ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_internal_cast (annot',exp'))))
    | E_internal_exp _ -> k exp
    | E_internal_exp_user _ -> k exp
    | E_var (lexp,exp1,exp2) ->
       n_lexp lexp (fun lexp ->
       n_exp exp1 (fun exp1 ->
       rewrap (E_var (lexp,exp1,n_exp exp2 k))))
    | E_internal_return exp1 ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_internal_return exp1)))
    | E_internal_value v ->
       k (rewrap (E_internal_value v))
    | E_comment str ->
       k (rewrap (E_comment str))
    | E_comment_struc exp' ->
       n_exp exp' (fun exp' ->
       k (rewrap (E_comment_struc exp')))
    | E_return exp' ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_return exp')))
    | E_throw exp' ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_throw exp')))
    | E_internal_plet _ -> failwith "E_internal_plet should not be here yet" in

  let rewrite_fun _ (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),fdannot)) = 
    let effectful_funcl (FCL_aux (FCL_Funcl(_, pexp), _)) = effectful_pexp pexp in
    let newreturn = List.exists effectful_funcl funcls in
    let rewrite_funcl (FCL_aux (FCL_Funcl(id,pexp),annot)) =
      let _ = reset_fresh_name_counter () in
      FCL_aux (FCL_Funcl (id,n_pexp newreturn pexp (fun x -> x)),annot)
    in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),fdannot) in
  let rewrite_def rewriters def =
    (* let _ = Pretty_print_sail.pp_defs stderr (Defs [def]) in *)
    match def with
    | DEF_val (LB_aux (lb, annot)) ->
      let rewrap lb = DEF_val (LB_aux (lb, annot)) in
      begin
        match lb with
        | LB_val (pat, exp) ->
          rewrap (LB_val (pat, n_exp_term (effectful exp) exp))
      end
    | DEF_fundef fdef -> DEF_fundef (rewrite_fun rewriters fdef)
    | DEF_internal_mutrec fdefs ->
      DEF_internal_mutrec (List.map (rewrite_fun rewriters) fdefs)
    | d -> d in
  rewrite_defs_base
    {rewrite_exp = rewrite_exp
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }

let rewrite_defs_internal_lets =

  let rec pat_of_local_lexp (LEXP_aux (lexp, ((l, _) as annot))) = match lexp with
    | LEXP_id id -> P_aux (P_id id, annot)
    | LEXP_cast (typ, id) -> add_p_typ typ (P_aux (P_id id, annot))
    | LEXP_tup lexps -> P_aux (P_tup (List.map pat_of_local_lexp lexps), annot)
    | _ -> raise (Reporting_basic.err_unreachable l "unexpected local lexp") in

  let e_let (lb,body) =
    match lb with
    | LB_aux (LB_val (P_aux ((P_wild | P_typ (_, P_aux (P_wild, _))), _),
      E_aux (E_assign ((LEXP_aux (_, annot) as le), exp), (l, _))), _)
      when lexp_is_local le (env_of_annot annot) && not (lexp_is_effectful le) ->
       (* Rewrite assignments to local variables into let bindings *)
       let (lhs, rhs) = rewrite_lexp_to_rhs le in
       let (LEXP_aux (_, lannot)) = lhs in
       let ltyp = typ_of_annot lannot in
       let rhs = annot_exp (E_cast (ltyp, rhs exp)) l (env_of_annot lannot) ltyp in
       E_let (LB_aux (LB_val (pat_of_local_lexp lhs, rhs), annot), body)
    | LB_aux (LB_val (pat,exp'),annot') ->
       if effectful exp'
       then E_internal_plet (pat,exp',body)
       else E_let (lb,body) in

  let e_internal_let = fun (lexp,exp1,exp2) ->
    let paux, annot = match lexp with
    | LEXP_aux (LEXP_id id, annot) ->
       (P_id id, annot)
    | LEXP_aux (LEXP_cast (typ, id), annot) ->
       (unaux_pat (add_p_typ typ (P_aux (P_id id, annot))), annot)
    | _ -> failwith "E_var with unexpected lexp" in
    if effectful exp1 then
      E_internal_plet (P_aux (paux, annot), exp1, exp2)
    else
      E_let (LB_aux (LB_val (P_aux (paux, annot), exp1), annot), exp2) in

  let alg = { id_exp_alg with e_let = e_let; e_internal_let = e_internal_let } in
  rewrite_defs_base
    { rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }

let rewrite_defs_pat_lits =
  let rewrite_pexp (Pat_aux (pexp_aux, annot) as pexp) =
    let guards = ref [] in
    let counter = ref 0 in

    let rewrite_pat = function
      | P_lit lit, p_annot ->
         let env = env_of_annot p_annot in
         let typ = typ_of_annot p_annot in
         let id = mk_id ("p" ^ string_of_int !counter ^ "#") in
         let guard = mk_exp (E_app_infix (mk_exp (E_id id), mk_id "==", mk_exp (E_lit lit))) in
         let guard = check_exp (Env.add_local id (Immutable, typ) env) guard bool_typ in
         guards := guard :: !guards;
         incr counter;
         P_aux (P_id id, p_annot)
      | p_aux, p_annot -> P_aux (p_aux, p_annot)
    in

    match pexp_aux with
    | Pat_exp (pat, exp) ->
       begin
         let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat } pat in
         match !guards with
         | [] -> pexp
         | (g :: gs) ->
            let guard_annot = (fst annot, Some (env_of exp, bool_typ, no_effect)) in
            Pat_aux (Pat_when (pat, List.fold_left (fun g g' -> E_aux (E_app (mk_id "and_bool", [g; g']), guard_annot)) g gs, exp), annot)
       end
    | Pat_when (pat, guard, exp) ->
       begin
         let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat } pat in
         let guard_annot = (fst annot, Some (env_of exp, bool_typ, no_effect)) in
         Pat_aux (Pat_when (pat, List.fold_left (fun g g' -> E_aux (E_app (mk_id "and_bool", [g; g']), guard_annot)) guard !guards, exp), annot)
       end
  in

  let alg = { id_exp_alg with pat_aux = (fun (pexp_aux, annot) -> rewrite_pexp (Pat_aux (pexp_aux, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) }


(* Now all expressions have no blocks anymore, any term is a sequence of let-expressions,
 * internal let-expressions, or internal plet-expressions ended by a term that does not
 * access memory or registers and does not update variables *)

let swaptyp typ (l,tannot) = match tannot with
  | Some (env, typ', eff) -> (l, Some (env, typ, eff))
  | _ -> raise (Reporting_basic.err_unreachable l "swaptyp called with empty type annotation")

type 'a updated_term =
  | Added_vars of 'a exp * 'a pat
  | Same_vars of 'a exp

let rec rewrite_var_updates ((E_aux (expaux,((l,_) as annot))) as exp) =

  let env = env_of exp in

  let tuple_exp = function
    | [] -> annot_exp (E_lit (mk_lit L_unit)) l env unit_typ
    | [e] -> e
    | es -> annot_exp (E_tuple es) l env (tuple_typ (List.map typ_of es)) in

  let tuple_pat = function
    | [] -> annot_pat P_wild l env unit_typ
    | [pat] ->
       let typ = pat_typ_of pat in
       add_p_typ typ pat
    | pats ->
       let typ = tuple_typ (List.map pat_typ_of pats) in
       add_p_typ typ (annot_pat (P_tup pats) l env typ) in

  let rec add_vars overwrite ((E_aux (expaux,annot)) as exp) vars =
    match expaux with
    | E_let (lb,exp) ->
       let exp = add_vars overwrite exp vars in
       E_aux (E_let (lb,exp),swaptyp (typ_of exp) annot)
    | E_var (lexp,exp1,exp2) ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_var (lexp,exp1,exp2), swaptyp (typ_of exp2) annot)
    | E_internal_plet (pat,exp1,exp2) ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_plet (pat,exp1,exp2), swaptyp (typ_of exp2) annot)
    | E_internal_return exp2 ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_return exp2,swaptyp (typ_of exp2) annot)
    | _ ->
       (* after rewrite_defs_letbind_effects there cannot be terms that have
          effects/update local variables in "tail-position": check n_exp_term
          and where it is used. *)
       if overwrite then
         match typ_of exp with
         | Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> tuple_exp vars
         | _ -> raise (Reporting_basic.err_unreachable l
             "add_vars: trying to overwrite a non-unit expression in tail-position")
       else tuple_exp (exp :: vars) in

  let mk_var_exps_pats l env ids =
    ids
    |> IdSet.elements
    |> List.map
        (fun id ->
          let (E_aux (_, a) as exp) = infer_exp env (E_aux (E_id id, (l, ()))) in
          exp, P_aux (P_id id, a))
    |> List.split in

  let rewrite (E_aux (expaux,((el,_) as annot)) as full_exp) (P_aux (_,(pl,pannot)) as pat) =
    let env = env_of_annot annot in
    let overwrite = match typ_of full_exp with
      | Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true
      | _ -> false in
    match expaux with
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
       (* Translate for loops into calls to one of the foreach combinators.
          The loop body becomes a function of the loop variable and any
          mutable local variables that are updated inside the loop.
          Since the foreach* combinators are higher-order functions,
          they cannot be represented faithfully in the AST. The following
          code abuses the parameters of an E_app node, embedding the loop body
          function as an expression followed by the list of variables it
          expects. In (Lem) pretty-printing, this turned into an anonymous
          function and passed to foreach*. *)
       let vars, varpats = mk_var_exps_pats pl env (find_updated_vars exp4) in
       let exp4 = rewrite_var_updates (add_vars overwrite exp4 vars) in
       let ord_exp, lower, upper = match destruct_range (typ_of exp1), destruct_range (typ_of exp2) with
         | None, _ | _, None ->
            raise (Reporting_basic.err_unreachable el "Could not determine loop bounds")
         | Some (l1, u1), Some (l2, u2) ->
            if is_order_inc order
            then (annot_exp (E_lit (mk_lit L_true)) el env bool_typ, l1, u2)
            else (annot_exp (E_lit (mk_lit L_false)) el env bool_typ, l2, u1) in
       let lvar_kid = mk_kid ("loop_" ^ string_of_id id) in
       let lvar_nc = nc_and (nc_lteq lower (nvar lvar_kid)) (nc_lteq (nvar lvar_kid) upper) in
       let lvar_typ = mk_typ (Typ_exist ([lvar_kid], lvar_nc, atom_typ (nvar lvar_kid))) in
       let lvar_pat = unaux_pat (add_p_typ lvar_typ (annot_pat (P_var (
         annot_pat (P_id id) el env (atom_typ (nvar lvar_kid)),
         TP_aux (TP_var lvar_kid, gen_loc el))) el env lvar_typ)) in
       let lb = annot_letbind (lvar_pat, exp1) el env lvar_typ in
       let body = annot_exp (E_let (lb, exp4)) el env (typ_of exp4) in
       let v = annot_exp (E_app (mk_id "foreach", [exp1; exp2; exp3; ord_exp; tuple_exp vars; body])) el env (typ_of body) in
       Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
     | E_loop(loop,cond,body) ->
        let vars, varpats = mk_var_exps_pats pl env (find_updated_vars body) in
        let body = rewrite_var_updates (add_vars overwrite body vars) in
        let (E_aux (_,(_,bannot))) = body in
        let fname = match loop with
          | While -> "while"
          | Until -> "until" in
        let funcl = Id_aux (Id fname,gen_loc el) in
        let v = E_aux (E_app (funcl,[cond;tuple_exp vars;body]), (gen_loc el, bannot)) in
        Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_if (c,e1,e2) ->
       let vars, varpats =
         IdSet.union (find_updated_vars e1) (find_updated_vars e2)
         |> mk_var_exps_pats pl env in
       if vars = [] then
         (Same_vars (E_aux (E_if (c,rewrite_var_updates e1,rewrite_var_updates e2),annot)))
       else
         let e1 = rewrite_var_updates (add_vars overwrite e1 vars) in
         let e2 = rewrite_var_updates (add_vars overwrite e2 vars) in
         (* after rewrite_defs_letbind_effects c has no variable updates *)
         let env = env_of_annot annot in
         let typ = typ_of e1 in
         let eff = union_eff_exps [e1;e2] in
         let v = E_aux (E_if (c,e1,e2), (gen_loc el, Some (env, typ, eff))) in
         Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_case (e1,ps) ->
       (* after rewrite_defs_letbind_effects e1 needs no rewriting *)
       let vars, varpats =
         ps
         |> List.map (fun (Pat_aux ((Pat_exp (_,e)|Pat_when (_,_,e)),_)) -> e)
         |> List.map find_updated_vars
         |> List.fold_left IdSet.union IdSet.empty
         |> mk_var_exps_pats pl env in
       if vars = [] then
         let ps = List.map (function
           | Pat_aux (Pat_exp (p,e),a) ->
             Pat_aux (Pat_exp (p,rewrite_var_updates e),a)
           | Pat_aux (Pat_when (p,g,e),a) ->
             Pat_aux (Pat_when (p,g,rewrite_var_updates e),a)) ps in
         Same_vars (E_aux (E_case (e1,ps),annot))
       else
         let rewrite_pexp (Pat_aux (pexp, (l, _))) = match pexp with
           | Pat_exp (pat, exp) ->
             let exp = rewrite_var_updates (add_vars overwrite exp vars) in
             let pannot = (l, Some (env_of exp, typ_of exp, effect_of exp)) in
             Pat_aux (Pat_exp (pat, exp), pannot)
           | Pat_when _ ->
             raise (Reporting_basic.err_unreachable l
               "Guarded patterns should have been rewritten already") in
         let typ = match ps with
           | Pat_aux ((Pat_exp (_,first)|Pat_when (_,_,first)),_) :: _ -> typ_of first
           | _ -> unit_typ in
         let v = propagate_exp_effect (annot_exp (E_case (e1, List.map rewrite_pexp ps)) pl env typ) in
         Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_assign (lexp,vexp) ->
       let mk_id_pat id = match Env.lookup_id id env with
         | Local (_, typ) ->
            add_p_typ typ (annot_pat (P_id id) pl env typ)
         | _ ->
            raise (Reporting_basic.err_unreachable pl
              ("Failed to look up type of variable " ^ string_of_id id)) in
       if effectful exp then
         Same_vars (E_aux (E_assign (lexp,vexp),annot))
       else 
         (match lexp with
          | LEXP_aux (LEXP_id id,annot) ->
             let pat = annot_pat (P_id id) pl env (typ_of vexp) in
             Added_vars (vexp, mk_id_pat id)
          | LEXP_aux (LEXP_cast (typ,id),annot) ->
             let pat = add_p_typ typ (annot_pat (P_id id) pl env (typ_of vexp)) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_vector (LEXP_aux (LEXP_id id,((l2,_) as annot2)),i),((l1,_) as annot)) ->
             let eid = annot_exp (E_id id) l2 env (typ_of_annot annot2) in
             let vexp = annot_exp (E_vector_update (eid,i,vexp)) l1 env (typ_of_annot annot) in
             let pat = annot_pat (P_id id) pl env (typ_of vexp) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_vector_range (LEXP_aux (LEXP_id id,((l2,_) as annot2)),i,j),
                      ((l,_) as annot)) -> 
             let eid = annot_exp (E_id id) l2 env (typ_of_annot annot2) in
             let vexp = annot_exp (E_vector_update_subrange (eid,i,j,vexp)) l env (typ_of_annot annot) in
             let pat = annot_pat (P_id id) pl env (typ_of vexp) in
             Added_vars (vexp,pat)
          | _ -> Same_vars (E_aux (E_assign (lexp,vexp),annot)))
    | _ ->
       (* after rewrite_defs_letbind_effects this expression is pure and updates
       no variables: check n_exp_term and where it's used. *)
       Same_vars (E_aux (expaux,annot))  in

  match expaux with
  | E_let (lb,body) ->
     let body = rewrite_var_updates body in
     let (LB_aux (LB_val (pat, v), lbannot)) = lb in
     let lb = match rewrite v pat with
       | Added_vars (v, P_aux (pat, _)) ->
          annot_letbind (pat, v) (get_loc_exp v) env (typ_of v)
       | Same_vars v -> LB_aux (LB_val (pat, v),lbannot) in
     propagate_exp_effect (annot_exp (E_let (lb, body)) l env (typ_of body))
  | E_var (lexp,v,body) ->
     (* Rewrite E_var into E_let and call recursively *)
     let paux, typ = match lexp with
       | LEXP_aux (LEXP_id id, _) ->
          P_id id, typ_of v
       | LEXP_aux (LEXP_cast (typ, id), _) ->
          unaux_pat (add_p_typ typ (annot_pat (P_id id) l env (typ_of v))), typ
       | _ ->
         raise (Reporting_basic.err_unreachable l
           "E_var with a lexp that is not a variable") in
     let lb = annot_letbind (paux, v) l env typ in
     let exp = propagate_exp_effect (annot_exp (E_let (lb, body)) l env (typ_of body)) in
     rewrite_var_updates exp
  | E_internal_plet (pat,v,body) ->
     failwith "rewrite_var_updates: E_internal_plet shouldn't be introduced yet"
  (* There are no expressions that have effects or variable updates in
     "tail-position": check the definition nexp_term and where it is used. *)
  | _ -> exp

let replace_memwrite_e_assign exp =
  let e_aux = fun (expaux,annot) ->
    match expaux with
    | E_assign (LEXP_aux (LEXP_memory (id,args),_),v) -> E_aux (E_app (id,args @ [v]),annot)
    | _ -> E_aux (expaux,annot) in
  fold_exp { id_exp_alg with e_aux = e_aux } exp



let remove_reference_types exp =

  let rec rewrite_t (Typ_aux (t_aux,a)) = (Typ_aux (rewrite_t_aux t_aux,a))
  and rewrite_t_aux t_aux = match t_aux with
    | Typ_app (Id_aux (Id "reg",_), [Typ_arg_aux (Typ_arg_typ (Typ_aux (t_aux2, _)), _)]) ->
      rewrite_t_aux t_aux2
    | Typ_app (name,t_args) -> Typ_app (name,List.map rewrite_t_arg t_args)
    | Typ_fn (t1,t2,eff) -> Typ_fn (rewrite_t t1,rewrite_t t2,eff)
    | Typ_tup ts -> Typ_tup (List.map rewrite_t ts)
    | _ -> t_aux
  and rewrite_t_arg t_arg = match t_arg with
    | Typ_arg_aux (Typ_arg_typ t, a) -> Typ_arg_aux (Typ_arg_typ (rewrite_t t), a)
    | _ -> t_arg in

  let rec rewrite_annot = function
    | (l, None) -> (l, None)
    | (l, Some (env, typ, eff)) -> (l, Some (env, rewrite_t typ, eff)) in

  map_exp_annot rewrite_annot exp



let rewrite_defs_remove_superfluous_letbinds =

  let e_aux (exp,annot) = match exp with
    | E_let (lb,exp2) ->
       begin match lb,exp2 with
       (* 'let x = EXP1 in x' can be replaced with 'EXP1' *)
       | LB_aux (LB_val (P_aux (P_id id, _), exp1), _),
         E_aux (E_id id', _)
       | LB_aux (LB_val (P_aux (P_id id, _), exp1), _),
         E_aux (E_cast (_,E_aux (E_id id', _)), _)
         when Id.compare id id' == 0 && id_is_unbound id (env_of_annot annot) ->
          exp1
       (* "let x = EXP1 in return x" can be replaced with 'return (EXP1)', at
          least when EXP1 is 'small' enough *)
       | LB_aux (LB_val (P_aux (P_id id, _), exp1), _),
         E_aux (E_internal_return (E_aux (E_id id', _)), _)
         when Id.compare id id' == 0 && small exp1 && id_is_unbound id (env_of_annot annot) ->
          let (E_aux (_,e1annot)) = exp1 in
          E_aux (E_internal_return (exp1),e1annot)
       | _ -> E_aux (exp,annot) 
       end
    | _ -> E_aux (exp,annot) in

  let alg = { id_exp_alg with e_aux = e_aux } in
  rewrite_defs_base
    { rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }
  

let rewrite_defs_remove_superfluous_returns =

  let has_unittype e = match typ_of e with
    | Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true
    | _ -> false in

  let untyp_pat = function
    | P_aux (P_typ (typ, pat), _) -> pat, Some typ
    | pat -> pat, None in

  let uncast_internal_return = function
    | E_aux (E_internal_return (E_aux (E_cast (typ, exp), _)), a) ->
       E_aux (E_internal_return exp, a), Some typ
    | exp -> exp, None in

  let e_aux (exp,annot) = match exp with
    | E_let (LB_aux (LB_val (pat, exp1), _), exp2)
    | E_internal_plet (pat, exp1, exp2)
      when effectful exp1 ->
       begin match untyp_pat pat, uncast_internal_return exp2 with
       | (P_aux (P_lit (L_aux (lit,_)),_), ptyp),
         (E_aux (E_internal_return (E_aux (E_lit (L_aux (lit',_)),_)), a), etyp)
         when lit = lit' ->
          begin
            match ptyp, etyp with
            | Some typ, _ | _, Some typ -> E_aux (E_cast (typ, exp1), a)
            | None, None -> exp1
          end
       | (P_aux (P_wild,pannot), ptyp),
         (E_aux (E_internal_return (E_aux (E_lit (L_aux (L_unit,_)),_)), a), etyp)
         when has_unittype exp1 ->
          begin
            match ptyp, etyp with
            | Some typ, _ | _, Some typ -> E_aux (E_cast (typ, exp1), a)
            | None, None -> exp1
          end
       | (P_aux (P_id id,_), ptyp),
         (E_aux (E_internal_return (E_aux (E_id id',_)), a), etyp)
         when Id.compare id id' == 0 && id_is_unbound id (env_of_annot annot) ->
          begin
            match ptyp, etyp with
            | Some typ, _ | _, Some typ -> E_aux (E_cast (typ, exp1), a)
            | None, None -> exp1
          end
       | _ -> E_aux (exp,annot)
       end
    | _ -> E_aux (exp,annot) in

  let alg = { id_exp_alg with e_aux = e_aux } in
  rewrite_defs_base
    { rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let rewrite_defs_remove_e_assign (Defs defs) =
  let (Defs loop_specs) = fst (check Env.empty (Defs (List.map gen_vs
    [("foreach", "forall ('vars : Type). (int, int, int, bool, 'vars, 'vars) -> 'vars");
     ("while", "forall ('vars : Type). (bool, 'vars, 'vars) -> 'vars");
     ("until", "forall ('vars : Type). (bool, 'vars, 'vars) -> 'vars")]))) in
  let rewrite_exp _ e =
    replace_memwrite_e_assign (remove_reference_types (rewrite_var_updates e)) in
  rewrite_defs_base
    { rewrite_exp = rewrite_exp
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    } (Defs (loop_specs @ defs))

let recheck_defs defs = fst (check initial_env defs)

let rewrite_defs_lem = [
  ("tuple_vector_assignments", rewrite_tuple_vector_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("remove_numeral_pats", rewrite_defs_remove_numeral_pats);
  ("guarded_pats", rewrite_defs_guarded_pats);
  (* ("register_ref_writes", rewrite_register_ref_writes); *)
  ("fix_val_specs", rewrite_fix_val_specs);
  ("recheck_defs", recheck_defs);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  (* ("constraint", rewrite_constraint); *)
  (* ("remove_assert", rewrite_defs_remove_assert); *)
  ("top_sort_defs", top_sort_defs);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ("early_return", rewrite_defs_early_return);
  ("nexp_ids", rewrite_defs_nexp_ids);
  ("fix_val_specs", rewrite_fix_val_specs);
  ("remove_blocks", rewrite_defs_remove_blocks);
  ("letbind_effects", rewrite_defs_letbind_effects);
  ("remove_e_assign", rewrite_defs_remove_e_assign);
  ("internal_lets", rewrite_defs_internal_lets);
  ("remove_superfluous_letbinds", rewrite_defs_remove_superfluous_letbinds);
  ("remove_superfluous_returns", rewrite_defs_remove_superfluous_returns);
  ("recheck_defs", recheck_defs)
  ]

let rewrite_defs_ocaml = [
    (* ("top_sort_defs", top_sort_defs); *)
    (* ("undefined", rewrite_undefined); *)
  ("no_effect_check", (fun defs -> opt_no_effects := true; defs));
  ("pat_lits", rewrite_defs_pat_lits);
  ("tuple_vector_assignments", rewrite_tuple_vector_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  ("constraint", rewrite_constraint);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ("simple_types", rewrite_simple_types);
  ("overload_cast", rewrite_overload_cast);
  (* ("separate_numbs", rewrite_defs_separate_numbs) *)
  ]

let rewrite_defs_c = [
  ("no_effect_check", (fun defs -> opt_no_effects := true; defs));
  ("pat_lits", rewrite_defs_pat_lits);
  ("tuple_vector_assignments", rewrite_tuple_vector_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  ("constraint", rewrite_constraint);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ]

let rewrite_defs_interpreter = [
    ("no_effect_check", (fun defs -> opt_no_effects := true; defs));
    ("tuple_vector_assignments", rewrite_tuple_vector_assignments);
    ("tuple_assignments", rewrite_tuple_assignments);
    ("simple_assignments", rewrite_simple_assignments);
    ("remove_vector_concat", rewrite_defs_remove_vector_concat);
    ("constraint", rewrite_constraint);
    ("trivial_sizeof", rewrite_trivial_sizeof);
    ("sizeof", rewrite_sizeof);
  ]

let rewrite_check_annot =
  let check_annot exp =
    try
      prerr_endline ("CHECKING: " ^ string_of_exp exp ^ " : " ^ string_of_typ (typ_of exp));
      let _ = check_exp (env_of exp) (strip_exp exp) (typ_of exp) in
      let typ1 = typ_of exp in
      let typ2 = Env.expand_synonyms (env_of exp) (typ_of exp) in
      (if not (alpha_equivalent (env_of exp) typ1 typ2)
       then raise (Reporting_basic.err_typ Parse_ast.Unknown
                    ("Found synonym in annotation " ^ string_of_typ typ1 ^ " vs " ^ string_of_typ typ2))
       else ());
      exp
    with
      Type_error (l, err) -> raise (Reporting_basic.err_typ l (string_of_type_error err))
  in
  let check_pat pat =
    prerr_endline ("CHECKING PAT: " ^ string_of_pat pat ^ " : " ^ string_of_typ (pat_typ_of pat));
    let _, _ = bind_pat_no_guard (pat_env_of pat) (strip_pat pat) (pat_typ_of pat) in
    pat
  in

  let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> check_annot (E_aux (exp, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp);
                                          rewrite_pat = (fun _ -> check_pat) }

let rewrite_defs_check = [
  ("check_annotations", rewrite_check_annot);
  ]
