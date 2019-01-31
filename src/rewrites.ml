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
open Extra_pervasives

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

let gen_vs (id, spec) = Initial_check.extern_of_string (mk_id id) spec

let annot_exp_effect e_aux l env typ effect = E_aux (e_aux, (l, mk_tannot env typ effect))
let annot_exp e_aux l env typ = annot_exp_effect e_aux l env typ no_effect
let annot_pat p_aux l env typ = P_aux (p_aux, (l, mk_tannot env typ no_effect))
let annot_letbind (p_aux, exp) l env typ =
  LB_aux (LB_val (annot_pat p_aux l env typ, exp), (l, mk_tannot env typ (effect_of exp)))

let simple_num l n = E_aux (
  E_lit (L_aux (L_num n, gen_loc l)),
  simple_annot (gen_loc l)
    (atom_typ (Nexp_aux (Nexp_constant n, gen_loc l))))

let effectful_effs = function
  | Effect_aux (Effect_set effs, _) -> not (effs = [])
    (*List.exists
      (fun (BE_aux (be,_)) ->
       match be with
       | BE_nondet | BE_unspec | BE_undef | BE_lset -> false
       | _ -> true
      ) effs*)

let effectful eaux = effectful_effs (effect_of eaux)
let effectful_pexp pexp = effectful_effs (effect_of_pexp pexp)

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
  | LEXP_tup lexps | LEXP_vector_concat lexps -> List.for_all (fun lexp -> lexp_is_local lexp env) lexps
  | LEXP_vector (lexp,_)
  | LEXP_vector_range (lexp,_,_)
  | LEXP_field (lexp,_) -> lexp_is_local lexp env

let rec lexp_is_local_intro (LEXP_aux (lexp, _)) env = match lexp with
  | LEXP_memory _ | LEXP_deref _ -> false
  | LEXP_id id
  | LEXP_cast (_, id) -> id_is_unbound id env
  | LEXP_tup lexps | LEXP_vector_concat lexps -> List.for_all (fun lexp -> lexp_is_local_intro lexp env) lexps
  | LEXP_vector (lexp,_)
  | LEXP_vector_range (lexp,_,_)
  | LEXP_field (lexp,_) -> lexp_is_local_intro lexp env

let lexp_is_effectful (LEXP_aux (_, (_, annot))) = match destruct_tannot annot with
  | Some (_, _, eff) -> effectful_effs eff
  | _ -> false

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let vector_string_to_bit_list l lit =

  let hexchar_to_binlist = function
    | '0' -> ['0';'0';'0';'0']
    | '1' -> ['0';'0';'0';'1']
    | '2' -> ['0';'0';'1';'0']
    | '3' -> ['0';'0';'1';'1']
    | '4' -> ['0';'1';'0';'0']
    | '5' -> ['0';'1';'0';'1']
    | '6' -> ['0';'1';'1';'0']
    | '7' -> ['0';'1';'1';'1']
    | '8' -> ['1';'0';'0';'0']
    | '9' -> ['1';'0';'0';'1']
    | 'A' -> ['1';'0';'1';'0']
    | 'B' -> ['1';'0';'1';'1']
    | 'C' -> ['1';'1';'0';'0']
    | 'D' -> ['1';'1';'0';'1']
    | 'E' -> ['1';'1';'1';'0']
    | 'F' -> ['1';'1';'1';'1']
    | _ -> raise (Reporting.err_unreachable l __POS__ "hexchar_to_binlist given unrecognized character") in

  let s_bin = match lit with
    | L_hex s_hex -> List.flatten (List.map hexchar_to_binlist (explode (String.uppercase_ascii s_hex)))
    | L_bin s_bin -> explode s_bin
    | _ -> raise (Reporting.err_unreachable l __POS__ "s_bin given non vector literal") in

  List.map (function '0' -> L_aux (L_zero, gen_loc l)
                   | '1' -> L_aux (L_one, gen_loc l)
                   | _ -> raise (Reporting.err_unreachable (gen_loc l) __POS__ "binary had non-zero or one")) s_bin

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

let lookup_equal_kids env =
  let get_eq_kids kid eqs = try KBindings.find kid eqs with Not_found -> KidSet.singleton kid in
  let add_eq_kids kid1 kid2 eqs =
    let kids = KidSet.union (get_eq_kids kid2 eqs) (get_eq_kids kid1 eqs) in
    eqs
    |> KBindings.add kid1 kids
    |> KBindings.add kid2 kids
  in
  let add_nc eqs = function
    | NC_aux (NC_equal (Nexp_aux (Nexp_var kid1, _), Nexp_aux (Nexp_var kid2, _)), _) ->
       add_eq_kids kid1 kid2 eqs
    | _ -> eqs
  in
  List.fold_left add_nc KBindings.empty (Env.get_constraints env)

let lookup_constant_kid env kid =
  let kids =
    match KBindings.find kid (lookup_equal_kids env) with
    | kids -> kids
    | exception Not_found -> KidSet.singleton kid
  in
  let check_nc const nc = match const, nc with
    | None, NC_aux (NC_equal (Nexp_aux (Nexp_var kid, _), Nexp_aux (Nexp_constant i, _)), _)
      when KidSet.mem kid kids ->
       Some i
    | _, _ -> const
  in
  List.fold_left check_nc None (Env.get_constraints env)

let rec rewrite_nexp_ids env (Nexp_aux (nexp, l) as nexp_aux) = match nexp with
  | Nexp_id id -> rewrite_nexp_ids env (Env.get_num_def id env)
  | Nexp_var kid ->
     begin
       match lookup_constant_kid env kid with
         | Some i -> nconstant i
         | None -> nexp_aux
     end
  | Nexp_times (nexp1, nexp2) -> Nexp_aux (Nexp_times (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
  | Nexp_sum (nexp1, nexp2) -> Nexp_aux (Nexp_sum (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
  | Nexp_minus (nexp1, nexp2) -> Nexp_aux (Nexp_minus (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
  | Nexp_exp nexp -> Nexp_aux (Nexp_exp (rewrite_nexp_ids env nexp), l)
  | Nexp_neg nexp -> Nexp_aux (Nexp_neg (rewrite_nexp_ids env nexp), l)
  | _ -> nexp_aux

let rewrite_defs_nexp_ids, rewrite_typ_nexp_ids =
  let rec rewrite_typ env (Typ_aux (typ, l) as typ_aux) = match typ with
    | Typ_fn (arg_ts, ret_t, eff) ->
       Typ_aux (Typ_fn (List.map (rewrite_typ env) arg_ts, rewrite_typ env ret_t, eff), l)
    | Typ_tup ts ->
       Typ_aux (Typ_tup (List.map (rewrite_typ env) ts), l)
    | Typ_exist (kids, c, typ) ->
       Typ_aux (Typ_exist (kids, c, rewrite_typ env typ), l)
    | Typ_app (id, targs) ->
       Typ_aux (Typ_app (id, List.map (rewrite_typ_arg env) targs), l)
    | _ -> typ_aux
  and rewrite_typ_arg env (A_aux (targ, l) as targ_aux) = match targ with
    | A_nexp nexp ->
       A_aux (A_nexp (rewrite_nexp_ids env nexp), l)
    | A_typ typ ->
       A_aux (A_typ (rewrite_typ env typ), l)
    | A_order ord ->
       A_aux (A_order ord, l)
    | A_bool nc ->
       A_aux (A_bool nc, l)
  in

  let rewrite_annot (l, tannot) =
    match destruct_tannot tannot with
    | Some (env, typ, eff) -> l, replace_typ (rewrite_typ env typ) tannot
    | None -> l, empty_tannot
  in

  let rewrite_def rewriters = function
    | DEF_spec (VS_aux (VS_val_spec (typschm, id, exts, b), (l, tannot))) when not (is_empty_tannot tannot) ->
       let env = env_of_annot (l, tannot) in
       let typ = typ_of_annot (l, tannot) in
       let eff = effect_of_annot tannot in
       let typschm = match typschm with
         | TypSchm_aux (TypSchm_ts (tq, typ), l) ->
            TypSchm_aux (TypSchm_ts (tq, rewrite_typ env typ), l)
       in
       let a = rewrite_annot (l, mk_tannot env typ eff) in
       DEF_spec (VS_aux (VS_val_spec (typschm, id, exts, b), a))
    | d -> Rewriter.rewrite_def rewriters d
  in

  rewrite_defs_base { rewriters_base with
    rewrite_exp = (fun _ -> map_exp_annot rewrite_annot); rewrite_def = rewrite_def
    },
  rewrite_typ


let rewrite_bitvector_exps defs =
  let e_aux = function
    | (E_vector es, ((l, tannot) as a)) when not (is_empty_tannot tannot) ->
       let env = env_of_annot (l, tannot) in
       let typ = typ_of_annot (l, tannot) in
       let eff = effect_of_annot tannot in
       if is_bitvector_typ typ then
         try
           let len = mk_lit_exp (L_num (Big_int.of_int (List.length es))) in
           let es = mk_exp (E_list (List.map strip_exp es)) in
           let exp = mk_exp (E_app (mk_id "bitvector_of_bitlist", [len; es])) in
           check_exp env exp typ
         with
         | _ -> E_aux (E_vector es, a)
       else
         E_aux (E_vector es, a)
    | (e_aux, a) -> E_aux (e_aux, a)
  in
  let rewrite_exp _ = fold_exp { id_exp_alg with e_aux = e_aux } in
  if IdSet.mem (mk_id "bitvector_of_bitlist") (Initial_check.val_spec_ids defs) then
    rewrite_defs_base { rewriters_base with rewrite_exp = rewrite_exp } defs
  else defs


(* Re-write trivial sizeof expressions - trivial meaning that the
   value of the sizeof can be directly inferred from the type
   variables in scope. *)
let rewrite_trivial_sizeof, rewrite_trivial_sizeof_exp =
  let extract_typ_var l env nexp (id, (_, typ)) =
    let var = E_aux (E_id id, (l, mk_tannot env typ no_effect)) in
    match destruct_atom_nexp env typ with
    | Some size when prove env (nc_eq size nexp) -> Some var
    (* AA: This next case is a bit of a hack... is there a more
       general way to deal with trivial nexps that are offset by
       constants? This will resolve a 'n - 1 sizeof when 'n is in
       scope. *)
    | Some size when prove env (nc_eq (nsum size (nint 1)) nexp) ->
       let one_exp = infer_exp env (mk_lit_exp (L_num (Big_int.of_int 1))) in
       Some (E_aux (E_app (mk_id "add_atom", [var; one_exp]), (gen_loc l, mk_tannot env (atom_typ (nsum size (nint 1))) no_effect)))
    | _ ->
       begin
         match destruct_vector env typ with
         | Some (len, _, _) when prove env (nc_eq len nexp) ->
            Some (E_aux (E_app (mk_id "length", [var]), (l, mk_tannot env (atom_typ len) no_effect)))
         | _ -> None
       end
  in
  let rec split_nexp (Nexp_aux (nexp_aux, l) as nexp) =
    match nexp_aux with
    | Nexp_sum (n1, n2) ->
       mk_exp (E_app (mk_id "add_atom", [split_nexp n1; split_nexp n2]))
    | Nexp_minus (n1, n2) ->
       mk_exp (E_app (mk_id "sub_atom", [split_nexp n1; split_nexp n2]))
    | Nexp_times (n1, n2) ->
       mk_exp (E_app (mk_id "mult_atom", [split_nexp n1; split_nexp n2]))
    | Nexp_neg nexp -> mk_exp (E_app (mk_id "negate_atom", [split_nexp nexp]))
    | _ -> mk_exp (E_sizeof nexp)
  in
  let rec rewrite_e_aux split_sizeof (E_aux (e_aux, (l, _)) as orig_exp) =
    let env = env_of orig_exp in
    match e_aux with
    | E_sizeof (Nexp_aux (Nexp_constant c, _) as nexp) ->
       E_aux (E_lit (L_aux (L_num c, l)), (l, mk_tannot env (atom_typ nexp) no_effect))
    | E_sizeof nexp ->
       begin
         match nexp_simp (rewrite_nexp_ids (env_of orig_exp) nexp) with
         | Nexp_aux (Nexp_constant c, _) ->
            E_aux (E_lit (L_aux (L_num c, l)), (l, mk_tannot env (atom_typ nexp) no_effect))
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
                   | Typ_app (atom, [A_aux (A_nexp nexp, _)])
                        when string_of_id atom = "atom" ->
                      [nexp, E_id id]
                   | Typ_app (vector, _) when string_of_id vector = "vector" ->
                      let id_length = Id_aux (Id "length", gen_loc l) in
                      (try
                         (match Env.get_val_spec id_length (env_of_annot annot) with
                          | _ ->
                             let (len,_,_) = vector_typ_args_of typ_aux in
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
             raise (Reporting.err_typ l (Type_error.string_of_type_error err)) in
         (* Rewrite the inst using orig_kid so that each type variable has it's
            original name rather than a mangled typechecker name *)
         let inst = KBindings.fold (fun kid uvar b -> KBindings.add (orig_kid kid) uvar b) inst KBindings.empty in
         let kid_exp kid = begin
             (* We really don't want to see an existential here! *)
             assert (not (Str.string_match ex_regex (string_of_kid kid) 0));
             let uvar = try Some (KBindings.find (orig_kid kid) inst) with Not_found -> None in
             match uvar with
             | Some (A_aux (A_nexp nexp, _)) ->
                let sizeof = E_aux (E_sizeof nexp, (l, mk_tannot env (atom_typ nexp) no_effect)) in
                (try rewrite_trivial_sizeof_exp sizeof with
                | Type_error (l, err) ->
                  raise (Reporting.err_typ l (Type_error.string_of_type_error err)))
             (* If the type variable is Not_found then it was probably
                introduced by a P_var pattern, so it likely exists as
                a variable in scope. It can't be an existential because the assert rules that out. *)
             | None -> annot_exp (E_id (id_of_kid (orig_kid kid))) l env (atom_typ (nvar (orig_kid kid)))
             | _ ->
                raise (Reporting.err_unreachable l __POS__
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
    ; e_record = (fun fexps -> let (fexps, fexps') = List.split fexps in (E_record fexps, E_record fexps'))
    ; e_record_update = (fun ((e1,e1'),fexps) -> let (fexps, fexps') = List.split fexps in (E_record_update (e1,fexps), E_record_update (e1',fexps')))
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
    ; e_var = (fun ((lexp,lexp'), (e2,e2'), (e3,e3')) -> (E_var (lexp,e2,e3), E_var (lexp',e2',e3')))
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
    ; lEXP_vector_concat = (fun lexps -> let (lexps,lexps') = List.split lexps in (LEXP_vector_concat lexps, LEXP_vector_concat lexps'))
    ; lEXP_field = (fun ((lexp,lexp'),id) -> (LEXP_field (lexp,id), LEXP_field (lexp',id)))
    ; lEXP_aux = (fun ((lexp,lexp'),annot) -> (LEXP_aux (lexp,annot), LEXP_aux (lexp',annot)))
    ; fE_Fexp = (fun (id,(e,e')) -> (FE_Fexp (id,e), FE_Fexp (id,e')))
    ; fE_aux = (fun ((fexp,fexp'),annot) -> (FE_aux (fexp,annot), FE_aux (fexp',annot)))
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
          match typ_of_pat paux with
          | Typ_aux (Typ_tup typs, _) ->
             let ptyp' = Typ_aux (Typ_tup (kid_typs @ typs), l) in
             (match pat with
              | P_tup pats ->
                 P_aux (P_tup (kid_pats @ pats), (l, mk_tannot penv ptyp' peff))
              | P_wild -> P_aux (pat, (l, mk_tannot penv ptyp' peff))
              | P_typ (Typ_aux (Typ_tup typs, l), pat) ->
                 P_aux (P_typ (Typ_aux (Typ_tup (kid_typs @ typs), l),
                               rewrite_pat pat), (l, mk_tannot penv ptyp' peff))
              | P_as (_, id) | P_id id ->
                 (* adding parameters here would change the type of id;
              we should remove the P_as/P_id here and add a let-binding to the body *)
                 raise (Reporting.err_todo l
                                                 "rewriting as- or id-patterns for sizeof expressions not yet implemented")
              | _ ->
                 raise (Reporting.err_unreachable l __POS__
                                                        "unexpected pattern while rewriting function parameters for sizeof expressions"))
          | ptyp ->
             let ptyp' = Typ_aux (Typ_tup (kid_typs @ [ptyp]), l) in
             P_aux (P_tup (kid_pats @ [paux]), (l, mk_tannot penv ptyp' peff)) in
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
    | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), annot)) ->
       let exp' = fst (fold_exp { copy_exp_alg with e_aux = e_app_aux params_map } exp) in
       (params_map, defs @ [DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp'), annot))])
    | def ->
       (params_map, defs @ [def]) in

  let rewrite_sizeof_valspec params_map def =
    let rewrite_typschm (TypSchm_aux (TypSchm_ts (tq, typ), l) as ts) id =
      if Bindings.mem id params_map then
        let kid_typs = List.map (fun kid -> atom_typ (nvar kid))
                                (KidSet.elements (Bindings.find id params_map)) in
        let typ' = match typ with
          | Typ_aux (Typ_fn (vtyp_args, vtyp_ret, declared_eff), vl) ->
             Typ_aux (Typ_fn (kid_typs @ vtyp_args, vtyp_ret, declared_eff), vl)
          | _ ->
            raise (Reporting.err_typ l "val spec with non-function type") in
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
  fst (Type_error.check initial_env (Defs defs))

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
      (* ToDo: I have no idea what the boolean parameter means so guessed that
       * "true" was a good value to use.
       * (Adding a comment explaining the boolean might be useful?)
       *)
    ; p_or  = (fun (pat1, pat2) -> P_or (pat1 true, pat2 true))
    ; p_not = (fun pat -> P_not (pat true))
    ; p_as  = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_var = (fun (pat,kid) -> P_var (pat true,kid))
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_tup            = (fun ps -> P_tup (List.map (fun p -> p false) ps))
    ; p_list           = (fun ps -> P_list (List.map (fun p -> p false) ps))
    ; p_cons           = (fun (p,ps) -> P_cons (p false, ps false))
    ; p_string_append  = (fun (ps) -> P_string_append (List.map (fun p -> p false) ps))
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
        | P_vector _ -> P_aux (P_as (pat, fresh_id_v l),a)
        | P_lit _ -> P_aux (P_as (pat, fresh_id_v l), a)
        | P_id id -> P_aux (P_id id,a)
        | P_as (p,id) -> P_aux (P_as (p,id),a)
        | P_typ (typ, pat) -> P_aux (P_typ (typ, aux pat),a)
        | P_wild -> P_aux (P_wild,a)
        | P_app (id, pats) when Env.is_mapping id (env_of_annot a) ->
           P_aux (P_app (id, List.map aux pats), a)
        | _ ->
           raise
             (Reporting.err_unreachable
                l __POS__ "name_vector_concat_elements: Non-vector in vector-concat pattern") in
      P_vector_concat (List.map aux pats) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in

  let pat = fold_pat name_vector_concat_elements pat in

  let rec tag_last = function
    | x :: xs -> let is_last = xs = [] in (x,is_last) :: tag_last xs
    | _ -> [] in

  (* remove names from vectors in vector_concat patterns and collect them as declarations for the
     function body or expression *)
  let unname_vector_concat_elements =
    (* build a let-expression of the form "let child = root[i..j] in body" *)
    let letbind_vec typ_opt (rootid,rannot) (child,cannot) (i,j) =
      let (l,_) = cannot in
      let env = env_of_annot rannot in
      let rootname = string_of_id rootid in
      let childname = string_of_id child in

      let root = E_aux (E_id rootid, rannot) in
      let index_i = simple_num l i in
      let index_j = simple_num l j in

      let subv = fix_eff_exp (E_aux (E_vector_subrange (root, index_i, index_j), cannot)) in

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
         let (start,last_idx) = (match vector_start_index rtyp, vector_typ_args_of rtyp with
          | Nexp_aux (Nexp_constant start,_), (Nexp_aux (Nexp_constant length,_), ord, _) ->
             (start, if is_order_inc ord
                     then Big_int.sub (Big_int.add start length) (Big_int.of_int 1)
                     else Big_int.add (Big_int.sub start length) (Big_int.of_int 1))
          | _ ->
            raise (Reporting.err_unreachable (fst rannot') __POS__
              ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern"))) in
         let rec aux typ_opt (pos,pat_acc,decl_acc) (P_aux (p,cannot),is_last) =
           let ctyp = Env.base_typ_of (env_of_annot cannot) (typ_of_annot cannot) in
           let (length,ord,_) = vector_typ_args_of ctyp in
           let (pos',index_j) = match length with
             | Nexp_aux (Nexp_constant i,_) ->
                if is_order_inc ord
                then (Big_int.add pos i, Big_int.sub (Big_int.add pos i) (Big_int.of_int 1))
                else (Big_int.sub pos i, Big_int.add (Big_int.sub pos i) (Big_int.of_int 1))
             | Nexp_aux (_,l) ->
                if is_last then (pos,last_idx)
                else
                  raise
                    (Reporting.err_unreachable
                       l __POS__ ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern")) in
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
            (* | P_app (cname, pats) if Env.is_mapping cname (en) ->
             *    let (lb,decl,info) = letbind_vec typ_opt (rootid,rannot) (cname,cannot) (pos,index_j) in
             *    (pos', pat_acc @ [P_aux (P_app (cname,pats),cannot)], decl_acc @ [((lb,decl),info)]) *)
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
    ; p_or             = (fun ((pat1, ds1), (pat2, ds2)) -> (P_or(pat1, pat2), ds1 @ ds2))
    ; p_not            = (fun (pat, ds) -> (P_not(pat), ds))
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
    ; p_string_append  = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_string_append ps,List.flatten decls))
    ; p_cons           = (fun ((p,decls),(p',decls')) -> (P_cons (p,p'), decls @ decls'))
    ; p_aux            = (fun ((pat,decls),annot) -> p_aux ((pat,decls),annot))
    ; fP_aux           = (fun ((fpat,decls),annot) -> (FP_aux (fpat,annot),decls))
    ; fP_Fpat          = (fun (id,(pat,decls)) -> (FP_Fpat (id,pat),decls))
    } in

  let (pat,decls) = fold_pat unname_vector_concat_elements pat in

  (* We need to put the decls in the right order so letbinds are generated correctly for nested patterns *)
  let module G = Graph.Make(String) in
  let root_graph = List.fold_left (fun g (_, (root_id, child_id)) -> G.add_edge root_id child_id g) G.empty decls in
  let root_order = G.topsort root_graph in
  let find_root root_id =
    try List.find (fun (_, (root_id', _)) -> root_id = root_id') decls with
    | Not_found ->
    (* If it's not a root the it's a leaf node in the graph, so search for child_id *)
    try List.find (fun (_, (_, child_id)) -> root_id = child_id) decls with
    | Not_found -> assert false (* Should never happen *)
  in
  let decls = List.map find_root root_order in

  let (letbinds,decls) =
    let decls = List.map fst decls in
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
        let wild _ = P_aux (P_wild,(gen_loc l, mk_tannot env bit_typ eff)) in
        if is_vector_typ typ then
          match p, vector_typ_args_of typ with
          | P_vector ps,_ -> acc @ ps
          | _, (Nexp_aux (Nexp_constant length,_),_,_) ->
             acc @ (List.map wild (range Big_int.zero (Big_int.sub length (Big_int.of_int 1))))
          | _, _ ->
            (*if is_last then*) acc @ [wild Big_int.zero]
        else raise
          (Reporting.err_unreachable l __POS__
            ("remove_vector_concats: Non-vector in vector-concat pattern " ^
              string_of_typ (typ_of_annot annot))) in

      let has_length (P_aux (p,annot)) =
        let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
        match vector_typ_args_of typ with
        | (Nexp_aux (Nexp_constant length,_),_,_) -> true
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

let rec is_irrefutable_pattern (P_aux (p,ann)) =
  match p with
  | P_lit (L_aux (L_unit,_))
  | P_wild
    -> true
  | P_or(pat1, pat2) -> is_irrefutable_pattern pat1 && is_irrefutable_pattern pat2
  | P_not(pat) -> is_irrefutable_pattern pat
  | P_lit _ -> false
  | P_as (p1,_)
  | P_typ (_,p1)
    -> is_irrefutable_pattern p1
  | P_id id -> begin
    match Env.lookup_id id (env_of_annot ann) with
    | Local _ | Unbound -> true
    | Register _ -> false (* should be impossible, anyway *)
    | Enum enum ->
       match enum with
       | Typ_aux (Typ_id enum_id,_) ->
          List.length (Env.get_enum enum_id (env_of_annot ann)) <= 1
       | _ -> false (* should be impossible, anyway *)
  end
  | P_var (p1,_) -> is_irrefutable_pattern p1
  | P_app (f,args) ->
     Env.is_singleton_union_constructor f (env_of_annot ann) &&
       List.for_all is_irrefutable_pattern args
  | P_record (fps,_) ->
     List.for_all (fun (FP_aux (FP_Fpat (_,p),_)) -> is_irrefutable_pattern p) fps
  | P_vector ps
  | P_vector_concat ps
  | P_tup ps
  | P_list ps
    -> List.for_all is_irrefutable_pattern ps
  | P_cons (p1,p2) -> is_irrefutable_pattern p1 && is_irrefutable_pattern p2
  | P_string_append ps
    -> List.for_all is_irrefutable_pattern ps

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
  | P_or(pat1, pat2), _ -> (* todo: possibly not the right answer *) None
  | _, P_or(pat1, pat2) -> (* todo: possibly not the right answer *) None
  | P_not(pat), _ -> (* todo: possibly not the right answer *) None
  | _, P_not(pat) -> (* todo: possibly not the right answer *) None
  | P_as (pat1,_), _ -> subsumes_pat pat1 pat2
  | _, P_as (pat2,_) -> subsumes_pat pat1 pat2
  | P_typ (_,pat1), _ -> subsumes_pat pat1 pat2
  | _, P_typ (_,pat2) -> subsumes_pat pat1 pat2
  | P_id (Id_aux (id1,_) as aid1), P_id (Id_aux (id2,_) as aid2) ->
    if id1 = id2 then Some []
    else if Env.lookup_id aid1 (env_of_annot annot1) = Unbound
    then if Env.lookup_id aid2 (env_of_annot annot2) = Unbound
      then Some [(id2,id1)]
      else Some []
    else None
  | P_id id1, _ ->
    if Env.lookup_id id1 (env_of_annot annot1) = Unbound then Some [] else None
  | P_var (pat1,_), P_var (pat2,_) -> subsumes_pat pat1 pat2
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
  | _, P_wild -> if is_irrefutable_pattern pat1 then Some [] else None
  | _ -> None
and subsumes_fpat (FP_aux (FP_Fpat (id1,pat1),_)) (FP_aux (FP_Fpat (id2,pat2),_)) =
  if id1 = id2 then subsumes_pat pat1 pat2 else None

(* A simple check for pattern disjointness; used for optimisation in the
   guarded pattern rewrite step *)
let rec disjoint_pat (P_aux (p1,annot1) as pat1) (P_aux (p2,annot2) as pat2) =
  match p1, p2 with
  | P_as (pat1, _), _ -> disjoint_pat pat1 pat2
  | _, P_as (pat2, _) -> disjoint_pat pat1 pat2
  | P_typ (_, pat1), _ -> disjoint_pat pat1 pat2
  | _, P_typ (_, pat2) -> disjoint_pat pat1 pat2
  | P_var (pat1, _), _ -> disjoint_pat pat1 pat2
  | _, P_var (pat2, _) -> disjoint_pat pat1 pat2
  | P_id id, _ when id_is_unbound id (env_of_annot annot1) -> false
  | _, P_id id when id_is_unbound id (env_of_annot annot2) -> false
  | P_id id1, P_id id2 -> Id.compare id1 id2 <> 0
  | P_app (id1, args1), P_app (id2, args2) ->
     Id.compare id1 id2 <> 0 || List.exists2 disjoint_pat args1 args2
  | P_vector pats1, P_vector pats2
  | P_tup pats1, P_tup pats2
  | P_list pats1, P_list pats2 ->
     List.exists2 disjoint_pat pats1 pats2
  | _ -> false

let equiv_pats pat1 pat2 =
  match subsumes_pat pat1 pat2, subsumes_pat pat2 pat1 with
  | Some _, Some _ -> true
  | _, _ -> false

let subst_id_pat pat (id1,id2) =
  let p_id (Id_aux (id,l)) = (if id = id1 then P_id (Id_aux (id2,l)) else P_id (Id_aux (id,l))) in
  fold_pat {id_pat_alg with p_id = p_id} pat

let subst_id_exp exp (id1,id2) =
  Ast_util.subst (Id_aux (id1,Parse_ast.Unknown)) (E_aux (E_id (Id_aux (id2,Parse_ast.Unknown)),(Parse_ast.Unknown,empty_tannot))) exp

let rec pat_to_exp ((P_aux (pat,(l,annot))) as p_aux) =
  let rewrap e = E_aux (e,(l,annot)) in
  let env = env_of_pat p_aux in
  let typ = typ_of_pat p_aux in
  match pat with
  | P_lit lit -> rewrap (E_lit lit)
  | P_wild -> raise (Reporting.err_unreachable l __POS__
      "pat_to_exp given wildcard pattern")
  | P_or(pat1, pat2) -> (* todo: insert boolean or *) pat_to_exp pat1 
  | P_not(pat) -> (* todo: insert boolean not *) pat_to_exp pat
  | P_as (pat,id) -> rewrap (E_id id)
  | P_var (pat, _) -> pat_to_exp pat
  | P_typ (_,pat) -> pat_to_exp pat
  | P_id id -> rewrap (E_id id)
  | P_app (id,pats) -> rewrap (E_app (id, List.map pat_to_exp pats))
  | P_record (fpats,b) ->
      rewrap (E_record (List.map fpat_to_fexp fpats))
  | P_vector pats -> rewrap (E_vector (List.map pat_to_exp pats))
  | P_vector_concat pats -> begin
      let empty_vec = E_aux (E_vector [], (l,())) in
      let concat_vectors vec1 vec2 =
        E_aux (E_vector_append (vec1, vec2), (l, ()))
      in
      check_exp env (List.fold_right concat_vectors (List.map (fun p -> strip_exp (pat_to_exp p)) pats) empty_vec) typ
    end
  | P_tup pats -> rewrap (E_tuple (List.map pat_to_exp pats))
  | P_list pats -> rewrap (E_list (List.map pat_to_exp pats))
  | P_cons (p,ps) -> rewrap (E_cons (pat_to_exp p, pat_to_exp ps))
  | P_string_append (pats) -> begin
      let empty_string = annot_exp (E_lit (L_aux (L_string "", l))) l env string_typ in
      let string_append str1 str2 =
        annot_exp (E_app (mk_id "string_append", [str1; str2])) l env string_typ
      in
      (List.fold_right string_append (List.map pat_to_exp pats) empty_string)
    end

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

(* Rewrite guarded patterns into a combination of if-expressions and
   unguarded pattern matches

   Strategy:
   - Split clauses into groups where the first pattern subsumes all the
     following ones
   - Translate the groups in reverse order, using the next group as a
     fall-through target, if there is one
   - Within a group,
     - translate the sequence of clauses to an if-then-else cascade using the
       guards as long as the patterns are equivalent modulo substitution, or
     - recursively translate the remaining clauses to a pattern match if
       there is a difference in the patterns.

  TODO: Compare this more closely with the algorithm in the CPP'18 paper of
  Spector-Zabusky et al, who seem to use the opposite grouping and merging
  strategy to ours: group *mutually exclusive* clauses, and try to merge them
  into a pattern match first instead of an if-then-else cascade.
*)
let rewrite_guarded_clauses l cs =
  let rec group fallthrough clauses =
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
          raise (Reporting.err_unreachable l __POS__
            "group given empty list in rewrite_guarded_clauses") in
    let add_group cs groups = (if_pexp (groups @ fallthrough) cs) :: groups in
    List.fold_right add_group groups []
  and if_pexp fallthrough (pat,cs,annot) = (match cs with
    | c :: _ ->
        (* fix_eff_pexp (pexp *)
        let body = if_exp fallthrough pat cs in
        let pexp = fix_eff_pexp (Pat_aux (Pat_exp (pat,body),annot)) in
        let (Pat_aux (_,annot)) = pexp in
        (pat, body, annot)
    | [] ->
        raise (Reporting.err_unreachable l __POS__
            "if_pexp given empty list in rewrite_guarded_clauses"))
  and if_exp fallthrough current_pat = (function
    | (pat,guard,body,annot) :: ((pat',guard',body',annot') as c') :: cs ->
        (match guard with
          | Some exp ->
              let else_exp =
                if equiv_pats current_pat pat'
                then if_exp fallthrough current_pat (c' :: cs)
                else case_exp (pat_to_exp current_pat) (typ_of body') (group fallthrough (c' :: cs)) in
              fix_eff_exp (annot_exp (E_if (exp,body,else_exp)) (fst annot) (env_of exp) (typ_of body))
          | None -> body)
    | [(pat,guard,body,annot)] ->
        (* For singleton clauses with a guard, use fallthrough clauses if the
           guard is not satisfied, but only those fallthrough clauses that are
           not disjoint with the current pattern *)
        let overlapping_clause (pat, _, _) = not (disjoint_pat current_pat pat) in
        let fallthrough = List.filter overlapping_clause fallthrough in
        (match guard, fallthrough with
          | Some exp, _ :: _ ->
              let else_exp = case_exp (pat_to_exp current_pat) (typ_of body) fallthrough in
              fix_eff_exp (annot_exp (E_if (exp,body,else_exp)) (fst annot) (env_of exp) (typ_of body))
          | _, _ -> body)
    | [] ->
        raise (Reporting.err_unreachable l __POS__
            "if_exp given empty list in rewrite_guarded_clauses")) in
  group [] cs

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
| P_or(pat1, pat2) -> contains_bitvector_pat pat1 || contains_bitvector_pat pat2
| P_not(pat) -> contains_bitvector_pat pat
| P_vector _ | P_vector_concat _ ->
    let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
    is_bitvector_typ typ
| P_app (_,pats) | P_tup pats | P_list pats ->
    List.exists contains_bitvector_pat pats
| P_cons (p,ps) -> contains_bitvector_pat p || contains_bitvector_pat ps
| P_string_append (ps) -> List.exists contains_bitvector_pat ps
| P_record (fpats,_) ->
    List.exists (fun (FP_aux (FP_Fpat (_,pat),_)) -> contains_bitvector_pat pat) fpats

let contains_bitvector_pexp = function
| Pat_aux (Pat_exp (pat,_),_) | Pat_aux (Pat_when (pat,_,_),_) ->
  contains_bitvector_pat pat

(* Rewrite bitvector patterns to guarded patterns *)

let remove_bitvector_pat (P_aux (_, (l, _)) as pat) =

  let env = try env_of_pat pat with _ -> Env.empty in

  (* first introduce names for bitvector patterns *)
  let name_bitvector_roots =
    { p_lit = (fun lit -> P_lit lit)
    ; p_typ = (fun (typ,p) -> P_typ (typ,p false))
    ; p_wild = P_wild
    (* todo: I have no idea what the boolean parameter means - so I randomly
     * passed "true".  A comment to explain the bool might be a good idea?
     *)
    ; p_or  = (fun (pat1, pat2) -> P_or (pat1 true, pat2 true))
    ; p_not = (fun pat -> P_not (pat true))
    ; p_as  = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_var = (fun (pat,kid) -> P_var (pat true,kid))
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_string_append  = (fun ps -> P_string_append (List.map (fun p -> p false) ps))
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
    (typ_of_pat pat) in

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
    let start = vector_start_index typ in
    let (length, ord, _) = vector_typ_args_of typ in
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
    let letbind = LB_aux (LB_val (e,elem), (l, mk_tannot env bit_typ no_effect)) in
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
      let start = vector_start_index t in
      let (_,ord,_) = vector_typ_args_of t in
      let start_idx = match start with
      | Nexp_aux (Nexp_constant s, _) -> s
      | _ ->
        raise (Reporting.err_unreachable l __POS__
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
    ; p_or             = (fun ((pat1, gdl1), (pat2, gdl2)) ->
                              (P_or(pat1, pat2), flatten_guards_decls [gdl1; gdl2]))
    ; p_not            = (fun (pat, gdl) -> (P_not(pat), gdl))
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
    ; p_string_append  = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_string_append ps, flatten_guards_decls gdls))
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
  let p_lit outer_env = function
    | L_aux (L_num n, l) ->
       let id = fresh_id "l__" Parse_ast.Unknown in
       let typ = atom_typ (nconstant n) in
       let guard =
         mk_exp (E_app_infix (
           mk_exp (E_id id),
           mk_id "==",
           mk_lit_exp (L_num n)
         )) in
       (* Check expression in reasonable approx of environment to resolve overriding *)
       let env = Env.add_local id (Immutable, typ) outer_env in
       let checked_guard = check_exp env guard bool_typ in
       (Some checked_guard, P_id id)
    | lit -> (None, P_lit lit) in
  let guard_pat outer_env =
    fold_pat { (compute_pat_alg None compose_guard_opt) with p_lit = p_lit outer_env } in
  let pat_aux (pexp_aux, a) =
    let pat,guard,exp,a = destruct_pexp (Pat_aux (pexp_aux, a)) in
    let guard',pat = guard_pat (env_of_pat pat) pat in
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

let rewrite_defs_vector_string_pats_to_bit_list =
  let rewrite_p_aux (pat, (annot : tannot annot)) =
    let env = env_of_annot annot in
    match pat with
    | P_lit (L_aux (lit, l) as l_aux) ->
       begin match lit with
       | L_hex _ | L_bin _ -> P_aux (P_vector (List.map (fun p -> P_aux (P_lit p, (l, mk_tannot env bit_typ no_effect))) (vector_string_to_bit_list l lit)), annot)
       | lit -> P_aux (P_lit l_aux, annot)
       end
    | pat -> (P_aux (pat, annot))
  in
  let rewrite_e_aux (exp, (annot : tannot annot)) =
    let env = env_of_annot annot in
    match exp with
    | E_lit (L_aux (lit, l) as l_aux) ->
       begin match lit with
       | L_hex _ | L_bin _ -> E_aux (E_vector (List.map (fun e -> E_aux (E_lit e, (l, mk_tannot env bit_typ no_effect))) (vector_string_to_bit_list l lit)), annot)
       | lit -> E_aux (E_lit l_aux, annot)
       end
    | exp -> (E_aux (exp, annot))
  in
  let pat_alg = { id_pat_alg with p_aux = rewrite_p_aux } in
  let rewrite_pat rw pat =
    fold_pat pat_alg pat
  in
  let rewrite_exp rw exp =
    fold_exp { id_exp_alg with e_aux = rewrite_e_aux; pat_alg = pat_alg } exp
  in
  rewrite_defs_base { rewriters_base with rewrite_pat = rewrite_pat; rewrite_exp = rewrite_exp }

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
      (pat, Some (rewrite_rec guard), rewrite_rec body, annot) in
    let clauses = rewrite_guarded_clauses l (List.map clause ps) in
    let e = rewrite_rec e in
    if (effectful e) then
      let (E_aux (_,(el,eannot))) = e in
      let pat_e' = fresh_id_pat "p__" (el, mk_tannot (env_of e) (typ_of e) no_effect) in
      let exp_e' = pat_to_exp pat_e' in
      let letbind_e = LB_aux (LB_val (pat_e',e), (el,eannot)) in
      let exp' = case_exp exp_e' (typ_of full_exp) clauses in
      rewrap (E_let (letbind_e, exp'))
    else case_exp e (typ_of full_exp) clauses
  | E_try (e,ps)
    when List.exists is_guarded_pexp ps ->
    let e = rewrite_rec e in
    let clause = function
    | Pat_aux (Pat_exp (pat, body), annot) ->
      (pat, None, rewrite_rec body, annot)
    | Pat_aux (Pat_when (pat, guard, body), annot) ->
      (pat, Some (rewrite_rec guard), rewrite_rec body, annot) in
    let clauses = rewrite_guarded_clauses l (List.map clause ps) in
    let pexp (pat,body,annot) = Pat_aux (Pat_exp (pat,body),annot) in
    let ps = List.map pexp clauses in
    fix_eff_exp (annot_exp (E_try (e,ps)) l (env_of full_exp) (typ_of full_exp))
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
         FCL_aux (FCL_Funcl(id,construct_pexp (pat,None,exp,(Parse_ast.Unknown,empty_tannot))),annot)) cs
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
          let field_update exp = FE_aux (FE_Fexp (id, exp), annot) in
          (lhs, (fun exp -> rhs (E_aux (E_record_update (lexp_to_exp lexp, [field_update exp]), lannot))))
       | _ -> raise (Reporting.err_unreachable l __POS__ ("Unsupported lexp: " ^ string_of_lexp le))
     end
  | _ -> raise (Reporting.err_unreachable l __POS__ ("Unsupported lexp: " ^ string_of_lexp le))

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
      | (E_aux(E_assign(le,e), (l, tannot)) as exp)::exps
           when not (is_empty_tannot tannot) && lexp_is_local_intro le (env_of_annot (l, tannot)) && not (lexp_is_effectful le) ->
         let env = env_of_annot (l, tannot) in
         let (le', re') = rewrite_lexp_to_rhs le in
         let e' = re' (rewrite_base e) in
         let exps' = walker exps in
         let effects = union_eff_exps exps' in
         let block = E_aux (E_block exps', (gen_loc l, mk_tannot env unit_typ effects)) in
         [fix_eff_exp (E_aux (E_var(le', e', block), annot))]
      | e::exps -> (rewrite_rec e)::(walker exps)
    in
    E_aux (E_block (walker exps), annot)

  | E_assign(le,e)
    when lexp_is_local_intro le (env_of full_exp) && not (lexp_is_effectful le) ->
    let (le', re') = rewrite_lexp_to_rhs le in
    let e' = re' (rewrite_base e) in
    let block = annot_exp (E_block []) (gen_loc l) (env_of full_exp) unit_typ in
    E_aux (E_var (le', e', block), annot)

  | _ -> rewrite_base full_exp

let rewrite_defs_exp_lift_assign defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_lift_assign_intro;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp (*_lift_assign_intro*);
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
  let (Defs write_reg_spec) = fst (Type_error.check Env.empty (Defs (List.map gen_vs
    [("write_reg_ref", "forall ('a : Type). (register('a), 'a) -> unit effect {wreg}")]))) in
  let lexp_ref_exp (LEXP_aux (_, annot) as lexp) =
    try
      let exp = infer_exp (env_of_annot annot) (strip_exp (lexp_to_exp lexp)) in
      if is_ref_typ (typ_of exp) then Some exp else None
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

  let rec is_return (E_aux (exp, _)) = match exp with
  | E_return _ -> true
  | E_cast (_, e) -> is_return e
  | _ -> false in

  let rec get_return (E_aux (e, annot) as exp) = match e with
  | E_return e -> e
  | E_cast (typ, e) -> E_aux (E_cast (typ, get_return e), annot)
  | _ -> exp in

  let contains_return exp =
    fst (fold_exp
    { (compute_exp_alg false (||))
      with e_return = (fun (_, r) -> (true, E_return r)) } exp) in

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
    | [] -> (Parse_ast.Unknown, empty_tannot) in
    if List.for_all is_return_pexp pes
    then E_return (E_aux (E_case (e, List.map get_return_pexp pes), annot))
    else E_case (e, pes) in

  let e_let (lb, exp) =
    let (E_aux (_, annot) as ret_exp) = get_return exp in
    if is_return exp then E_return (E_aux (E_let (lb, ret_exp), annot))
    else E_let (lb, exp) in

  let e_var (lexp, exp1, exp2) =
    let (E_aux (_, annot) as ret_exp2) = get_return exp2 in
    if is_return exp2 then
      E_return (E_aux (E_var (lexp, exp1, ret_exp2), annot))
    else E_var (lexp, exp1, exp2) in

  let e_app (id, es) =
    try E_return (get_return (List.find is_return es))
    with
    | Not_found -> E_app (id, es)
  in

  let e_aux (exp, (l, annot)) =
    let full_exp = propagate_exp_effect (E_aux (exp, (l, annot))) in
    let env = env_of full_exp in
    match full_exp with
    | E_aux (E_return exp, (l, tannot)) when not (is_empty_tannot tannot) ->
      (* Add escape effect annotation, since we use the exception mechanism
         of the state monad to implement early return in the Lem backend *)
       let typ = typ_of_annot (l, tannot) in
       let env = env_of_annot (l, tannot) in
       let eff = effect_of_annot tannot in
       let tannot' = mk_tannot env typ (union_effects eff (mk_effect [BE_escape])) in
       let exp' = match Env.get_ret_typ env with
         | Some typ -> add_e_cast typ exp
         | None -> exp in
       E_aux (E_app (mk_id "early_return", [exp']), (l, tannot'))
    | _ -> full_exp in

  (* Make sure that all final leaves of an expression (e.g. all branches of
     the last if-expression) are wrapped in a return statement.  This allows
     the above rewriting to uniformly pull these returns back out, even if
     originally only one of the branches of the last if-expression was a
     return, and the other an "exit()", for example. *)
  let rec add_final_return nested (E_aux (e, annot) as exp) =
    let rewrap e = E_aux (e, annot) in
    match e with
      | E_return _ -> exp
      | E_cast (typ, e') ->
         begin
           let (E_aux (e_aux', annot') as e') = add_final_return nested e' in
           match e_aux' with
             | E_return e' -> rewrap (E_return (rewrap (E_cast (typ, e'))))
             | _ -> rewrap (E_cast (typ, e'))
         end
      | E_block ((_ :: _) as es) ->
         rewrap (E_block (Util.butlast es @ [add_final_return true (Util.last es)]))
      | E_if (c, t, e) ->
         rewrap (E_if (c, add_final_return true t, add_final_return true e))
      | E_let (lb, exp) ->
         rewrap (E_let (lb, add_final_return true exp))
      | E_var (lexp, e1, e2) ->
         rewrap (E_var (lexp, e1, add_final_return true e2))
      | _ ->
         if nested && not (contains_return exp) then rewrap (E_return exp) else exp
  in

  let rewrite_funcl_early_return _ (FCL_aux (FCL_Funcl (id, pexp), a)) =
    let pat,guard,exp,pannot = destruct_pexp pexp in
    let exp =
      if contains_return exp then
        (* Try to pull out early returns as far as possible *)
        let exp' =
          fold_exp
            { id_exp_alg with e_block = e_block; e_if = e_if; e_case = e_case;
              e_let = e_let; e_var = e_var; e_app = e_app }
            (add_final_return false exp) in
        (* Remove early return if we can pull it out completely, and rewrite
           remaining early returns to "early_return" calls *)
        fold_exp
          { id_exp_alg with e_aux = e_aux }
          (if is_return exp' then get_return exp' else exp)
      else exp
    in
    let a = match destruct_tannot (snd a) with
      | Some (env, typ, eff) ->
         (fst a, mk_tannot env typ (union_effects eff (effect_of exp)))
      | _ -> a in
    FCL_aux (FCL_Funcl (id, construct_pexp (pat, guard, exp, pannot)), a) in

  let rewrite_fun_early_return rewriters
    (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), a)) =
    FD_aux (FD_function (rec_opt, tannot_opt, effect_opt,
      List.map (rewrite_funcl_early_return rewriters) funcls), a) in

  let (Defs early_ret_spec) = fst (Type_error.check Env.empty (Defs [gen_vs
    ("early_return", "forall ('a : Type) ('b : Type). 'a -> 'b effect {escape}")])) in

  rewrite_defs_base
    { rewriters_base with rewrite_fun = rewrite_fun_early_return }
    (Defs (early_ret_spec @ defs))

let swaptyp typ (l,tannot) = match destruct_tannot tannot with
  | Some (env, typ', eff) -> (l, mk_tannot env typ eff)
  | _ -> raise (Reporting.err_unreachable l __POS__ "swaptyp called with empty type annotation")

let is_funcl_rec (FCL_aux (FCL_Funcl (id, pexp), _)) =
  let pat,guard,exp,pannot = destruct_pexp pexp in
  let exp = match guard with None -> exp
    | Some exp' -> E_aux (E_block [exp';exp],(Parse_ast.Unknown,empty_tannot)) in
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


let pat_var (P_aux (paux, a)) =
  let env = env_of_annot a in
  let is_var id =
    not (Env.is_union_constructor id env) &&
      match Env.lookup_id id env with Enum _ -> false | _ -> true
  in match paux with
  | (P_as (_, id) | P_id id) when is_var id -> Some id
  | _ -> None

(* Split out function clauses for individual union constructor patterns
   (e.g. AST nodes) into auxiliary functions.  Used for the execute function. *)
let rewrite_split_fun_constr_pats fun_name (Defs defs) =
  let rewrite_fundef typquant (FD_aux (FD_function (r_o, t_o, e_o, clauses), ((l, _) as fdannot))) =
    let rec_clauses, clauses = List.partition is_funcl_rec clauses in
    let clauses, aux_funs =
      List.fold_left
        (fun (clauses, aux_funs) (FCL_aux (FCL_Funcl (id, pexp), fannot) as clause) ->
           let pat, guard, exp, annot = destruct_pexp pexp in
           match pat with
             | P_aux (P_app (constr_id, args), pannot) ->
                let argstup_typ = tuple_typ (List.map typ_of_pat args) in
                let pannot' = swaptyp argstup_typ pannot in
                let pat' =
                  match args with
                  | [arg] -> arg
                  | _ -> P_aux (P_tup args, pannot')
                in
                let pexp' = construct_pexp (pat', guard, exp, annot) in
                let aux_fun_id = prepend_id (fun_name ^ "_") constr_id in
                let aux_funcl = FCL_aux (FCL_Funcl (aux_fun_id, pexp'), pannot') in
                begin
                  try
                    let aux_clauses = Bindings.find aux_fun_id aux_funs in
                    clauses,
                    Bindings.add aux_fun_id (aux_clauses @ [aux_funcl]) aux_funs
                  with Not_found ->
                    let argpats, argexps = List.split (List.mapi
                     (fun idx (P_aux (_,a) as pat) ->
                        let id = match pat_var pat with
                          | Some id -> id
                          | None -> mk_id ("arg" ^ string_of_int idx)
                        in
                        P_aux (P_id id, a), E_aux (E_id id, a))
                     args)
                    in
                    let pexp = construct_pexp
                     (P_aux (P_app (constr_id, argpats), pannot),
                      None,
                      E_aux (E_app (aux_fun_id, argexps), annot),
                      annot)
                    in
                    clauses @ [FCL_aux (FCL_Funcl (id, pexp), fannot)],
                    Bindings.add aux_fun_id [aux_funcl] aux_funs
                end
             | _ -> clauses @ [clause], aux_funs)
        ([], Bindings.empty) clauses
    in
    let add_aux_def id funcls defs =
      let env, args_typ, ret_typ = match funcls with
        | FCL_aux (FCL_Funcl (_, pexp), _) :: _ ->
           let pat, _, exp, _ = destruct_pexp pexp in
           env_of exp, typ_of_pat pat, typ_of exp
        | _ ->
           raise (Reporting.err_unreachable l __POS__
             "rewrite_split_fun_constr_pats: empty auxiliary function")
      in
      let eff = List.fold_left
        (fun eff (FCL_aux (FCL_Funcl (_, pexp), _)) ->
           let _, _, exp, _ = destruct_pexp pexp in
           union_effects eff (effect_of exp))
        no_effect funcls
      in
      let fun_typ =
        (* Because we got the argument type from a pattern we need to
           do this. *)
        match args_typ with
        | Typ_aux (Typ_tup (args_typs), _) ->
           function_typ args_typs ret_typ eff
        | _ ->
           function_typ [args_typ] ret_typ eff
      in
      let quant_new_tyvars qis =
        let quant_tyvars = List.fold_left KidSet.union KidSet.empty (List.map tyvars_of_quant_item qis) in
        let typ_tyvars = tyvars_of_typ fun_typ in
        let new_tyvars = KidSet.diff typ_tyvars quant_tyvars in
        List.map (mk_qi_id K_int) (KidSet.elements new_tyvars)
      in
      let typquant = match typquant with
        | TypQ_aux (TypQ_tq qis, l) ->
           let qis =
             List.filter
               (fun qi -> KidSet.subset (tyvars_of_quant_item qi) (tyvars_of_typ fun_typ))
               qis
             @ quant_new_tyvars qis
           in
           TypQ_aux (TypQ_tq qis, l)
        | _ ->
           TypQ_aux (TypQ_tq (List.map (mk_qi_id K_int) (KidSet.elements (tyvars_of_typ fun_typ))), l)
      in
      let val_spec =
        VS_aux (VS_val_spec
          (mk_typschm typquant fun_typ, id, (fun _ -> None), false),
          (Parse_ast.Unknown, empty_tannot))
      in
      let fundef = FD_aux (FD_function (r_o, t_o, e_o, funcls), fdannot) in
      [DEF_spec val_spec; DEF_fundef fundef] @ defs
    in
    Bindings.fold add_aux_def aux_funs
      [DEF_fundef (FD_aux (FD_function (r_o, t_o, e_o, rec_clauses @ clauses), fdannot))]
  in
  let typquant = List.fold_left (fun tq def -> match def with
    | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (tq, _), _), id, _, _), _))
      when string_of_id id = fun_name -> tq
    | _ -> tq) (mk_typquant []) defs
  in
  let defs = List.fold_right (fun def defs -> match def with
    | DEF_fundef fundef when string_of_id (id_of_fundef fundef) = fun_name ->
       rewrite_fundef typquant fundef @ defs
    | _ -> def :: defs) defs []
  in
  Defs defs

(* Propagate effects of functions, if effect checking and propagation
   have not been performed already by the type checker. *)
let rewrite_fix_val_specs (Defs defs) =
  let find_vs env val_specs id =
    try Bindings.find id val_specs with
    | Not_found ->
       begin
         try Env.get_val_spec id env with
         | _ ->
            raise (Reporting.err_unreachable (Parse_ast.Unknown) __POS__
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
    | E_aux (E_app_infix (_, f, _) as exp, (l, tannot))
    | E_aux (E_app (f, _) as exp, (l, tannot))
         when not (is_empty_tannot tannot) ->
       let env = env_of_annot (l, tannot) in
       let typ = typ_of_annot (l, tannot) in
       let eff = effect_of_annot tannot in
       let vs = find_vs env val_specs f in
       (* The (updated) environment is used later by fix_eff_exp to look up
          the actual effects of a function call *)
       let env = Env.update_val_spec f vs env in
       E_aux (exp, (l, mk_tannot env typ (union_effects eff (eff_of_vs vs))))
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
         (* TODO We currently expand type synonyms here to make life easier
            for the Lem pretty-printer later on, as it currently does not have
            access to the environment when printing val specs (and unexpanded
            type synonyms nested in existentials might cause problems).
            A more robust solution would be to make the (global) environment
            more easily available to the pretty-printer. *)
         let args_t' = List.map (Env.expand_synonyms (env_of exp)) args_t in
         let ret_t' = Env.expand_synonyms (env_of exp) ret_t in
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
    let recopt =
      match recopt with
      | Rec_aux ((Rec_rec | Rec_measure _), _) -> recopt
      | _ when List.exists is_funcl_rec funcls ->
         Rec_aux (Rec_rec, Parse_ast.Unknown)
      | _ -> recopt
    in
    let tannotopt = match tannotopt, funcls with
    | Typ_annot_opt_aux (Typ_annot_opt_some (typq, typ), l),
      FCL_aux (FCL_Funcl (_, Pat_aux ((Pat_exp (_, exp) | Pat_when (_, _, exp)), _)), _) :: _ ->
       Typ_annot_opt_aux (Typ_annot_opt_some (typq, Env.expand_synonyms (env_of exp) typ), l)
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

let rewrite_type_union_typs rw_typ (Tu_aux (Tu_ty_id (typ, id), annot)) =
  Tu_aux (Tu_ty_id (rw_typ typ, id), annot)

let rewrite_type_def_typs rw_typ rw_typquant (TD_aux (td, annot)) =
  match td with
  | TD_abbrev (id, typq, A_aux (A_typ typ, l)) ->
     TD_aux (TD_abbrev (id, rw_typquant typq, A_aux (A_typ (rw_typ typ), l)), annot)
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
  | DEC_config (id, typ, exp) -> DEC_aux (DEC_config (id, rw_typ typ, exp), annot)
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

let rewrite_undefined_if_gen always_bitvector defs =
  if !Initial_check.opt_undefined_gen
  then rewrite_undefined (always_bitvector || !Pretty_print_lem.opt_mwords) defs
  else defs

let rec simple_typ (Typ_aux (typ_aux, l) as typ) = Typ_aux (simple_typ_aux typ_aux, l)
and simple_typ_aux = function
  | Typ_id id -> Typ_id id
  | Typ_app (id, [_; _; A_aux (A_typ typ, l)]) when Id.compare id (mk_id "vector") = 0 ->
     Typ_app (mk_id "list", [A_aux (A_typ (simple_typ typ), l)])
  | Typ_app (id, [_]) when Id.compare id (mk_id "atom") = 0 ->
     Typ_id (mk_id "int")
  | Typ_app (id, [_; _]) when Id.compare id (mk_id "range") = 0 ->
     Typ_id (mk_id "int")
  | Typ_app (id, args) -> Typ_app (id, List.concat (List.map simple_typ_arg args))
  | Typ_fn (arg_typs, ret_typ, effs) -> Typ_fn (List.map simple_typ arg_typs, simple_typ ret_typ, effs)
  | Typ_tup typs -> Typ_tup (List.map simple_typ typs)
  | Typ_exist (_, _, Typ_aux (typ, l)) -> simple_typ_aux typ
  | typ_aux -> typ_aux
and simple_typ_arg (A_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | A_typ typ -> [A_aux (A_typ (simple_typ typ), l)]
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
    | DEF_type td -> DEF_type (rewrite_type_def_typs simple_typ simple_typquant td)
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

let rewrite_vector_concat_assignments defs =
  let assign_tuple e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (LEXP_aux (LEXP_vector_concat lexps, lannot), exp) ->
       let typ = Env.base_typ_of env (typ_of exp) in
       if is_vector_typ typ then
         (* let _ = Pretty_print_common.print stderr (Pretty_print_sail.doc_exp (E_aux (e_aux, annot))) in *)
         let start = vector_start_index typ in
         let (_, ord, etyp) = vector_typ_args_of typ in
         let len (LEXP_aux (le, lannot)) =
           let ltyp = Env.base_typ_of env (typ_of_annot lannot) in
           if is_vector_typ ltyp then
             let (len, _, _) = vector_typ_args_of ltyp in
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
             raise (Reporting.err_typ l (Type_error.string_of_type_error err))
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
       let letbind = mk_letbind (mk_pat (P_typ (Type_check.typ_of exp,
                                                mk_pat (P_tup (List.map (fun id -> mk_pat (P_id id)) ids)))))
                                (strip_exp exp)
       in
       let let_exp = mk_exp (E_let (letbind, block)) in
       begin
         try check_exp env let_exp unit_typ with
         | Type_error (l, err) ->
           raise (Reporting.err_typ l (Type_error.string_of_type_error err))
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
    fix_eff_exp (annot_exp e_aux l env (typ_of body)) in

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
  match destruct_tannot annot with
  | Some (env, typ, eff) when is_unit_typ typ ->
     let body = body (annot_exp (E_lit (mk_lit L_unit)) l env unit_typ) in
     let body_typ = try typ_of body with _ -> unit_typ in
     let wild = add_p_typ (typ_of v) (annot_pat P_wild l env (typ_of v)) in
     let lb = fix_eff_lb (annot_letbind (unaux_pat wild, v) l env unit_typ) in
     fix_eff_exp (annot_exp (E_let (lb, body)) l env body_typ)
  | Some (env, typ, eff) ->
     let id = fresh_id "w__" l in
     let pat = add_p_typ (typ_of v) (annot_pat (P_id id) l env (typ_of v)) in
     let lb = fix_eff_lb (annot_letbind (unaux_pat pat, v) l env typ) in
     let body = body (annot_exp (E_id id) l env typ) in
     fix_eff_exp (annot_exp (E_let (lb, body)) l env (typ_of body))
  | None ->
     raise (Reporting.err_unreachable l __POS__ "no type information")


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
  and value_fexps fexps =
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
       n_exp_name exp (fun exp ->
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
    | LEXP_vector_concat es ->
       n_lexpL es (fun es ->
       k (fix_eff_lexp (LEXP_aux (LEXP_vector_concat es,annot))))
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
        let exp = add_e_cast (typ_of exp) exp in
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
    | E_app (op_bool, [l; r])
      when string_of_id op_bool = "and_bool" || string_of_id op_bool = "or_bool" ->
       (* Leave effectful operands of Boolean "and"/"or" in place to allow
          short-circuiting. *)
       let newreturn = effectful l || effectful r in
       let l = n_exp_term newreturn l in
       let r = n_exp_term newreturn r in
       k (rewrap (E_app (op_bool, [l; r])))
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
       n_fexpL fexps (fun fexps ->
       k (rewrap (E_record fexps)))
    | E_record_update (exp1,fexps) ->
       n_exp_name exp1 (fun exp1 ->
       n_fexpL fexps (fun fexps ->
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
       let exp1 = n_exp_term newreturn exp1 in
       n_pexpL newreturn pexps (fun pexps ->
       k (rewrap (E_try (exp1,pexps))))
    | E_let (lb,body) ->
       n_lb lb (fun lb ->
       rewrap (E_let (lb,n_exp body k)))
    | E_sizeof nexp ->
       k (rewrap (E_sizeof nexp))
    | E_constraint nc ->
       k (rewrap (E_constraint nc))
    | E_assign (lexp,exp1) ->
       n_lexp lexp (fun lexp ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_assign (lexp,exp1)))))
    | E_exit exp' -> k (E_aux (E_exit (n_exp_term (effectful exp') exp'),annot))
    | E_assert (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_assert (exp1,exp2)))))
    | E_var (lexp,exp1,exp2) ->
       n_lexp lexp (fun lexp ->
       n_exp exp1 (fun exp1 ->
       rewrap (E_var (lexp,exp1,n_exp exp2 k))))
    | E_internal_return exp1 ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_internal_return exp1)))
    | E_internal_value v ->
       k (rewrap (E_internal_value v))
    | E_return exp' ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_return exp')))
    | E_throw exp' ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_throw exp')))
    | E_internal_plet _ -> failwith "E_internal_plet should not be here yet" in

  let rewrite_fun _ (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),fdannot)) =
    (* let propagate_funcl_effect (FCL_aux (FCL_Funcl(id, pexp), (l, a))) =
      let pexp, eff = propagate_pexp_effect pexp in
      FCL_aux (FCL_Funcl(id, pexp), (l, add_effect_annot a eff))
    in
    let funcls = List.map propagate_funcl_effect funcls in *)
    let effectful_funcl (FCL_aux (FCL_Funcl(_, pexp), _)) = effectful_pexp pexp in
    let newreturn = List.exists effectful_funcl funcls in
    let rewrite_funcl (FCL_aux (FCL_Funcl(id,pexp),annot)) =
      let _ = reset_fresh_name_counter () in
      FCL_aux (FCL_Funcl (id,n_pexp newreturn pexp (fun x -> x)),annot)
    in
    FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),fdannot)
  in
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
    | d -> d
  in
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
    | _ -> raise (Reporting.err_unreachable l __POS__ "unexpected local lexp") in

  let e_let (lb,body) =
    match lb with
    | LB_aux (LB_val (P_aux ((P_wild | P_typ (_, P_aux (P_wild, _))), _),
      E_aux (E_assign ((LEXP_aux (_, annot) as le), exp), (l, _))), _)
      when lexp_is_local le (env_of_annot annot) && not (lexp_is_effectful le) ->
       (* Rewrite assignments to local variables into let bindings *)
       let (lhs, rhs) = rewrite_lexp_to_rhs le in
       let (LEXP_aux (_, lannot)) = lhs in
       let ltyp = typ_of_annot lannot in
       let rhs = add_e_cast ltyp (rhs exp) in
       E_let (LB_aux (LB_val (pat_of_local_lexp lhs, rhs), annot), body)
    | LB_aux (LB_val (pat,exp'),annot') ->
       if effectful exp'
       then E_internal_plet (pat,exp',body)
       else E_let (lb,body) in

  let e_var = fun (lexp,exp1,exp2) ->
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

  let alg = { id_exp_alg with e_let = e_let; e_var = e_var } in
  rewrite_defs_base
    { rewrite_exp = (fun _ exp -> fold_exp alg (propagate_exp_effect exp))
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let fold_guards guards =
  match guards with
  | [] -> (mk_exp (E_lit (mk_lit L_true)))
  | g :: gs -> List.fold_left (fun g g' -> mk_exp (E_app (mk_id "and_bool", [strip_exp g; strip_exp g']))) g gs

let fold_typed_guards env guards =
  match guards with
  | [] -> annot_exp (E_lit (mk_lit L_true)) Parse_ast.Unknown env bool_typ
  | g :: gs -> List.fold_left (fun g g' -> annot_exp (E_app (mk_id "and_bool", [g; g'])) Parse_ast.Unknown env bool_typ) g gs


let rewrite_pexp_with_guards rewrite_pat (Pat_aux (pexp_aux, (annot: tannot annot)) as pexp) =
  let guards = ref [] in

  match pexp_aux with
  | Pat_exp (pat, exp) ->
     begin
       let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat guards } pat in
       match !guards with
       | [] -> pexp
       | gs ->
          let unchecked_pexp = mk_pexp (Pat_when (strip_pat pat, List.map strip_exp gs |> fold_guards, strip_exp exp)) in
          check_case (env_of_pat pat) (typ_of_pat pat) unchecked_pexp (typ_of exp)
     end
  | Pat_when (pat, guard, exp) ->
     begin
       let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat guards } pat in
       let unchecked_pexp = mk_pexp (Pat_when (strip_pat pat, List.map strip_exp !guards |> fold_guards, strip_exp exp)) in
       check_case (env_of_pat pat) (typ_of_pat pat) unchecked_pexp (typ_of exp)
     end


let pexp_rewriters rewrite_pexp =
  let alg = { id_exp_alg with pat_aux = (fun (pexp_aux, annot) -> rewrite_pexp (Pat_aux (pexp_aux, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) }


let stringappend_counter = ref 0

let fresh_stringappend_id () =
  let id = mk_id ("_s" ^ (string_of_int !stringappend_counter) ^ "#") in
  stringappend_counter := !stringappend_counter + 1;
  id

let unk = Parse_ast.Unknown
let unkt = (Parse_ast.Unknown, empty_tannot)

let construct_bool_match env (match_on : tannot exp) (pexp : tannot pexp) : tannot exp =
  let true_exp = annot_exp (E_lit (mk_lit L_true)) unk env bool_typ in
  let false_exp = annot_exp (E_lit (mk_lit L_false)) unk env bool_typ in
    let true_pexp =
      match pexp with
      | Pat_aux (Pat_exp (pat, exp), annot) ->
         Pat_aux (Pat_exp (pat, true_exp), unkt)
      | Pat_aux (Pat_when (pat, guards, exp), annot) ->
         Pat_aux (Pat_when (pat, guards, true_exp), unkt)
    in
    let false_pexp = Pat_aux (Pat_exp (annot_pat P_wild unk env (typ_of match_on), false_exp), unkt) in
    annot_exp (E_case (match_on, [true_pexp; false_pexp])) unk env bool_typ

let rec bindings_of_pat (P_aux (p_aux, p_annot) as pat) =
  match p_aux with
  | P_lit _ | P_wild -> []
  | P_id id -> [pat]
  | P_record _ -> failwith "record patterns not yet implemented"
  (* we assume the type-checker has already checked the two sides have the same bindings *)
  | P_or (left, right) -> bindings_of_pat left
  | P_as (p, id) -> [annot_pat (P_id id) unk (env_of_pat p) (typ_of_pat p)]
  | P_cons (left, right) -> bindings_of_pat left @ bindings_of_pat right
  (* todo: is this right for negated patterns? *)
  | P_not p
    | P_typ (_, p)
    | P_var (p, _) -> bindings_of_pat p
  | P_app (_, ps)
    | P_vector ps
    | P_vector_concat ps
    | P_tup ps
    | P_list ps
    | P_string_append ps -> List.map bindings_of_pat ps |> List.flatten

let rec binding_typs_of_pat (P_aux (p_aux, p_annot) as pat) =
  match p_aux with
  | P_lit _ | P_wild -> []
  | P_id id -> [typ_of_pat pat]
  | P_record _ -> failwith "record patterns not yet implemented"
  (* we assume the type-checker has already checked the two sides have the same bindings *)
  | P_or (left, right) -> binding_typs_of_pat left
  | P_as (p, id) -> [typ_of_pat p]
  | P_cons (left, right) -> binding_typs_of_pat left @ binding_typs_of_pat right
  (* todo: is this right for negated patterns? *)
  | P_not p
    | P_typ (_, p)
    | P_var (p, _) -> binding_typs_of_pat p
  | P_app (_, ps)
    | P_vector ps
    | P_vector_concat ps
    | P_tup ps
    | P_list ps
    | P_string_append ps -> List.map binding_typs_of_pat ps |> List.flatten

let construct_toplevel_string_append_call env f_id bindings binding_typs guard expr =
  (* s# if match f#(s#) { Some (bindings) => guard, _ => false) } => let Some(bindings) = f#(s#) in expr *)
  let s_id = fresh_stringappend_id () in
  let option_typ = app_typ (mk_id "option") [A_aux (A_typ (match binding_typs with
                                                                         | [] -> unit_typ
                                                                         | [typ] -> typ
                                                                         | typs -> tuple_typ typs
                                                              ), unk)]
  in
  let bindings = if bindings = [] then
                   [annot_pat (P_lit (mk_lit L_unit)) unk env unit_typ]
                 else
                   bindings
  in
  let new_pat = annot_pat (P_id s_id) unk env string_typ in
  let new_guard = annot_exp (
                      E_case (annot_exp (E_app (f_id, [annot_exp (E_id s_id) unk env string_typ])) unk env option_typ,
                              [
                                Pat_aux (Pat_exp (annot_pat (P_app (mk_id "Some", bindings)) unk env option_typ, guard), unkt);
                                Pat_aux (Pat_exp (annot_pat P_wild unk env option_typ, annot_exp (E_lit (mk_lit L_false)) unk env bool_typ), unkt)
                              ]
                        )
                    ) unk env bool_typ in
  let new_letbind = annot_letbind (P_app (mk_id "Some", bindings), annot_exp (E_app (f_id, [annot_exp (E_id s_id) unk env string_typ])) unk env option_typ) unk env option_typ in
  let new_expr = annot_exp (E_let (new_letbind, expr)) unk env (typ_of expr) in
  (new_pat, [new_guard], new_expr)

let construct_toplevel_string_append_func env f_id pat =
  let binding_typs = binding_typs_of_pat pat in
  let bindings = bindings_of_pat pat in
  let bindings = if bindings = [] then
                   [annot_pat (P_lit (mk_lit L_unit)) unk env unit_typ]
                 else
                   bindings
  in
  let option_typ = app_typ (mk_id "option") [A_aux (A_typ (match binding_typs with
                                                                       | [] -> unit_typ
                                                                       | [typ] -> typ
                                                                       | typs -> tuple_typ typs
                                                            ), unk)]
  in
  let fun_typ = (mk_typ (Typ_fn ([string_typ], option_typ, no_effect))) in
  let new_val_spec = VS_aux (VS_val_spec (mk_typschm (TypQ_aux (TypQ_no_forall, unk)) fun_typ, f_id, (fun _ -> None), false), unkt) in
  let new_val_spec, env = Type_check.check_val_spec env new_val_spec in
  let non_rec = (Rec_aux (Rec_nonrec, Parse_ast.Unknown)) in
  let no_tannot = (Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown)) in
  let effect_pure = (Effect_opt_aux (Effect_opt_pure, Parse_ast.Unknown)) in
  let s_id = fresh_stringappend_id () in
  let arg_pat = mk_pat (P_id s_id) in
  (* We can ignore guards here because we've already removed them *)
  let rec rewrite_pat env (pat, guards, expr) =
    match pat with
      (* "lit" ^ pat2 ^ ... ^ patn => Some(...) ---> s# if startswith(s#, "lit") => match string_drop(s#, strlen("lit")) {
                                                                                      pat2 => Some(...)
                                                                                      _ => None()
                                                                                    }
       *)
    | P_aux (P_string_append (
                 P_aux (P_lit (L_aux (L_string s, _) as lit), _)
                 :: pats
               ), psa_annot) ->
       let s_id = fresh_stringappend_id () in
       let drop_exp = annot_exp (E_app (mk_id "string_drop", [annot_exp (E_id s_id) unk env string_typ; annot_exp (E_app (mk_id "string_length", [annot_exp (E_lit lit) unk env string_typ])) unk env nat_typ])) unk env string_typ in
       (* recurse into pat2 .. patn *)
       let new_pat2_pexp =
         match rewrite_pat env (P_aux (P_string_append pats, psa_annot), guards, expr) with
         | pat, [], expr -> Pat_aux (Pat_exp (pat, expr), unkt)
         | pat, gs, expr -> Pat_aux (Pat_when (pat, fold_typed_guards env gs, expr), unkt)
       in
       let new_guard = annot_exp (E_app (mk_id "string_startswith", [annot_exp (E_id s_id) unk env string_typ;
                                                                     annot_exp (E_lit lit) unk env string_typ]
                         )) unk env bool_typ in
       let new_wildcard = Pat_aux (Pat_exp (annot_pat P_wild unk env string_typ, annot_exp (E_app (mk_id "None", [annot_exp (E_lit (mk_lit L_unit)) unk env unit_typ])) unk env option_typ), unkt) in
       let new_expr = annot_exp (E_case (drop_exp, [new_pat2_pexp; new_wildcard])) unk env (typ_of expr) in
       (annot_pat (P_id s_id) unk env string_typ, [new_guard], new_expr)
    (* mapping(x) ^ pat2 ^ .. ^ patn => Some(...) ---> s# => match map_matches_prefix(s#) {
                                                               Some(x, n#) => match string_drop(s#, n#) {
                                                                                pat2 ^ .. ^ patn => Some(...)
                                                                                _ => None()
                                                                              }
                                                             }
     *)
    | P_aux (P_string_append (
                 P_aux (P_app (mapping_id, arg_pats) , _)
                 :: pats
               ), psa_annot)
         when Env.is_mapping mapping_id env ->
       (* common things *)
       let mapping_prefix_func =
         match mapping_id with
         | Id_aux (Id id, _)
         | Id_aux (DeIid id, _) -> id ^ "_matches_prefix"
       in
       let mapping_inner_typ =
         match Env.get_val_spec (mk_id mapping_prefix_func) env with
         | (_, Typ_aux (Typ_fn (_, Typ_aux (Typ_app (_, [A_aux (A_typ typ, _)]), _), _), _)) -> typ
         | _ -> typ_error Parse_ast.Unknown "mapping prefix func without correct function type?"
       in

       let s_id = fresh_stringappend_id () in
       let len_id = fresh_stringappend_id () in

       (* construct drop expression -- string_drop(s#, len#) *)
       let drop_exp = annot_exp (E_app (mk_id "string_drop",
                                        [annot_exp (E_id s_id) unk env string_typ;
                                         annot_exp (E_id len_id) unk env nat_typ]))
                        unk env string_typ in
       (* construct func expression -- maybe_atoi s# *)
       let func_exp = annot_exp (E_app (mk_id mapping_prefix_func,
                                        [annot_exp (E_id s_id) unk env string_typ]))
                        unk env mapping_inner_typ in
       (* construct some pattern -- Some (n#, len#) *)
       let opt_typ = app_typ (mk_id "option") [A_aux (A_typ mapping_inner_typ, unk)] in
       let tup_arg_pat = match arg_pats with
         | [] -> assert false
         | [arg_pat] -> arg_pat
         | arg_pats -> annot_pat (P_tup arg_pats) unk env (tuple_typ (List.map typ_of_pat arg_pats))
       in

       let some_pat = annot_pat (P_app (mk_id "Some",
                                        [tup_arg_pat;
                                         annot_pat (P_id len_id) unk env nat_typ]))
                        unk env opt_typ in
       let some_pat, some_pat_env, _ = bind_pat env (strip_pat some_pat) opt_typ in

       (* need to add the Some(...) env to tup_arg_pats for pat_to_exp below as it calls the typechecker *)
       let tup_arg_pat = map_pat_annot (fun (l, tannot) -> (l, replace_env some_pat_env tannot)) tup_arg_pat in

       let new_wildcard = Pat_aux (Pat_exp (annot_pat P_wild unk env string_typ, annot_exp (E_app (mk_id "None", [annot_exp (E_lit (mk_lit L_unit)) unk env unit_typ])) unk env option_typ), unkt) in

       (* recurse into pat2 .. patn *)
       let new_pat2_pexp =
         match rewrite_pat env (P_aux (P_string_append (pats), psa_annot), guards, expr) with
         | pat, [], expr -> Pat_aux (Pat_exp (pat, expr), unkt)
         | pat, gs, expr -> Pat_aux (Pat_when (pat, fold_typed_guards env gs, expr), unkt)
       in

       let inner_match = annot_exp (E_case (drop_exp, [new_pat2_pexp; new_wildcard])) unk env option_typ in

       let outer_match = annot_exp (E_case (func_exp, [Pat_aux (Pat_exp (some_pat, inner_match), unkt); new_wildcard])) unk env option_typ in

       (annot_pat (P_id s_id) unk env string_typ, [], outer_match)
    | _ -> (pat, guards, expr)
  in
  let new_pat, new_guards, new_expr = rewrite_pat env (pat, [], annot_exp (E_app (mk_id "Some", List.map (fun p -> pat_to_exp p) bindings)) unk env option_typ) in
  let new_pexp = match new_guards with
    | [] -> Pat_aux (Pat_exp (new_pat, new_expr), unkt)
    | gs -> Pat_aux (Pat_when (new_pat, fold_typed_guards env gs, new_expr), unkt)
  in
  let wildcard = mk_pexp (Pat_exp (mk_pat P_wild, mk_exp (E_app (mk_id "None", [mk_lit_exp L_unit])))) in
  let new_match = mk_exp (E_case (mk_exp (E_id s_id), [strip_pexp new_pexp; wildcard])) in
  let new_fun_def = FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl f_id arg_pat new_match]), (unk,())) in
  let new_fun_def, env = Type_check.check_fundef env new_fun_def in
  List.flatten [new_val_spec; new_fun_def]

let rewrite_defs_toplevel_string_append (Defs defs) =
  let new_defs = ref ([] : tannot def list) in
  let rec rewrite_pexp (Pat_aux (pexp_aux, pexp_annot) as pexp) =
    (* merge cases of Pat_exp and Pat_when *)
    let (P_aux (p_aux, p_annot) as pat, guards, expr) =
      match pexp_aux with
      | Pat_exp (pat, expr) -> (pat, [], expr)
      | Pat_when (pat, guard, expr) -> (pat, [guard], expr)
    in

    let env = env_of_annot p_annot in

    let (new_pat, new_guards, new_expr) =
      match pat with
      | P_aux (P_string_append appends, psa_annot) ->
         let f_id = fresh_stringappend_id () in
         new_defs := (construct_toplevel_string_append_func env f_id pat) @ !new_defs;
         construct_toplevel_string_append_call env f_id (bindings_of_pat pat) (binding_typs_of_pat pat) (fold_typed_guards env guards) expr
      | _ -> (pat, guards, expr)
    in

    (* un-merge Pat_exp and Pat_when cases *)
    let new_pexp = match new_guards with
      | [] -> Pat_aux (Pat_exp (new_pat, new_expr), pexp_annot)
      | gs -> Pat_aux (Pat_when (new_pat, fold_typed_guards env gs, new_expr), pexp_annot)
    in
    new_pexp
  in
  let rewrite def =
    new_defs := [];
    let alg = { id_exp_alg with pat_aux = (fun (pexp_aux, annot) -> rewrite_pexp (Pat_aux (pexp_aux, annot))) } in
    let rewritten = rewrite_def { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) } def in
    !new_defs @ [rewritten]
  in
  Defs (List.map rewrite defs |> List.flatten)


let rec rewrite_defs_pat_string_append =
  let rec rewrite_pat env ((pat : tannot pat), (guards : tannot exp list), (expr : tannot exp)) =
    let guards_ref = ref guards in
    let expr_ref = ref expr in
    let folder p =
      let p, g, e = rewrite_pat env (p, !guards_ref, !expr_ref) in
      guards_ref := g;
      expr_ref := e;
      p
    in
    match pat with
    (*
        "lit" ^^ pat2 => expr ---> s# if startswith(s#, "lit")
                                        && match str_drop(s#, strlen("lit")) {
                                             pat2 => true, _ => false
                                           }
                                   => match str_drop(s#, strlen("lit")) {
                                        pat2 => expr
                                      }
     *)
    | P_aux (P_string_append (
                 P_aux (P_lit (L_aux (L_string s, _) as lit), _)
                 :: pats
               ), psa_annot) ->

       let id = fresh_stringappend_id () in

       (* construct drop expression -- string_drop(s#, strlen("lit")) *)
       let drop_exp = annot_exp (E_app (mk_id "string_drop", [annot_exp (E_id id) unk env string_typ; annot_exp (E_app (mk_id "string_length", [annot_exp (E_lit lit) unk env string_typ])) unk env nat_typ])) unk env string_typ  in

       (* recurse into pat2 *)
       let new_pat2_pexp =
         match rewrite_pat env (P_aux (P_string_append (pats), psa_annot), guards, expr) with
         | pat, [], expr -> Pat_aux (Pat_exp (pat, expr), unkt)
         | pat, gs, expr -> Pat_aux (Pat_when (pat, fold_typed_guards env gs, expr), unkt)
       in

       (* construct the two new guards *)
       let guard1 = annot_exp (E_app (mk_id "string_startswith",
                                      [annot_exp (E_id id) unk env string_typ;
                                       annot_exp (E_lit lit) unk env string_typ]
                      )) unk env bool_typ in
       let guard2 = construct_bool_match env drop_exp new_pat2_pexp in

       (* construct new match expr *)
       let new_expr = annot_exp (E_case (drop_exp, [new_pat2_pexp])) unk env (typ_of expr) in

       (* construct final result *)
       annot_pat (P_id id) unk env string_typ, [guard1; guard2], new_expr

    (*
        (builtin x) ^^ pat2 => expr ---> s# if match maybe_atoi s# {
                                                 Some (n#, len#) =>
                                                   match string_drop(s#, len#) {
                                                     pat2 => true, _ => false
                                                   }
                                                 None => false
                                               }
                                         => let (x, len#) = match maybe_int_of_prefix s# {
                                                              Some (x, len#) => (x, len#)
                                                            } in
                                            match string_drop(s#, len#) {
                                              pat2 => expr
                                            }
     *)

    | P_aux (P_string_append (
                 P_aux (P_app (mapping_id, arg_pats) , _)
                 :: pats
               ), psa_annot)
         when Env.is_mapping mapping_id env ->
       (* common things *)
       let mapping_prefix_func =
         match mapping_id with
         | Id_aux (Id id, _)
         | Id_aux (DeIid id, _) -> id ^ "_matches_prefix"
       in
       let mapping_inner_typ =
         match Env.get_val_spec (mk_id mapping_prefix_func) env with
         | (_, Typ_aux (Typ_fn (_, Typ_aux (Typ_app (_, [A_aux (A_typ typ, _)]), _), _), _)) -> typ
         | _ -> typ_error Parse_ast.Unknown "mapping prefix func without correct function type?"
       in

       let s_id = fresh_stringappend_id () in
       let len_id = fresh_stringappend_id () in

       (* construct drop expression -- string_drop(s#, len#) *)
       let drop_exp = annot_exp (E_app (mk_id "string_drop",
                                        [annot_exp (E_id s_id) unk env string_typ;
                                         annot_exp (E_id len_id) unk env nat_typ]))
                        unk env string_typ in
       (* construct func expression -- maybe_atoi s# *)
       let func_exp = annot_exp (E_app (mk_id mapping_prefix_func,
                                        [annot_exp (E_id s_id) unk env string_typ]))
                        unk env mapping_inner_typ in
       (* construct some pattern -- Some (n#, len#) *)
       let opt_typ = app_typ (mk_id "option") [A_aux (A_typ mapping_inner_typ, unk)] in
       let tup_arg_pat = match arg_pats with
         | [] -> assert false
         | [arg_pat] -> arg_pat
         | arg_pats -> annot_pat (P_tup arg_pats) unk env (tuple_typ (List.map typ_of_pat arg_pats))
       in

       let some_pat = annot_pat (P_app (mk_id "Some",
                                        [tup_arg_pat;
                                         annot_pat (P_id len_id) unk env nat_typ]))
                        unk env opt_typ in
       let some_pat, some_pat_env, _ = bind_pat env (strip_pat some_pat) opt_typ in

       (* need to add the Some(...) env to tup_arg_pats for pat_to_exp below as it calls the typechecker *)
       let tup_arg_pat = map_pat_annot (fun (l, tannot) -> (l, replace_env some_pat_env tannot)) tup_arg_pat in

       (* construct None pattern *)
       let none_pat = annot_pat P_wild unk env opt_typ in

       (* recurse into pat2 *)
       let new_pat2_pexp =
         match rewrite_pat env (P_aux (P_string_append (pats), psa_annot), guards, expr) with
         | pat, [], expr -> Pat_aux (Pat_exp (pat, expr), unkt)
         | pat, gs, expr -> Pat_aux (Pat_when (pat, fold_typed_guards env gs, expr), unkt)
       in

       (* construct the new guard *)
       let guard_inner_match = construct_bool_match env drop_exp new_pat2_pexp in
       let new_guard = annot_exp (E_case (func_exp, [
                                     Pat_aux (Pat_exp (some_pat, guard_inner_match), unkt);
                                     Pat_aux (Pat_exp (none_pat, annot_exp (E_lit (mk_lit (L_false))) unk env bool_typ), unkt)
                         ])) unk env bool_typ in

       (* construct the new match *)
       let new_match = annot_exp (E_case (drop_exp, [new_pat2_pexp])) unk env (typ_of expr) in

       (* construct the new let *)
       let new_binding = annot_exp (E_cast (mapping_inner_typ,
                                            annot_exp (E_case (func_exp, [
                                                             Pat_aux (Pat_exp (some_pat,
                                                                               annot_exp (E_tuple [
                                                                                           pat_to_exp tup_arg_pat;
                                                                                           annot_exp (E_id len_id) unk env nat_typ
                                                                                 ]) unk env mapping_inner_typ
                                                                        ), unkt)
                                              ])) unk env mapping_inner_typ
                           )) unk env mapping_inner_typ in
       let new_letbind =
         match arg_pats with
         | [] -> assert false
         | [arg_pat] -> annot_letbind
                          (P_tup [arg_pat; annot_pat (P_id len_id) unk env nat_typ], new_binding)
                          unk env (tuple_typ [typ_of_pat arg_pat; nat_typ])
         | arg_pats -> annot_letbind
                         (P_tup
                            [annot_pat (P_tup arg_pats) unk env (tuple_typ (List.map typ_of_pat arg_pats));
                             annot_pat (P_id len_id) unk env nat_typ],
                          new_binding)
                         unk env (tuple_typ [tuple_typ (List.map typ_of_pat arg_pats); nat_typ])
       in
       let new_let = annot_exp (E_let (new_letbind, new_match)) unk env (typ_of expr) in

       (* construct final result *)
       annot_pat (P_id s_id) unk env string_typ,
       [new_guard],
       new_let

    | P_aux (P_string_append [pat], _) ->
       pat, guards, expr

    | P_aux (P_string_append [], (l, _)) ->
       annot_pat (P_lit (L_aux (L_string "", l))) l env string_typ, guards, expr

    | P_aux (P_string_append _, _) ->
       failwith ("encountered a variety of string append pattern that is not yet implemented: " ^ string_of_pat pat)

    | P_aux (P_or(pat1, pat2), p_annot) ->
       (* todo: this is wrong - no idea what is happening here *)
       let (pat1', guards1, expr1) = rewrite_pat env (pat1, guards, expr) in
       let (pat2', guards2, expr2) = rewrite_pat env (pat2, guards, expr) in
       (P_aux (P_or(pat1', pat2'), p_annot), guards1 @ guards2, expr2)

    | P_aux (P_not(pat), p_annot) ->
       let (pat', guards, expr) = rewrite_pat env (pat, guards, expr) in
       (P_aux (P_not(pat'), p_annot), guards, expr)

    | P_aux (P_as (inner_pat, inner_id), p_annot) ->
       let inner_pat, guards, expr = rewrite_pat env (inner_pat, guards, expr) in
       P_aux (P_as (inner_pat, inner_id), p_annot), guards, expr
    | P_aux (P_typ (inner_typ, inner_pat), p_annot) ->
       let inner_pat, guards, expr = rewrite_pat env (inner_pat, guards, expr) in
       P_aux (P_typ (inner_typ, inner_pat), p_annot), guards, expr
    | P_aux (P_var (inner_pat, typ_pat), p_annot) ->
       let inner_pat, guards, expr = rewrite_pat env (inner_pat, guards, expr) in
       P_aux (P_var (inner_pat, typ_pat), p_annot), guards, expr
    | P_aux (P_record _, p_annot) ->
       failwith "record patterns not yet implemented"
    | P_aux (P_vector pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_vector pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_vector_concat pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_vector_concat pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_tup pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_tup pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_list pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_list pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_app (f, pats), p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_app (f, pats), p_annot), !guards_ref, !expr_ref
    | P_aux (P_cons (pat1, pat2), p_annot) ->
       let pat1, guards, expr = rewrite_pat env (pat1, guards, expr) in
       let pat2, guards, expr = rewrite_pat env (pat2, guards, expr) in
       P_aux (P_cons (pat1, pat2), p_annot), guards, expr
    | P_aux (P_id _, _)
    | P_aux (P_lit _, _)
    | P_aux (P_wild, _) -> pat, guards, expr
  in

  let rec rewrite_pexp (Pat_aux (pexp_aux, pexp_annot) as pexp) =

    (* merge cases of Pat_exp and Pat_when *)
    let (P_aux (p_aux, p_annot) as pat, guards, expr) =
      match pexp_aux with
      | Pat_exp (pat, expr) -> (pat, [], expr)
      | Pat_when (pat, guard, expr) -> (pat, [guard], expr)
    in

    let env = env_of_annot p_annot in

    let (new_pat, new_guards, new_expr) =
      rewrite_pat env (pat, guards, expr)
    in

    (* un-merge Pat_exp and Pat_when cases *)
    let new_pexp = match new_guards with
    | [] -> Pat_aux (Pat_exp (new_pat, new_expr), pexp_annot)
    | gs -> Pat_aux (Pat_when (new_pat, fold_typed_guards env gs, new_expr), pexp_annot)
    in
    new_pexp

  in
  pexp_rewriters rewrite_pexp


let mappingpatterns_counter = ref 0

let fresh_mappingpatterns_id () =
  let id = mk_id ("_mappingpatterns_" ^ (string_of_int !mappingpatterns_counter) ^ "#") in
  mappingpatterns_counter := !mappingpatterns_counter + 1;
  id

let rewrite_defs_mapping_patterns =
  let rec rewrite_pat env (pat, guards, expr) =
    let guards_ref = ref guards in
    let expr_ref = ref expr in
    let folder p =
      let p, g, e = rewrite_pat env (p, !guards_ref, !expr_ref) in
      guards_ref := g;
      expr_ref := e;
      p
    in
    let env = env_of_pat pat in
    match pat with
      (*
          mapping(args) if g => expr ----> s# if mapping_matches(s#)
                                                 & (if mapping_matches(s#) then let args = mapping(s#) in g)
                                             => let args = mapping(s#) in expr

          (plus 'infer the mapping type' shenanigans)
       *)
    | P_aux (P_app (mapping_id, arg_pats), p_annot) when Env.is_mapping mapping_id env ->

       let mapping_in_typ = typ_of_annot p_annot in

       let x = Env.get_val_spec mapping_id env in
       let (_, Typ_aux(Typ_bidir(typ1, typ2), _)) = x in

       let mapping_direction =
         if mapping_in_typ = typ1 then
           "forwards"
         else
           "backwards"
       in

       let mapping_out_typ =
         if mapping_in_typ = typ2 then
           typ2
         else
           typ1
       in

       let mapping_name =
         match mapping_id with
         | Id_aux (Id id, _)
         | Id_aux (DeIid id, _) -> id
       in

       let mapping_matches_id = mk_id (mapping_name ^ "_" ^ mapping_direction ^ "_matches") in
       let mapping_perform_id = mk_id (mapping_name ^ "_" ^ mapping_direction) in
       let s_id = fresh_mappingpatterns_id () in

       let s_exp = annot_exp (E_id s_id) unk env mapping_in_typ in
       let new_guard = annot_exp (E_app (mapping_matches_id, [s_exp])) unk env bool_typ in
       let new_binding = annot_exp (E_app (mapping_perform_id, [s_exp])) unk env typ2 in
       let new_letbind = match arg_pats with
         | [] -> assert false
         | [arg_pat] -> LB_aux (LB_val (arg_pat, new_binding), unkt)
         | arg_pats ->
            let checked_tup = annot_pat (P_tup arg_pats) unk env mapping_out_typ in
            LB_aux (LB_val (checked_tup, new_binding), unkt)
       in

       let new_let = annot_exp (E_let (new_letbind, expr)) unk env (typ_of expr) in

       let false_exp = annot_exp (E_lit (L_aux (L_false, unk))) unk env bool_typ in
       let new_other_guards = annot_exp (E_if (new_guard,
                                               (annot_exp (E_let (new_letbind, fold_typed_guards env guards)) unk env bool_typ),
                                               false_exp)) unk env bool_typ in

       annot_pat (P_typ (mapping_in_typ, annot_pat (P_id s_id) unk env mapping_in_typ)) unk env mapping_in_typ, [new_guard; new_other_guards], new_let

    | P_aux (P_as (inner_pat, inner_id), p_annot) ->
       let inner_pat, guards, expr = rewrite_pat env (inner_pat, guards, expr) in
       P_aux (P_as (inner_pat, inner_id), p_annot), guards, expr
    | P_aux (P_typ (inner_typ, inner_pat), p_annot) ->
       let inner_pat, guards, expr = rewrite_pat env (inner_pat, guards, expr) in
       P_aux (P_typ (inner_typ, inner_pat), p_annot), guards, expr
    | P_aux (P_var (inner_pat, typ_pat), p_annot) ->
       let inner_pat, guards, expr = rewrite_pat env (inner_pat, guards, expr) in
       P_aux (P_var (inner_pat, typ_pat), p_annot), guards, expr
    | P_aux (P_record _, p_annot) ->
       failwith "record patterns not yet implemented"
    | P_aux (P_vector pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_vector pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_vector_concat pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_vector_concat pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_tup pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_tup pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_list pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_list pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_app (f, pats), p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_app (f, pats), p_annot), !guards_ref, !expr_ref
    | P_aux (P_string_append pats, p_annot) ->
       let pats = List.map folder pats in
       P_aux (P_string_append pats, p_annot), !guards_ref, !expr_ref
    | P_aux (P_cons (pat1, pat2), p_annot) ->
       let pat1, guards, expr = rewrite_pat env (pat1, guards, expr) in
       let pat2, guards, expr = rewrite_pat env (pat2, guards, expr) in
       P_aux (P_cons (pat1, pat2), p_annot), guards, expr
    | P_aux (P_or (pat1, pat2), p_annot) ->
       let pat1, guards, expr = rewrite_pat env (pat1, guards, expr) in
       let pat2, guards, expr = rewrite_pat env (pat2, guards, expr) in
       P_aux (P_or (pat1, pat2), p_annot), guards, expr
    | P_aux (P_not p, p_annot) ->
       let p', guards, expr = rewrite_pat env (p, guards, expr) in
       P_aux (P_not p', p_annot), guards, expr
    | P_aux (P_id _, _)
    | P_aux (P_lit _, _)
    | P_aux (P_wild, _) -> pat, guards, expr
  in

  let rec rewrite_pexp (Pat_aux (pexp_aux, pexp_annot) as pexp) =

    (* merge cases of Pat_exp and Pat_when *)
    let (P_aux (p_aux, p_annot) as pat, guards, expr) =
      match pexp_aux with
      | Pat_exp (pat, expr) -> (pat, [], expr)
      | Pat_when (pat, guard, expr) -> (pat, [guard], expr)
    in

    let env = env_of_annot p_annot in

    let (new_pat, new_guards, new_expr) =
      rewrite_pat env (pat, guards, expr)
    in

    (* un-merge Pat_exp and Pat_when cases *)
    let new_pexp = match new_guards with
    | [] -> Pat_aux (Pat_exp (new_pat, new_expr), pexp_annot)
    | gs -> Pat_aux (Pat_when (new_pat, fold_typed_guards env gs, new_expr), pexp_annot)
    in
    typ_debug (lazy (Printf.sprintf "rewritten pexp: %s\n%!" (Pretty_print_sail.doc_pexp new_pexp |> Pretty_print_sail.to_string)));
    new_pexp

  in
  pexp_rewriters rewrite_pexp

let rewrite_lit_lem (L_aux (lit, _)) = match lit with
  | L_num _ | L_string _ | L_hex _ | L_bin _ | L_real _ -> true
  | _ -> false

let rewrite_no_strings (L_aux (lit, _)) = match lit with
  | L_string _ -> false
  | _ -> true

let rewrite_lit_ocaml (L_aux (lit, _)) = match lit with
  | L_num _ | L_string _ | L_hex _ | L_bin _ | L_real _ | L_unit -> false
  | _ -> true

let rewrite_defs_pat_lits rewrite_lit =
  let rewrite_pexp (Pat_aux (pexp_aux, annot) as pexp) =
    let guards = ref [] in
    let counter = ref 0 in

    let rewrite_pat = function
      (* Matching on unit is always the same as matching on wildcard *)
      | P_lit (L_aux (L_unit, _) as lit), p_annot when rewrite_lit lit ->
         P_aux (P_wild, p_annot)
      | P_lit lit, p_annot when rewrite_lit lit ->
         let env = env_of_annot p_annot in
         let typ = typ_of_annot p_annot in
         let id = mk_id ("p" ^ string_of_int !counter ^ "#") in
         let guard = mk_exp (E_app_infix (mk_exp (E_id id), mk_id "==", mk_exp (E_lit lit))) in
         let guard = check_exp (Env.add_local id (Immutable, typ) env) guard bool_typ in
         guards := guard :: !guards;
         incr counter;
         P_aux (P_id id, p_annot)
      | p_aux, p_annot ->
         P_aux (p_aux, p_annot)
    in

    match pexp_aux with
    | Pat_exp (pat, exp) ->
       begin
         let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat } pat in
         match !guards with
         | [] -> Pat_aux (Pat_exp (pat, exp), annot)
         | (g :: gs) ->
            let guard_annot = (fst annot, mk_tannot (env_of exp) bool_typ no_effect) in
            Pat_aux (Pat_when (pat, List.fold_left (fun g g' -> E_aux (E_app (mk_id "and_bool", [g; g']), guard_annot)) g gs, exp), annot)
       end
    | Pat_when (pat, guard, exp) ->
       begin
         let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat } pat in
         let guard_annot = (fst annot, mk_tannot (env_of exp) bool_typ no_effect) in
         Pat_aux (Pat_when (pat, List.fold_left (fun g g' -> E_aux (E_app (mk_id "and_bool", [g; g']), guard_annot)) guard !guards, exp), annot)
       end
  in

  let alg = { id_exp_alg with pat_aux = (fun (pexp_aux, annot) -> rewrite_pexp (Pat_aux (pexp_aux, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) }


(* Now all expressions have no blocks anymore, any term is a sequence of let-expressions,
 * internal let-expressions, or internal plet-expressions ended by a term that does not
 * access memory or registers and does not update variables *)

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
       let typ = typ_of_pat pat in
       add_p_typ typ pat
    | pats ->
       let typ = tuple_typ (List.map typ_of_pat pats) in
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
         let lb = LB_aux (LB_val (P_aux (P_wild, annot), exp), annot) in
         let exp' = tuple_exp vars in
         E_aux (E_let (lb, exp'), swaptyp (typ_of exp') annot)
       else tuple_exp (exp :: vars) in

  let mk_var_exps_pats l env ids =
    ids
    |> IdSet.elements
    |> List.map
        (fun id ->
          let (E_aux (_, a) as exp) = infer_exp env (E_aux (E_id id, (l, ()))) in
          exp, P_aux (P_id id, a))
    |> List.split in

  let rewrite used_vars (E_aux (expaux,((el,_) as annot)) as full_exp) (P_aux (paux,(pl,pannot)) as pat) =
    let env = env_of_annot annot in
    let overwrite = match paux with
      | P_wild | P_typ (_, P_aux (P_wild, _)) -> true
      | _ -> false in
    match expaux with
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
       (* Translate for loops into calls to one of the foreach combinators.
          The loop body becomes a function of the loop variable and any
          mutable local variables that are updated inside the loop and
          are used after or within the loop.
          Since the foreach* combinators are higher-order functions,
          they cannot be represented faithfully in the AST. The following
          code abuses the parameters of an E_app node, embedding the loop body
          function as an expression followed by the list of variables it
          expects. In (Lem) pretty-printing, this turned into an anonymous
          function and passed to foreach*. *)
       let vars, varpats =
         find_updated_vars exp4
         |> IdSet.inter (IdSet.union used_vars (find_used_vars full_exp))
         |> mk_var_exps_pats pl env
       in
       let exp4 = rewrite_var_updates (add_vars overwrite exp4 vars) in
       let ord_exp, kids, constr, lower, upper, lower_exp, upper_exp =
         match destruct_numeric (Env.expand_synonyms env (typ_of exp1)), destruct_numeric (Env.expand_synonyms env (typ_of exp2)) with
           | None, _ | _, None ->
              raise (Reporting.err_unreachable el __POS__ "Could not determine loop bounds")
           | Some (kids1, constr1, n1), Some (kids2, constr2, n2) ->
              let kids = kids1 @ kids2 in
              let constr = nc_and constr1 constr2 in
              let ord_exp, lower, upper, lower_exp, upper_exp =
                if is_order_inc order
                then (annot_exp (E_lit (mk_lit L_true)) el env bool_typ, n1, n2, exp1, exp2)
                else (annot_exp (E_lit (mk_lit L_false)) el env bool_typ, n2, n1, exp2, exp1)
              in
              ord_exp, kids, constr, lower, upper, lower_exp, upper_exp
       in
       (* Bind the loop variable in the body, annotated with constraints *)
       let lvar_kid = mk_kid ("loop_" ^ string_of_id id) in
       let lvar_nc = nc_and constr (nc_and (nc_lteq lower (nvar lvar_kid)) (nc_lteq (nvar lvar_kid) upper)) in
       let lvar_typ = mk_typ (Typ_exist (List.map (mk_kopt K_int) (lvar_kid :: kids), lvar_nc, atom_typ (nvar lvar_kid))) in
       let lvar_pat = unaux_pat (add_p_typ lvar_typ (annot_pat (P_var (
         annot_pat (P_id id) el env (atom_typ (nvar lvar_kid)),
         TP_aux (TP_var lvar_kid, gen_loc el))) el env lvar_typ)) in
       let lb = fix_eff_lb (annot_letbind (lvar_pat, exp1) el env lvar_typ) in
       let body = fix_eff_exp (annot_exp (E_let (lb, exp4)) el env (typ_of exp4)) in
       (* If lower > upper, the loop body never gets executed, and the type
          checker might not be able to prove that the initial value exp1
          satisfies the constraints on the loop variable.

          Make this explicit by guarding the loop body with lower <= upper.
          (for type-checking; the guard is later removed again by the Lem
          pretty-printer).  This could be implemented with an assertion, but
          that would force the loop to be effectful, so we use an if-expression
          instead.  This code assumes that the loop bounds have (possibly
          existential) atom types, and the loop body has type unit. *)
       let lower_kid = mk_kid ("loop_" ^ string_of_id id ^ "_lower") in
       let lower_pat = P_var (annot_pat P_wild el env (typ_of lower_exp), mk_typ_pat (TP_app (mk_id "atom", [mk_typ_pat (TP_var lower_kid)]))) in
       let lb_lower = annot_letbind (lower_pat, lower_exp) el env (typ_of lower_exp) in
       let upper_kid = mk_kid ("loop_" ^ string_of_id id ^ "_upper") in
       let upper_pat = P_var (annot_pat P_wild el env (typ_of upper_exp), mk_typ_pat (TP_app (mk_id "atom", [mk_typ_pat (TP_var upper_kid)]))) in
       let lb_upper = annot_letbind (upper_pat, upper_exp) el env (typ_of upper_exp) in
       let guard = annot_exp (E_constraint (nc_lteq (nvar lower_kid) (nvar upper_kid))) el env bool_typ in
       let unit_exp = annot_exp (E_lit (mk_lit L_unit)) el env unit_typ in
       let skip_val = tuple_exp (if overwrite then vars else unit_exp :: vars) in
       let guarded_body =
         fix_eff_exp (annot_exp (E_let (lb_lower,
           fix_eff_exp (annot_exp (E_let (lb_upper,
             fix_eff_exp (annot_exp (E_if (guard, body, skip_val))
               el env (typ_of exp4))))
             el env (typ_of exp4))))
           el env (typ_of exp4)) in
       let v = fix_eff_exp (annot_exp (E_app (mk_id "foreach", [exp1; exp2; exp3; ord_exp; tuple_exp vars; guarded_body])) el env (typ_of body)) in
       Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
     | E_loop(loop,cond,body) ->
        (* Find variables that might be updated in the loop body and are used
           either after or within the loop. *)
        let vars, varpats =
          find_updated_vars body
          |> IdSet.inter (IdSet.union used_vars (find_used_vars full_exp))
          |> mk_var_exps_pats pl env
        in
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
         |> IdSet.inter used_vars
         |> mk_var_exps_pats pl env in
       if vars = [] then
         (Same_vars (E_aux (E_if (c,rewrite_var_updates e1,rewrite_var_updates e2),annot)))
       else
         let e1 = rewrite_var_updates (add_vars overwrite e1 vars) in
         let e2 = rewrite_var_updates (add_vars overwrite e2 vars) in
         (* after rewrite_defs_letbind_effects c has no variable updates *)
         let env = env_of_annot annot in
         let typ = typ_of e1 in
         let eff = union_eff_exps [c;e1;e2] in
         let v = E_aux (E_if (c,e1,e2), (gen_loc el, mk_tannot env typ eff)) in
         Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_case (e1,ps) | E_try (e1, ps) ->
       let is_case = match expaux with E_case _ -> true | _ -> false in
       let vars, varpats =
         (* for E_case, e1 needs no rewriting after rewrite_defs_letbind_effects *)
         ((if is_case then [] else [e1]) @
         List.map (fun (Pat_aux ((Pat_exp (_,e)|Pat_when (_,_,e)),_)) -> e) ps)
         |> List.map find_updated_vars
         |> List.fold_left IdSet.union IdSet.empty
         |> IdSet.inter used_vars
         |> mk_var_exps_pats pl env in
       if vars = [] then
         let ps = List.map (function
           | Pat_aux (Pat_exp (p,e),a) ->
             Pat_aux (Pat_exp (p,rewrite_var_updates e),a)
           | Pat_aux (Pat_when (p,g,e),a) ->
             Pat_aux (Pat_when (p,g,rewrite_var_updates e),a)) ps in
         let expaux = if is_case then E_case (e1, ps) else E_try (e1, ps) in
         Same_vars (E_aux (expaux, annot))
       else
         let e1 = if is_case then e1 else rewrite_var_updates (add_vars overwrite e1 vars) in
         let rewrite_pexp (Pat_aux (pexp, (l, _))) = match pexp with
           | Pat_exp (pat, exp) ->
             let exp = rewrite_var_updates (add_vars overwrite exp vars) in
             let pannot = (l, mk_tannot (env_of exp) (typ_of exp) (effect_of exp)) in
             Pat_aux (Pat_exp (pat, exp), pannot)
           | Pat_when _ ->
             raise (Reporting.err_unreachable l __POS__
               "Guarded patterns should have been rewritten already") in
         let ps = List.map rewrite_pexp ps in
         let expaux = if is_case then E_case (e1, ps) else E_try (e1, ps) in
         let typ = match ps with
           | Pat_aux ((Pat_exp (_,first)|Pat_when (_,_,first)),_) :: _ -> typ_of first
           | _ -> unit_typ in
         let v = fix_eff_exp (annot_exp expaux pl env typ) in
         Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_assign (lexp,vexp) ->
       let mk_id_pat id = match Env.lookup_id id env with
         | Local (_, typ) ->
            add_p_typ typ (annot_pat (P_id id) pl env typ)
         | _ ->
            raise (Reporting.err_unreachable pl __POS__
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
     let lb = match rewrite (find_used_vars body) v pat with
       | Added_vars (v, P_aux (pat, _)) ->
          fix_eff_lb (annot_letbind (pat, v) (get_loc_exp v) env (typ_of v))
       | Same_vars v -> fix_eff_lb (LB_aux (LB_val (pat, v),lbannot)) in
     fix_eff_exp (annot_exp (E_let (lb, body)) l env (typ_of body))
  | E_var (lexp,v,body) ->
     (* Rewrite E_var into E_let and call recursively *)
     let paux, typ = match lexp with
       | LEXP_aux (LEXP_id id, _) ->
          P_id id, typ_of v
       | LEXP_aux (LEXP_cast (typ, id), _) ->
          unaux_pat (add_p_typ typ (annot_pat (P_id id) l env (typ_of v))), typ
       | _ ->
         raise (Reporting.err_unreachable l __POS__
           "E_var with a lexp that is not a variable") in
     let lb = fix_eff_lb (annot_letbind (paux, v) l env typ) in
     let exp = fix_eff_exp (annot_exp (E_let (lb, body)) l env (typ_of body)) in
     rewrite_var_updates exp
  | E_for _ | E_loop _ | E_if _ | E_case _ | E_assign _ ->
     let var_id = fresh_id "u__" l in
     let lb = LB_aux (LB_val (P_aux (P_id var_id, annot), exp), annot) in
     let exp' = E_aux (E_let (lb, E_aux (E_id var_id, annot)), annot) in
     rewrite_var_updates exp'
  | E_internal_plet (pat,v,body) ->
     failwith "rewrite_var_updates: E_internal_plet shouldn't be introduced yet"
  (* There are no other expressions that have effects or variable updates in
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
    | Typ_app (Id_aux (Id "reg",_), [A_aux (A_typ (Typ_aux (t_aux2, _)), _)]) ->
      rewrite_t_aux t_aux2
    | Typ_app (name,t_args) -> Typ_app (name,List.map rewrite_t_arg t_args)
    | Typ_fn (arg_typs, ret_typ, eff) -> Typ_fn (List.map rewrite_t arg_typs, rewrite_t ret_typ, eff)
    | Typ_tup ts -> Typ_tup (List.map rewrite_t ts)
    | _ -> t_aux
  and rewrite_t_arg t_arg = match t_arg with
    | A_aux (A_typ t, a) -> A_aux (A_typ (rewrite_t t), a)
    | _ -> t_arg in

  let rec rewrite_annot (l, tannot) =
    match destruct_tannot tannot with
    | None -> l, empty_tannot
    | Some (_, typ, _) -> l, replace_typ (rewrite_t typ) tannot in

  map_exp_annot rewrite_annot exp



let rewrite_defs_remove_superfluous_letbinds =

  let e_aux (exp,annot) = match exp with
    | E_let (LB_aux (LB_val (pat, exp1), _), exp2) ->
       begin match untyp_pat pat, uncast_exp exp1, uncast_exp exp2 with
       (* 'let x = EXP1 in x' can be replaced with 'EXP1' *)
       | (P_aux (P_id id, _), _), _, (E_aux (E_id id', _), _)
         when Id.compare id id' = 0 ->
          exp1
       (* "let _ = () in exp" can be replaced with exp *)
       | (P_aux (P_wild, _), _), (E_aux (E_lit (L_aux (L_unit, _)), _), _), _ ->
          exp2
       (* "let x = EXP1 in return x" can be replaced with 'return (EXP1)', at
          least when EXP1 is 'small' enough *)
       | (P_aux (P_id id, _), _), _, (E_aux (E_internal_return (E_aux (E_id id', _)), _), _)
         when Id.compare id id' = 0 && small exp1 ->
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

(* FIXME: We shouldn't allow nested not-patterns *)
let rewrite_defs_not_pats =
  let rewrite_pexp (pexp_aux, annot) =
    let rewrite_pexp' pat exp orig_guard =
      let guards = ref [] in
      let not_counter = ref 0 in
      let rewrite_not_pat (pat_aux, annot) =
        match pat_aux with
        | P_not pat ->
           incr not_counter;
           let np_id = mk_id ("np#" ^ string_of_int !not_counter) in
           let guard =
             mk_exp (E_case (mk_exp (E_id np_id),
                             [mk_pexp (Pat_exp (strip_pat pat, mk_lit_exp L_false));
                              mk_pexp (Pat_exp (mk_pat P_wild, mk_lit_exp L_true))]))
           in
           guards := (np_id, typ_of_annot annot, guard) :: !guards;
           P_aux (P_id np_id, annot)

        | _ -> P_aux (pat_aux, annot)
       in
       let pat = fold_pat { id_pat_alg with p_aux = rewrite_not_pat } pat in
       begin match !guards with
       | [] ->
          Pat_aux (pexp_aux, annot)
       | guards ->
          let guard_exp =
            match orig_guard, guards with
            | Some guard, _ ->
               List.fold_left (fun exp1 (_, _, exp2) -> mk_exp (E_app_infix (exp1, mk_id "&", exp2))) guard guards
            | None, (_, _, guard) :: guards ->
               List.fold_left (fun exp1 (_, _, exp2) -> mk_exp (E_app_infix (exp1, mk_id "&", exp2))) guard guards
            | _ -> raise (Reporting.err_unreachable (fst annot) __POS__ "Case in not-pattern re-writing should be unreachable")
          in
          (* We need to construct an environment to check the match guard in *)
          let env = env_of_pat pat in
          let env = List.fold_left (fun env (np_id, np_typ, _) -> Env.add_local np_id (Immutable, np_typ) env) env guards in
          let guard_exp = Type_check.check_exp env guard_exp bool_typ in
          Pat_aux (Pat_when (pat, guard_exp, exp), annot)
       end
    in
    match pexp_aux with
    | Pat_exp (pat, exp) ->
       rewrite_pexp' pat exp None
    | Pat_when (pat, guard, exp) ->
       rewrite_pexp' pat exp (Some (strip_exp guard))
  in
  let rw_exp = { id_exp_alg with pat_aux = rewrite_pexp } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rw_exp) }

let rewrite_defs_remove_superfluous_returns =

  let add_opt_cast typopt1 typopt2 annot exp =
    match typopt1, typopt2 with
    | Some typ, _ | _, Some typ -> add_e_cast typ exp
    | None, None -> exp
  in

  let e_aux (exp,annot) = match exp with
    | E_let (LB_aux (LB_val (pat, exp1), _), exp2)
    | E_internal_plet (pat, exp1, exp2)
      when effectful exp1 ->
       begin match untyp_pat pat, uncast_exp exp2 with
       | (P_aux (P_lit (L_aux (lit,_)),_), ptyp),
         (E_aux (E_internal_return (E_aux (E_lit (L_aux (lit',_)),_)), a), etyp)
         when lit = lit' ->
          add_opt_cast ptyp etyp a exp1
       | (P_aux (P_wild,pannot), ptyp),
         (E_aux (E_internal_return (E_aux (E_lit (L_aux (L_unit,_)),_)), a), etyp)
         when is_unit_typ (typ_of exp1) ->
          add_opt_cast ptyp etyp a exp1
       | (P_aux (P_id id,_), ptyp),
         (E_aux (E_internal_return (E_aux (E_id id',_)), a), etyp)
         when Id.compare id id' == 0 ->
          add_opt_cast ptyp etyp a exp1
       | (P_aux (P_tup ps, _), ptyp),
         (E_aux (E_internal_return (E_aux (E_tuple es, _)), a), etyp)
         when List.length ps = List.length es ->
          let same_id (P_aux (p, _)) (E_aux (e, _)) = match p, e with
            | P_id id, E_id id' -> Id.compare id id' == 0
            | _, _ -> false
          in
          let ps = List.map fst (List.map untyp_pat ps) in
          let es = List.map fst (List.map uncast_exp es) in
          if List.for_all2 same_id ps es
          then add_opt_cast ptyp etyp a exp1
          else E_aux (exp,annot)
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
  let (Defs loop_specs) = fst (Type_error.check Env.empty (Defs (List.map gen_vs
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

let merge_funcls (Defs defs) =
  let merge_function (FD_aux (FD_function (r,t,e,fcls),ann) as f) =
    match fcls with
    | [] | [_] -> f
    | (FCL_aux (FCL_Funcl (id,_),(l,_)))::_ ->
       let var = mk_id "merge#var" in
       let l_g = Parse_ast.Generated l in
       let ann_g : _ * tannot = (l_g,empty_tannot) in
       let clauses = List.map (fun (FCL_aux (FCL_Funcl (_,pexp),_)) -> pexp) fcls in
       FD_aux (FD_function (r,t,e,[
         FCL_aux (FCL_Funcl (id,Pat_aux (Pat_exp (P_aux (P_id var,ann_g),
                                                  E_aux (E_case (E_aux (E_id var,ann_g),clauses),ann_g)),ann_g)),
                  (l,empty_tannot))]),ann)
  in
  let merge_in_def = function
    | DEF_fundef f -> DEF_fundef (merge_function f)
    | DEF_internal_mutrec fs -> DEF_internal_mutrec (List.map merge_function fs)
    | d -> d
  in Defs (List.map merge_in_def defs)


let rec exp_of_mpat ((MP_aux (mpat, (l,annot))) as mp_aux) =
  let empty_vec = E_aux (E_vector [], (l,())) in
  let concat_vectors vec1 vec2 =
    E_aux (E_vector_append (vec1, vec2), (l,()))
  in
  let empty_string = E_aux (E_lit (L_aux (L_string "", Parse_ast.Unknown)), (l,())) in
  let string_append str1 str2 =
    E_aux (E_app (mk_id "string_append", [str1; str2]), (l,()))
  in
  match mpat with
  | MP_lit lit                      -> E_aux (E_lit lit, (l,annot))
  | MP_id id                        -> E_aux (E_id id, (l,annot))
  | MP_app (id, args)               -> E_aux (E_app (id, (List.map exp_of_mpat args)), (l,annot))
  | MP_record (mfpats, flag)        -> E_aux (E_record (fexps_of_mfpats mfpats flag (l,annot)), (l,annot))
  | MP_vector mpats                 -> E_aux (E_vector (List.map exp_of_mpat mpats), (l,annot))
  | MP_vector_concat mpats          -> List.fold_right concat_vectors (List.map (fun m -> strip_exp (exp_of_mpat m)) mpats) empty_vec
  | MP_tup mpats                    -> E_aux (E_tuple (List.map exp_of_mpat mpats), (l,annot))
  | MP_list mpats                   -> E_aux (E_list (List.map exp_of_mpat mpats), (l,annot))
  | MP_cons (mpat1, mpat2)          -> E_aux (E_cons (exp_of_mpat mpat1, exp_of_mpat mpat2), (l,annot))
  | MP_string_append mpats          -> List.fold_right string_append (List.map (fun m -> strip_exp (exp_of_mpat m)) mpats) empty_string
  | MP_typ (mpat, typ)              -> E_aux (E_cast (typ, exp_of_mpat mpat), (l,annot))
  | MP_as (mpat, id)                -> E_aux (E_case (E_aux (E_id id, (l,annot)), [
                                                    Pat_aux (Pat_exp (pat_of_mpat mpat, exp_of_mpat mpat), (l,annot))
                                                ]), (l,annot)) (* TODO FIXME location information? *)


and fexps_of_mfpats mfpats flag annot =
  let fexp_of_mfpat (MFP_aux (MFP_mpat (id, mpat), annot)) =
    FE_aux (FE_Fexp (id, exp_of_mpat mpat), annot)
  in
  List.map fexp_of_mfpat mfpats

and pat_of_mpat (MP_aux (mpat, annot)) =
  match mpat with
  | MP_lit lit                      -> P_aux (P_lit lit, annot)
  | MP_id id                        -> P_aux (P_id id, annot)
  | MP_app (id, args)               -> P_aux (P_app (id, (List.map pat_of_mpat args)), annot)
  | MP_record (mfpats, flag)        -> P_aux (P_record ((fpats_of_mfpats mfpats), flag), annot)
  | MP_vector mpats                 -> P_aux (P_vector (List.map pat_of_mpat mpats), annot)
  | MP_vector_concat mpats          -> P_aux (P_vector_concat (List.map pat_of_mpat mpats), annot)
  | MP_tup mpats                    -> P_aux (P_tup (List.map pat_of_mpat mpats), annot)
  | MP_list mpats                   -> P_aux (P_list (List.map pat_of_mpat mpats), annot)
  | MP_cons (mpat1, mpat2)          -> P_aux ((P_cons (pat_of_mpat mpat1, pat_of_mpat mpat2), annot))
  | MP_string_append (mpats)        -> P_aux ((P_string_append (List.map pat_of_mpat mpats), annot))
  | MP_typ (mpat, typ)              -> P_aux (P_typ (typ, pat_of_mpat mpat), annot)
  | MP_as (mpat, id)                -> P_aux (P_as (pat_of_mpat mpat, id), annot)

and fpats_of_mfpats mfpats =
  let fpat_of_mfpat (MFP_aux (MFP_mpat (id, mpat), annot)) =
    FP_aux (FP_Fpat (id, pat_of_mpat mpat), annot)
  in
  List.map fpat_of_mfpat mfpats

let rewrite_defs_realise_mappings (Defs defs) =
  let realise_mpexps forwards mpexp1 mpexp2 =
    let mpexp_pat, mpexp_exp =
      if forwards then mpexp1, mpexp2
      else mpexp2, mpexp1
    in
    let exp =
      match mpexp_exp with
      | MPat_aux ((MPat_pat mpat), _) -> exp_of_mpat mpat
      | MPat_aux ((MPat_when (mpat, _), _)) -> exp_of_mpat mpat
    in
    match mpexp_pat with
    | MPat_aux (MPat_pat mpat, annot) -> Pat_aux (Pat_exp (pat_of_mpat mpat, exp), annot)
    | MPat_aux (MPat_when (mpat, guard), annot) -> Pat_aux (Pat_when (pat_of_mpat mpat, guard, exp), annot)
  in
  let realise_single_mpexp mpexp exp =
    match mpexp with
    | MPat_aux (MPat_pat mpat, annot) ->
       Pat_aux (Pat_exp (pat_of_mpat mpat, exp), annot)
    | MPat_aux (MPat_when (mpat, guard), annot) ->
       Pat_aux (Pat_when (pat_of_mpat mpat, guard, exp), annot)
  in
  let realise_mapcl forwards id mapcl =
    match mapcl with
    | (MCL_aux (MCL_bidir (mpexp1, mpexp2), (l, ()))) ->
       [realise_mpexps forwards mpexp1 mpexp2]
    | (MCL_aux (MCL_forwards (mpexp, exp), (l, ()))) ->
       if forwards then
         [realise_single_mpexp mpexp exp]
       else
         []
    | (MCL_aux (MCL_backwards (mpexp, exp), (l, ()))) ->
       if forwards then
         []
       else
         [realise_single_mpexp mpexp exp]
  in
  let realise_bool_mapcl forwards id mapcl =
    match mapcl with
    | (MCL_aux (MCL_bidir (mpexp1, mpexp2), (l, ()))) ->
       let mpexp = if forwards then mpexp1 else mpexp2 in
       [realise_mpexps true mpexp (mk_mpexp (MPat_pat (mk_mpat (MP_lit (mk_lit L_true)))))]
    | (MCL_aux (MCL_forwards (mpexp, exp), (l, ()))) ->
       if forwards then
         [realise_single_mpexp mpexp (mk_lit_exp L_true)]
       else
         []
    | (MCL_aux (MCL_backwards (mpexp, exp), (l, ()))) ->
       if forwards then
         []
       else
         [realise_single_mpexp mpexp (mk_lit_exp L_true)]
  in
  let arg_id = mk_id "arg#" in
  let arg_exp = (mk_exp (E_id arg_id)) in
  let arg_pat = mk_pat (P_id arg_id) in
  let placeholder_id = mk_id "s#" in
  let append_placeholder = function
    | MPat_aux (MPat_pat (MP_aux (MP_string_append mpats, p_annot)), aux_annot) ->
       MPat_aux (MPat_pat (MP_aux (MP_string_append (mpats @ [mk_mpat (MP_id placeholder_id)]), p_annot)), aux_annot)
    | MPat_aux (MPat_when (MP_aux (MP_string_append mpats, p_annot), guard), aux_annot) ->
       MPat_aux (MPat_when (MP_aux (MP_string_append (mpats @ [mk_mpat (MP_id placeholder_id)]), p_annot), guard), aux_annot)
    | MPat_aux (MPat_pat mpat, aux_annot) ->
       MPat_aux (MPat_pat (mk_mpat (MP_string_append [mpat; mk_mpat (MP_id placeholder_id)])), aux_annot)
    | MPat_aux (MPat_when (mpat, guard), aux_annot) ->
       MPat_aux (MPat_when (mk_mpat (MP_string_append [mpat; mk_mpat (MP_id placeholder_id)]), guard), aux_annot)
  in
  let realise_prefix_mapcl forwards id mapcl =
    let strlen = (
        mk_mpat (MP_app ( mk_id "sub_nat",
                          [
                            mk_mpat (MP_app ( mk_id "string_length" , [mk_mpat (MP_id arg_id        )]));
                            mk_mpat (MP_app ( mk_id "string_length" , [mk_mpat (MP_id placeholder_id)]));
                          ]
          ))
      ) in
    match mapcl with
    | (MCL_aux (MCL_bidir (mpexp1, mpexp2), (l, ()))) -> begin
       let mpexp = if forwards then mpexp1 else mpexp2 in
       let other = if forwards then mpexp2 else mpexp1 in
       match other with
       | MPat_aux (MPat_pat mpat2, _)
         | MPat_aux (MPat_when (mpat2, _), _)->
          [realise_mpexps true (append_placeholder mpexp) (mk_mpexp (MPat_pat (mk_mpat (MP_app ((mk_id "Some"), [ mk_mpat (MP_tup [mpat2; strlen]) ])))))]
      end
    | (MCL_aux (MCL_forwards (mpexp, exp), (l, ()))) -> begin
        if forwards then
          [realise_single_mpexp (append_placeholder mpexp) (mk_exp (E_app ((mk_id "Some"), [mk_exp (E_tuple [exp; exp_of_mpat strlen])])))]
        else
          []
      end
    | (MCL_aux (MCL_backwards (mpexp, exp), (l, ()))) -> begin
        if forwards then
          []
        else
          [realise_single_mpexp (append_placeholder mpexp) (mk_exp (E_app ((mk_id "Some"), [mk_exp (E_tuple [exp; exp_of_mpat strlen])])))]
      end
  in
  let realise_mapdef (MD_aux (MD_mapping (id, _, mapcls), ((l, (tannot:tannot)) as annot))) =
    let forwards_id = mk_id (string_of_id id ^ "_forwards") in
    let forwards_matches_id = mk_id (string_of_id id ^ "_forwards_matches") in
    let backwards_id = mk_id (string_of_id id ^ "_backwards") in
    let backwards_matches_id = mk_id (string_of_id id ^ "_backwards_matches") in

    let non_rec = (Rec_aux (Rec_nonrec, Parse_ast.Unknown)) in
    let effect_pure = (Effect_opt_aux (Effect_opt_pure, Parse_ast.Unknown)) in
    (* We need to make sure we get the environment for the last mapping clause *)
    let env = match List.rev mapcls with
      | MCL_aux (_, mapcl_annot) :: _ -> env_of_annot mapcl_annot
      | _ -> Type_check.typ_error l "mapping with no clauses?"
    in
    let (typq, bidir_typ) = Env.get_val_spec id env in
    let (typ1, typ2, l) = match bidir_typ with
      | Typ_aux (Typ_bidir (typ1, typ2), l) -> typ1, typ2, l
      | _ -> Type_check.typ_error l "non-bidir type of mapping?"
    in
    let forwards_typ = Typ_aux (Typ_fn ([typ1], typ2, no_effect), l) in
    let forwards_matches_typ = Typ_aux (Typ_fn ([typ1], bool_typ, no_effect), l) in
    let backwards_typ = Typ_aux (Typ_fn ([typ2], typ1, no_effect), l) in
    let backwards_matches_typ = Typ_aux (Typ_fn ([typ2], bool_typ, no_effect), l) in

    let forwards_spec = VS_aux (VS_val_spec (mk_typschm typq forwards_typ, forwards_id, (fun _ -> None), false), (Parse_ast.Unknown,())) in
    let backwards_spec = VS_aux (VS_val_spec (mk_typschm typq backwards_typ, backwards_id, (fun _ -> None), false), (Parse_ast.Unknown,())) in
    let forwards_matches_spec = VS_aux (VS_val_spec (mk_typschm typq forwards_matches_typ, forwards_matches_id, (fun _ -> None), false), (Parse_ast.Unknown,())) in
    let backwards_matches_spec = VS_aux (VS_val_spec (mk_typschm typq backwards_matches_typ, backwards_matches_id, (fun _ -> None), false), (Parse_ast.Unknown,())) in

    let forwards_spec, env = Type_check.check_val_spec env forwards_spec in
    let backwards_spec, env = Type_check.check_val_spec env backwards_spec in
    let forwards_matches_spec, env = Type_check.check_val_spec env forwards_matches_spec in
    let backwards_matches_spec, env = Type_check.check_val_spec env backwards_matches_spec in

    let no_tannot = (Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown)) in
    let forwards_match = mk_exp (E_case (arg_exp, ((List.map (fun mapcl -> strip_mapcl mapcl |> realise_mapcl true forwards_id) mapcls) |> List.flatten))) in
    let backwards_match = mk_exp (E_case (arg_exp, ((List.map (fun mapcl -> strip_mapcl mapcl |> realise_mapcl false backwards_id) mapcls) |> List.flatten))) in

    let wildcard = mk_pexp (Pat_exp (mk_pat P_wild, mk_exp (E_lit (mk_lit L_false)))) in
    let forwards_matches_match = mk_exp (E_case (arg_exp, ((List.map (fun mapcl -> strip_mapcl mapcl |> realise_bool_mapcl true forwards_matches_id) mapcls) |> List.flatten) @ [wildcard])) in
    let backwards_matches_match = mk_exp (E_case (arg_exp, ((List.map (fun mapcl -> strip_mapcl mapcl |> realise_bool_mapcl false backwards_matches_id) mapcls) |> List.flatten) @ [wildcard])) in

    let forwards_fun = (FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl forwards_id arg_pat forwards_match]), (l, ()))) in
    let backwards_fun = (FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl backwards_id arg_pat backwards_match]), (l, ()))) in
    let forwards_matches_fun = (FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl forwards_matches_id arg_pat forwards_matches_match]), (l, ()))) in
    let backwards_matches_fun = (FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl backwards_matches_id arg_pat backwards_matches_match]), (l, ()))) in

    typ_debug (lazy (Printf.sprintf "forwards for mapping %s: %s\n%!" (string_of_id id) (Pretty_print_sail.doc_fundef forwards_fun |> Pretty_print_sail.to_string)));
    typ_debug (lazy (Printf.sprintf "backwards for mapping %s: %s\n%!" (string_of_id id) (Pretty_print_sail.doc_fundef backwards_fun |> Pretty_print_sail.to_string)));
    typ_debug (lazy (Printf.sprintf "forwards matches for mapping %s: %s\n%!" (string_of_id id) (Pretty_print_sail.doc_fundef forwards_matches_fun |> Pretty_print_sail.to_string)));
    typ_debug (lazy (Printf.sprintf "backwards matches for mapping %s: %s\n%!" (string_of_id id) (Pretty_print_sail.doc_fundef backwards_matches_fun |> Pretty_print_sail.to_string)));
    let forwards_fun, _ = Type_check.check_fundef env forwards_fun in
    let backwards_fun, _ = Type_check.check_fundef env backwards_fun in
    let forwards_matches_fun, _ = Type_check.check_fundef env forwards_matches_fun in
    let backwards_matches_fun, _ = Type_check.check_fundef env backwards_matches_fun in

    let prefix_id = mk_id (string_of_id id ^ "_matches_prefix") in
    let prefix_wildcard = mk_pexp (Pat_exp (mk_pat P_wild, mk_exp (E_app (mk_id "None", [mk_exp (E_lit (mk_lit L_unit))])))) in
    let string_defs =
      begin if subtype_check env typ1 string_typ && subtype_check env string_typ typ1 then
              let forwards_prefix_typ = Typ_aux (Typ_fn ([typ1], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ2; nat_typ]), Parse_ast.Unknown)], no_effect), Parse_ast.Unknown) in
              let forwards_prefix_spec = VS_aux (VS_val_spec (mk_typschm typq forwards_prefix_typ, prefix_id, (fun _ -> None), false), (Parse_ast.Unknown,())) in
              let forwards_prefix_spec, env = Type_check.check_val_spec env forwards_prefix_spec in
              let forwards_prefix_match = mk_exp (E_case (arg_exp, ((List.map (fun mapcl -> strip_mapcl mapcl |> realise_prefix_mapcl true prefix_id) mapcls) |> List.flatten) @ [prefix_wildcard])) in
              let forwards_prefix_fun = (FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl prefix_id arg_pat forwards_prefix_match]), (l, ()))) in
              typ_debug (lazy (Printf.sprintf "forwards prefix matches for mapping %s: %s\n%!" (string_of_id id) (Pretty_print_sail.doc_fundef forwards_prefix_fun |> Pretty_print_sail.to_string)));
              let forwards_prefix_fun, _ = Type_check.check_fundef env forwards_prefix_fun in
              forwards_prefix_spec @ forwards_prefix_fun
            else
              if subtype_check env typ2 string_typ && subtype_check env string_typ typ2 then
                let backwards_prefix_typ = Typ_aux (Typ_fn ([typ2], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ1; nat_typ]), Parse_ast.Unknown)], no_effect), Parse_ast.Unknown) in
                let backwards_prefix_spec = VS_aux (VS_val_spec (mk_typschm typq backwards_prefix_typ, prefix_id, (fun _ -> None), false), (Parse_ast.Unknown,())) in
                let backwards_prefix_spec, env = Type_check.check_val_spec env backwards_prefix_spec in
                let backwards_prefix_match = mk_exp (E_case (arg_exp, ((List.map (fun mapcl -> strip_mapcl mapcl |> realise_prefix_mapcl false prefix_id) mapcls) |> List.flatten) @ [prefix_wildcard])) in
                let backwards_prefix_fun = (FD_aux (FD_function (non_rec, no_tannot, effect_pure, [mk_funcl prefix_id arg_pat backwards_prefix_match]), (l, ()))) in
                typ_debug (lazy (Printf.sprintf "backwards prefix matches for mapping %s: %s\n%!" (string_of_id id) (Pretty_print_sail.doc_fundef backwards_prefix_fun |> Pretty_print_sail.to_string)));
                let backwards_prefix_fun, _ = Type_check.check_fundef env backwards_prefix_fun in
                backwards_prefix_spec @ backwards_prefix_fun
              else
                []
      end
    in

      forwards_spec
    @ forwards_fun
    @ backwards_spec
    @ backwards_fun
    @ forwards_matches_spec
    @ forwards_matches_fun
    @ backwards_matches_spec
    @ backwards_matches_fun
    @ string_defs
  in
  let rewrite_def def =
    match def with
    | DEF_mapdef mdef -> realise_mapdef mdef
    | d -> [d]
  in
  Defs (List.map rewrite_def defs |> List.flatten)


(* Rewrite to make all pattern matches in Coq output exhaustive.
   Assumes that guards, vector patterns, etc have been rewritten already,
   and the scattered functions have been merged.
   Will add escape effect where a default is needed, so effects will
   need recalculated afterwards.

   Also detects and removes redundant wildcard patterns at the end of the match.
   (We could do more, but this is sufficient to deal with the code generated by
   the mappings rewrites.)

   Note: if this naive implementation turns out to be too slow or buggy, we
   could look at implementing Maranget JFP 17(3), 2007.
 *)

let opt_coq_warn_nonexhaustive = ref false

module MakeExhaustive =
struct

type rlit =
  | RL_unit
  (* TODO: zero and one are currently replaced by RL_inf to deal with BU;
     needs more careful thought about semantics of BU *)
  | RL_zero
  | RL_one
  | RL_true
  | RL_false
  | RL_inf

let string_of_rlit = function
  | RL_unit -> "()"
  | RL_zero -> "bitzero"
  | RL_one -> "bitone"
  | RL_true -> "true"
  | RL_false -> "false"
  | RL_inf -> "..."

let rlit_of_lit (L_aux (l,_)) =
  match l with
  | L_unit -> RL_unit
  | L_zero -> (*RL_zero*) RL_inf
  | L_one -> (*RL_one*) RL_inf
  | L_true -> RL_true
  | L_false -> RL_false
  | L_num _ | L_hex _ | L_bin _ | L_string _ | L_real _ -> RL_inf
  | L_undef -> assert false

let inv_rlit_of_lit (L_aux (l,_)) =
  match l with
  | L_unit -> []
  | L_zero -> (*[RL_one]*) [RL_inf]
  | L_one -> (*[RL_zero]*) [RL_inf]
  | L_true -> [RL_false]
  | L_false -> [RL_true]
  | L_num _ | L_hex _ | L_bin _ | L_string _ | L_real _ -> [RL_inf]
  | L_undef -> assert false

type residual_pattern =
  | RP_any
  | RP_lit of rlit
  | RP_enum of id
  | RP_app of id * residual_pattern list
  | RP_tup of residual_pattern list
  | RP_nil
  | RP_cons of residual_pattern * residual_pattern

let rec string_of_rp = function
  | RP_any -> "_"
  | RP_lit rlit -> string_of_rlit rlit
  | RP_enum id -> string_of_id id
  | RP_app (f,args) -> string_of_id f ^ "(" ^ String.concat "," (List.map string_of_rp args) ^ ")"
  | RP_tup rps -> "(" ^ String.concat "," (List.map string_of_rp rps) ^ ")"
  | RP_nil -> "[| |]"
  | RP_cons (rp1,rp2) -> string_of_rp rp1 ^ "::" ^ string_of_rp rp2

type ctx = {
  env : Env.t;
  enum_to_rest: (residual_pattern list) Bindings.t;
  constructor_to_rest: (residual_pattern list) Bindings.t
}

let make_enum_mappings ids m =
  IdSet.fold (fun id m ->
    Bindings.add id
      (List.map (fun e -> RP_enum e) (IdSet.elements (IdSet.remove id ids))) m)
    ids
    m

let make_cstr_mappings env ids m =
  let ids = IdSet.elements ids in
  let constructors = List.map
    (fun id ->
      let _,ty = Env.get_val_spec id env in
      let args = match ty with
        | Typ_aux (Typ_fn (tys,_,_),_) -> List.map (fun _ -> RP_any) tys
        | _ -> [RP_any]
      in RP_app (id,args)) ids in
  let rec aux ids acc l =
    match ids, l with
    | [], [] -> m
    | id::ids, rp::t ->
       let m = aux ids (acc@[rp]) t in
       Bindings.add id (acc@t) m
    | _ -> assert false
  in aux ids [] constructors

let ctx_from_pattern_completeness_ctx env =
  let ctx = Env.pattern_completeness_ctx env in
  { env = env;
    enum_to_rest = Bindings.fold (fun _ ids m -> make_enum_mappings ids m) 
      ctx.Pattern_completeness.enums Bindings.empty;
    constructor_to_rest = Bindings.fold (fun _ ids m -> make_cstr_mappings env ids m)
      ctx.Pattern_completeness.variants Bindings.empty
  }

let printprefix = ref "  "

let rec remove_clause_from_pattern ctx (P_aux (rm_pat,ann)) res_pat =
  let subpats rm_pats res_pats =
    let res_pats' = List.map2 (remove_clause_from_pattern ctx) rm_pats res_pats in
    let rec aux acc fixed residual =
      match fixed, residual with
      | [], [] -> []
      | (fh::ft), (rh::rt) ->
         let rt' = aux (acc@[fh]) ft rt in
         let newr = List.map (fun x -> acc @ (x::ft)) rh in
         newr @ rt'
      | _,_ -> assert false (* impossible because we managed map2 above *)
    in aux [] res_pats res_pats'
  in
  let inconsistent () =
    raise (Reporting.err_unreachable (fst ann) __POS__
             ("Inconsistency during exhaustiveness analysis with " ^
                 string_of_rp res_pat))
  in
  (*let _ = print_endline (!printprefix ^ "pat: " ^string_of_pat (P_aux (rm_pat,ann))) in
  let _ = print_endline (!printprefix ^ "res_pat: " ^string_of_rp res_pat) in
  let _ = printprefix := "  " ^ !printprefix in*)
  let rp' =
  match rm_pat with
  | P_wild -> []
  | P_id id when (match Env.lookup_id id ctx.env with Unbound | Local _ -> true | _ -> false) -> []
  | P_lit lit ->
     (match res_pat with
     | RP_any -> List.map (fun l -> RP_lit l) (inv_rlit_of_lit lit)
     | RP_lit RL_inf -> [res_pat]
     | RP_lit lit' -> if lit' = rlit_of_lit lit then [] else [res_pat]
     | _ -> inconsistent ())
  | P_as (p,_) 
  | P_typ (_,p)
  | P_var (p,_) 
    -> remove_clause_from_pattern ctx p res_pat
  | P_id id ->
     (match Env.lookup_id id ctx.env with
     | Enum enum ->
        (match res_pat with
        | RP_any -> Bindings.find id ctx.enum_to_rest
        | RP_enum id' -> if Id.compare id id' == 0 then [] else [res_pat]
        | _ -> inconsistent ())
     | _ -> assert false)
  | P_tup rm_pats ->
     let previous_res_pats = 
       match res_pat with
       | RP_tup res_pats -> res_pats
       | RP_any -> List.map (fun _ -> RP_any) rm_pats
       | _ -> inconsistent ()
     in
     let res_pats' = subpats rm_pats previous_res_pats in
     List.map (fun rps -> RP_tup rps) res_pats'
  | P_app (id,args) ->
     (match res_pat with
     | RP_app (id',residual_args) ->
        if Id.compare id id' == 0 then
          let res_pats' =
            (* Constructors that were specified without a return type might get
               an extra tuple in their type; expand that here if necessary.
               TODO: this should go away if we enforce proper arities. *)
            match args, residual_args with
            | [], [RP_any]
            | _::_::_, [RP_any]
              -> subpats args (List.map (fun _ -> RP_any) args)
            | _,_ ->
               subpats args residual_args in
          List.map (fun rps -> RP_app (id,rps)) res_pats'
        else [res_pat]
     | RP_any ->
        let res_args = subpats args (List.map (fun _ -> RP_any) args) in
        (List.map (fun l -> (RP_app (id,l))) res_args) @
          (Bindings.find id ctx.constructor_to_rest)
     | _ -> inconsistent ()
     )
  | P_list ps ->
     (match ps with
     | p1::ptl -> remove_clause_from_pattern ctx (P_aux (P_cons (p1,P_aux (P_list ptl,ann)),ann)) res_pat
     | [] ->
        match res_pat with
        | RP_any -> [RP_cons (RP_any,RP_any)]
        | RP_cons _ -> [res_pat]
        | RP_nil -> []
        | _ -> inconsistent ())
  | P_cons (p1,p2) -> begin
     let rp',rps = 
       match res_pat with
       | RP_cons (rp1,rp2) -> [], Some [rp1;rp2]
       | RP_any -> [RP_nil], Some [RP_any;RP_any]
       | RP_nil -> [RP_nil], None
       | _ -> inconsistent ()
     in
     match rps with
     | None -> rp'
     | Some rps ->
        let res_pats = subpats [p1;p2] rps in
        rp' @ List.map (function [rp1;rp2] -> RP_cons (rp1,rp2) | _ -> assert false) res_pats
  end
  | P_record _ ->
     raise (Reporting.err_unreachable (fst ann) __POS__
              "Record pattern not supported")
  | P_vector _
  | P_vector_concat _
  | P_string_append _ ->
     raise (Reporting.err_unreachable (fst ann) __POS__
              "Found pattern that should have been rewritten away in earlier stage")

  (*in let _ = printprefix := String.sub (!printprefix) 0 (String.length !printprefix - 2)
  in let _ = print_endline (!printprefix ^ "res_pats': " ^ String.concat "; " (List.map string_of_rp rp'))*)
  in rp'

let process_pexp env =
  let ctx = ctx_from_pattern_completeness_ctx env in
  fun rps patexp ->
  (*let _ = print_endline ("res_pats: " ^ String.concat "; " (List.map string_of_rp rps)) in
    let _ = print_endline ("pat: " ^ string_of_pexp patexp) in*)
  match patexp with
  | Pat_aux (Pat_exp (p,_),_) -> 
     List.concat (List.map (remove_clause_from_pattern ctx p) rps)
  | Pat_aux (Pat_when _,(l,_)) ->
     raise (Reporting.err_unreachable l __POS__
              "Guarded pattern should have been rewritten away")

(* We do some minimal redundancy checking to remove bogus wildcard patterns here *)
let check_cases process is_wild loc_of cases =
  let rec aux rps acc = function
    | [] -> acc, rps
    | [p] when is_wild p && match rps with [] -> true | _ -> false ->
      let () = Reporting.print_err false false
        (loc_of p) "Match checking" "Redundant wildcard clause" in
      acc, []
    | h::t -> aux (process rps h) (h::acc) t
  in
  let cases, rps = aux [RP_any] [] cases in
  List.rev cases, rps

let not_enum env id =
  match Env.lookup_id id env with
  | Enum _ -> false
  | _ -> true

let pexp_is_wild = function
  | (Pat_aux (Pat_exp (P_aux (P_wild,_),_),_)) -> true
  | (Pat_aux (Pat_exp (P_aux (P_id id,ann),_),_))
       when not_enum (env_of_annot ann) id -> true
  | _ -> false

let pexp_loc = function
  | (Pat_aux (Pat_exp (P_aux (_,(l,_)),_),_)) -> l
  | (Pat_aux (Pat_when (P_aux (_,(l,_)),_,_),_)) -> l

let funcl_is_wild = function
  | (FCL_aux (FCL_Funcl (_,pexp),_)) -> pexp_is_wild pexp

let funcl_loc (FCL_aux (_,(l,_))) = l

let rewrite_case (e,ann) =
  match e with
  | E_case (e1,cases) ->
     begin
     let env = env_of_annot ann in
     let cases, rps = check_cases (process_pexp env) pexp_is_wild pexp_loc cases in
     match rps with
     | [] -> E_aux (E_case (e1,cases),ann)
     | (example::_) ->

        let _ =
          if !opt_coq_warn_nonexhaustive
          then Reporting.print_err false false
            (fst ann) "Non-exhaustive matching" ("Example: " ^ string_of_rp example) in

        let l = Parse_ast.Generated Parse_ast.Unknown in
        let p = P_aux (P_wild, (l, empty_tannot)) in
        let ann' = mk_tannot env (typ_of_annot ann) (mk_effect [BE_escape]) in
        (* TODO: use an expression that specifically indicates a failed pattern match *)
        let b = E_aux (E_exit (E_aux (E_lit (L_aux (L_unit, l)),(l,empty_tannot))),(l,ann')) in
        E_aux (E_case (e1,cases@[Pat_aux (Pat_exp (p,b),(l,empty_tannot))]),ann)
     end
  | E_let (LB_aux (LB_val (pat,e1),lb_ann),e2) ->
     begin
     let env = env_of_annot ann in
     let ctx = ctx_from_pattern_completeness_ctx env in
     let rps = remove_clause_from_pattern ctx pat RP_any in
     match rps with
     | [] -> E_aux (e,ann)
     | (example::_) ->
        let _ =
          if !opt_coq_warn_nonexhaustive
          then Reporting.print_err false false
            (fst ann) "Non-exhaustive let" ("Example: " ^ string_of_rp example) in
        let l = Parse_ast.Generated Parse_ast.Unknown in
        let p = P_aux (P_wild, (l, empty_tannot)) in
        let ann' = mk_tannot env (typ_of_annot ann) (mk_effect [BE_escape]) in
        (* TODO: use an expression that specifically indicates a failed pattern match *)
        let b = E_aux (E_exit (E_aux (E_lit (L_aux (L_unit, l)),(l,empty_tannot))),(l,ann')) in
        E_aux (E_case (e1,[Pat_aux (Pat_exp(pat,e2),ann);
                           Pat_aux (Pat_exp (p,b),(l,empty_tannot))]),ann)
     end
  | _ -> E_aux (e,ann)

let rewrite_fun rewriters (FD_aux (FD_function (r,t,e,fcls),f_ann)) =
  let id,fcl_ann =
    match fcls with
    | FCL_aux (FCL_Funcl (id,_),ann) :: _ -> id,ann
    | [] -> raise (Reporting.err_unreachable (fst f_ann) __POS__
                 "Empty function")
  in
  let env = env_of_annot fcl_ann in
  let process_funcl rps (FCL_aux (FCL_Funcl (_,pexp),_)) = process_pexp env rps pexp in
  let fcls, rps = check_cases process_funcl funcl_is_wild funcl_loc fcls in
  let fcls' = List.map (function FCL_aux (FCL_Funcl (id,pexp),ann) ->
                                  FCL_aux (FCL_Funcl (id, rewrite_pexp rewriters pexp),ann))
                fcls in
  match rps with
  | [] -> FD_aux (FD_function (r,t,e,fcls'),f_ann)
  | (example::_) ->
     let _ =
       if !opt_coq_warn_nonexhaustive
       then Reporting.print_err false false
              (fst f_ann) "Non-exhaustive matching" ("Example: " ^ string_of_rp example) in

     let l = Parse_ast.Generated Parse_ast.Unknown in
     let p = P_aux (P_wild, (l, empty_tannot)) in
     let ann' = mk_tannot env (typ_of_annot fcl_ann) (mk_effect [BE_escape]) in
     (* TODO: use an expression that specifically indicates a failed pattern match *)
     let b = E_aux (E_exit (E_aux (E_lit (L_aux (L_unit, l)),(l,empty_tannot))),(l,ann')) in
     let default = FCL_aux (FCL_Funcl (id,Pat_aux (Pat_exp (p,b),(l,empty_tannot))),fcl_ann) in

     FD_aux (FD_function (r,t,e,fcls'@[default]),f_ann)
  

let rewrite =
  let alg = { id_exp_alg with e_aux = rewrite_case } in
  rewrite_defs_base
    { rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


end

(* Splitting a function (e.g., an execute function on an AST) can produce
   new functions that appear to be recursive but are not.  This checks to
   see if the flag can be turned off.  Doesn't handle mutual recursion
   for now. *)
let minimise_recursive_functions (Defs defs) =
  let funcl_is_rec (FCL_aux (FCL_Funcl (id,pexp),_)) =
    fold_pexp
      { (pure_exp_alg false (||)) with
        e_app = (fun (id',args) ->
          Id.compare id id' == 0 || List.exists (fun x -> x) args);
        e_app_infix = (fun (arg1,id',arg2) ->
          arg1 || arg2 || Id.compare id id' == 0)
      } pexp
  in
  let rewrite_function (FD_aux (FD_function (recopt,topt,effopt,funcls),ann) as fd) =
    match recopt with
    | Rec_aux (Rec_nonrec, _) -> fd
    | Rec_aux ((Rec_rec | Rec_measure _), l) ->
       if List.exists funcl_is_rec funcls
       then fd
       else FD_aux (FD_function (Rec_aux (Rec_nonrec, Generated l),topt,effopt,funcls),ann)
  in
  let rewrite_def = function
    | DEF_fundef fd -> DEF_fundef (rewrite_function fd)
    | d -> d
  in Defs (List.map rewrite_def defs)

let move_termination_measures (Defs defs) =
  let scan_for id defs =
    let rec aux = function
      | [] -> None
      | (DEF_measure (id',pat,exp))::t ->
         if Id.compare id id' == 0 then Some (pat,exp) else aux t
      | (DEF_fundef (FD_aux (FD_function (_,_,_,FCL_aux (FCL_Funcl (id',_),_)::_),_)))::_
      | (DEF_spec (VS_aux (VS_val_spec (_,id',_,_),_))::_)
        when Id.compare id id' == 0 -> None
      | _::t -> aux t
    in aux defs
  in
  let rec aux acc = function
    | [] -> List.rev acc
    | (DEF_fundef (FD_aux (FD_function (r,ty,e,fs),(l,f_ann))) as d)::t -> begin
       let id = match fs with
         | [] -> assert false (* TODO *)
         | (FCL_aux (FCL_Funcl (id,_),_))::_ -> id
       in
       match scan_for id t with
       | None -> aux (d::acc) t
       | Some (pat,exp) ->
          let r = Rec_aux (Rec_measure (pat,exp), Generated l) in
          aux (DEF_fundef (FD_aux (FD_function (r,ty,e,fs),(l,f_ann)))::acc) t
      end
    | (DEF_measure _)::t -> aux acc t
    | h::t -> aux (h::acc) t
  in Defs (aux [] defs)

(* Make recursive functions with a measure use the measure as an
   explicit recursion limit, enforced by an assertion. *)
let rewrite_explicit_measure (Defs defs) =
  let scan_function measures = function
    | FD_aux (FD_function (Rec_aux (Rec_measure (mpat,mexp),rl),topt,effopt,
                           FCL_aux (FCL_Funcl (id,_),_)::_),ann) ->
       Bindings.add id (mpat,mexp) measures
    | _ -> measures
  in
  let scan_def measures = function
    | DEF_fundef fd -> scan_function measures fd
    | _ -> measures
  in
  let measures = List.fold_left scan_def Bindings.empty defs in
  let add_escape eff =
    union_effects eff (mk_effect [BE_escape])
  in
  (* NB: the Coq backend relies on recognising the #rec# prefix *)
  let rec_id = function
    | Id_aux (Id id,l)
    | Id_aux (DeIid id,l) -> Id_aux (Id ("#rec#" ^ id),Generated l)
  in
  let limit = mk_id "#reclimit" in
  (* Add helper function with extra argument to spec *)
  let rewrite_spec (VS_aux (VS_val_spec (typsch,id,extern,flag),ann) as vs) =
    match Bindings.find id measures with
    | _ -> begin
       match typsch with
       | TypSchm_aux (TypSchm_ts (tq,
           Typ_aux (Typ_fn (args,res,eff),typl)),tsl) ->
          [VS_aux (VS_val_spec (
             TypSchm_aux (TypSchm_ts (tq,
               Typ_aux (Typ_fn (args@[int_typ],res,add_escape eff),typl)),tsl)
                     ,rec_id id,extern,flag),ann);
           VS_aux (VS_val_spec (
             TypSchm_aux (TypSchm_ts (tq,
               Typ_aux (Typ_fn (args,res,add_escape eff),typl)),tsl)
                     ,id,extern,flag),ann)]
       | _ -> [vs] (* TODO warn *)
      end
    | exception Not_found -> [vs]
  in
  (* Add extra argument and assertion to each funcl, and rewrite recursive calls *)
  let rewrite_funcl (FCL_aux (FCL_Funcl (id,pexp),fcl_ann) as fcl) =
    let loc = Parse_ast.Generated (fst fcl_ann) in
    let P_aux (pat,pann),guard,body,ann = destruct_pexp pexp in
    let extra_pat = P_aux (P_id limit,(loc,empty_tannot)) in
    let pat = match pat with
      | P_tup pats -> P_tup (pats@[extra_pat])
      | p -> P_tup [P_aux (p,pann);extra_pat]
    in
    let assert_exp =
      E_aux (E_assert
         (E_aux (E_app (mk_id "gteq_int",
           [E_aux (E_id limit,(loc,empty_tannot));
            E_aux (E_lit (L_aux (L_num Big_int.zero,loc)),(loc,empty_tannot))]),
           (loc,empty_tannot)),
          (E_aux (E_lit (L_aux (L_string "recursion limit reached",loc)),(loc,empty_tannot)))),
              (loc,empty_tannot))
    in
    let tick =
      E_aux (E_app (mk_id "sub_int",
        [E_aux (E_id limit,(loc,empty_tannot));
         E_aux (E_lit (L_aux (L_num (Big_int.of_int 1),loc)),(loc,empty_tannot))]),
             (loc,empty_tannot))
    in
    let open Rewriter in
    let body =
      fold_exp { id_exp_alg with
          e_app = (fun (f,args) ->
          if Id.compare f id == 0
          then E_app (rec_id id, args@[tick])
          else E_app (f, args))
        } body
    in
    let body = E_aux (E_block [assert_exp; body],(loc,empty_tannot)) in
    FCL_aux (FCL_Funcl (rec_id id, construct_pexp (P_aux (pat,pann),guard,body,ann)),fcl_ann)
  in
  let rewrite_function (FD_aux (FD_function (r,t,e,fcls),ann) as fd) =
    let loc = Parse_ast.Generated (fst ann) in
    match fcls with
    | FCL_aux (FCL_Funcl (id,_),fcl_ann)::_ -> begin
        match Bindings.find id measures with
        | (measure_pat, measure_exp) ->
           let e = match e with
             | Effect_opt_aux (Effect_opt_pure, _) ->
                Effect_opt_aux (Effect_opt_effect (mk_effect [BE_escape]), loc)
             | Effect_opt_aux (Effect_opt_effect eff,_) ->
                Effect_opt_aux (Effect_opt_effect (add_escape eff), loc)
           in
           let arg_typs = match Env.get_val_spec id (env_of_annot fcl_ann) with
             | _, Typ_aux (Typ_fn (args,_,_),_) -> args
             | _, _ -> raise (Reporting.err_unreachable (fst ann) __POS__
                            "Function doesn't have function type")
           in
           let measure_pats = match arg_typs, measure_pat with
             | [_], _ -> [measure_pat]
             | _, P_aux (P_tup ps,_) -> ps
             | _, _ -> [measure_pat]
           in
           let mk_wrap i (P_aux (p,(l,_))) =
             let id =
               match p with
               | P_id id
               | P_typ (_,(P_aux (P_id id,_))) -> id
               | P_wild
               | P_typ (_,(P_aux (P_wild,_))) ->
                  mk_id ("_arg" ^ string_of_int i)
               | _ -> raise (Reporting.err_todo l "Measure patterns can only be identifiers or wildcards")
             in
             P_aux (P_id id,(loc,empty_tannot)),
             E_aux (E_id id,(loc,empty_tannot))
           in
           let wpats,wexps = List.split (Util.list_mapi mk_wrap measure_pats) in
           let wpat = match wpats with
             | [wpat] -> wpat
             | _ -> P_aux (P_tup wpats,(loc,empty_tannot))
           in
           let measure_exp = E_aux (E_cast (int_typ, measure_exp),(loc,empty_tannot)) in
           let wbody = E_aux (E_app (rec_id id,wexps@[measure_exp]),(loc,empty_tannot)) in
           let wrapper =
             FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (wpat,wbody),(loc,empty_tannot))),(loc,empty_tannot))
           in
           let new_rec =
             Rec_aux (Rec_measure (P_aux (P_tup (List.map (fun _ -> P_aux (P_wild,(loc,empty_tannot))) measure_pats @ [P_aux (P_id limit,(loc,empty_tannot))]),(loc,empty_tannot)), E_aux (E_id limit, (loc,empty_tannot))), loc)
           in
           [FD_aux (FD_function (new_rec,t,e,List.map rewrite_funcl fcls),ann);
            FD_aux (FD_function (Rec_aux (Rec_nonrec,loc),t,e,[wrapper]),ann)]
        | exception Not_found -> [fd]
      end
    | _ -> [fd]
  in
  let rewrite_def = function
    | DEF_spec vs -> List.map (fun vs -> DEF_spec vs) (rewrite_spec vs)
    | DEF_fundef fd -> List.map (fun f -> DEF_fundef f) (rewrite_function fd)
    | d -> [d]
  in
  Defs (List.flatten (List.map rewrite_def defs))

let recheck_defs defs = fst (Type_error.check initial_env defs)
let recheck_defs_without_effects defs =
  let () = opt_no_effects := true in
  let result,_ = Type_error.check initial_env defs in
  let () = opt_no_effects := false in
  result

let remove_mapping_valspecs (Defs defs) =
  let allowed_def def =
    match def with
    | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (_, Typ_aux (Typ_bidir _, _)), _), _, _, _), _)) -> false
    | _ -> true
  in
  Defs (List.filter allowed_def defs)


let opt_mono_rewrites = ref false
let opt_mono_complex_nexps = ref true

let mono_rewrites defs =
  if !opt_mono_rewrites then
    Monomorphise.mono_rewrites defs
  else defs

let rewrite_toplevel_nexps defs =
  if !opt_mono_complex_nexps then
    Monomorphise.rewrite_toplevel_nexps defs
  else defs

let opt_mono_split = ref ([]:((string * int) * string) list)
let opt_dmono_analysis = ref 0
let opt_auto_mono = ref false
let opt_dall_split_errors = ref false
let opt_dmono_continue = ref false

let monomorphise defs =
  let open Monomorphise in
  monomorphise
    { auto = !opt_auto_mono;
      debug_analysis = !opt_dmono_analysis;
      all_split_errors = !opt_dall_split_errors;
      continue_anyway = !opt_dmono_continue }
    !opt_mono_split
    defs

let if_mono f defs =
  match !opt_mono_split, !opt_auto_mono with
  | [], false -> defs
  | _, _ -> f defs

(* Also turn mwords stages on when we're just trying out mono *)
let if_mwords f defs =
  if !Pretty_print_lem.opt_mwords then f defs else if_mono f defs

let rewrite_defs_lem = [
  ("realise_mappings", rewrite_defs_realise_mappings);
  ("remove_mapping_valspecs", remove_mapping_valspecs);
  ("toplevel_string_append", rewrite_defs_toplevel_string_append);
  ("pat_string_append", rewrite_defs_pat_string_append);
  ("mapping_builtins", rewrite_defs_mapping_patterns);
  ("mono_rewrites", mono_rewrites);
  ("recheck_defs", if_mono recheck_defs);
  ("rewrite_toplevel_nexps", if_mono rewrite_toplevel_nexps);
  ("monomorphise", if_mono monomorphise);
  ("recheck_defs", if_mwords recheck_defs);
  ("add_bitvector_casts", if_mwords Monomorphise.add_bitvector_casts);
  ("rewrite_atoms_to_singletons", if_mono Monomorphise.rewrite_atoms_to_singletons);
  ("recheck_defs", if_mwords recheck_defs);
  ("rewrite_undefined", rewrite_undefined_if_gen false);
  ("rewrite_defs_vector_string_pats_to_bit_list", rewrite_defs_vector_string_pats_to_bit_list);
  ("remove_not_pats", rewrite_defs_not_pats);
  ("pat_lits", rewrite_defs_pat_lits rewrite_lit_lem);
  ("vector_concat_assignments", rewrite_vector_concat_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("remove_numeral_pats", rewrite_defs_remove_numeral_pats);
  ("guarded_pats", rewrite_defs_guarded_pats);
  ("bitvector_exps", rewrite_bitvector_exps);
  (* ("register_ref_writes", rewrite_register_ref_writes); *)
  ("nexp_ids", rewrite_defs_nexp_ids);
  ("fix_val_specs", rewrite_fix_val_specs);
  ("split_execute", rewrite_split_fun_constr_pats "execute");
  ("recheck_defs", recheck_defs);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  (* ("constraint", rewrite_constraint); *)
  (* ("remove_assert", rewrite_defs_remove_assert); *)
  ("top_sort_defs", top_sort_defs);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ("early_return", rewrite_defs_early_return);
  ("fix_val_specs", rewrite_fix_val_specs);
  (* early_return currently breaks the types *)
  ("recheck_defs", recheck_defs);
  ("remove_blocks", rewrite_defs_remove_blocks);
  ("letbind_effects", rewrite_defs_letbind_effects);
  ("remove_e_assign", rewrite_defs_remove_e_assign);
  ("internal_lets", rewrite_defs_internal_lets);
  ("remove_superfluous_letbinds", rewrite_defs_remove_superfluous_letbinds);
  ("remove_superfluous_returns", rewrite_defs_remove_superfluous_returns);
  ("merge function clauses", merge_funcls);
  ("recheck_defs", recheck_defs)
  ]

let rewrite_defs_coq = [
  ("realise_mappings", rewrite_defs_realise_mappings);
  ("remove_mapping_valspecs", remove_mapping_valspecs);
  ("toplevel_string_append", rewrite_defs_toplevel_string_append);
  ("pat_string_append", rewrite_defs_pat_string_append);
  ("mapping_builtins", rewrite_defs_mapping_patterns);
  ("rewrite_undefined", rewrite_undefined_if_gen true);
  ("rewrite_defs_vector_string_pats_to_bit_list", rewrite_defs_vector_string_pats_to_bit_list);
  ("remove_not_pats", rewrite_defs_not_pats);
  ("pat_lits", rewrite_defs_pat_lits rewrite_lit_lem);
  ("vector_concat_assignments", rewrite_vector_concat_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("remove_numeral_pats", rewrite_defs_remove_numeral_pats);
  ("guarded_pats", rewrite_defs_guarded_pats);
  ("bitvector_exps", rewrite_bitvector_exps);
  (* ("register_ref_writes", rewrite_register_ref_writes); *)
  ("nexp_ids", rewrite_defs_nexp_ids);
  ("fix_val_specs", rewrite_fix_val_specs);
  ("split_execute", rewrite_split_fun_constr_pats "execute");
  ("minimise_recursive_functions", minimise_recursive_functions);
  ("recheck_defs", recheck_defs);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  (* ("constraint", rewrite_constraint); *)
  (* ("remove_assert", rewrite_defs_remove_assert); *)
  ("move_termination_measures", move_termination_measures);
  ("top_sort_defs", top_sort_defs);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ("early_return", rewrite_defs_early_return);
  (* merge funcls before adding the measure argument so that it doesn't
     disappear into an internal pattern match *)
  ("merge function clauses", merge_funcls);
  ("recheck_defs_without_effects", recheck_defs_without_effects);
  ("make_cases_exhaustive", MakeExhaustive.rewrite);
  ("rewrite_explicit_measure", rewrite_explicit_measure);
  ("recheck_defs_without_effects", recheck_defs_without_effects);
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
    (* ("undefined", rewrite_undefined); *)
  ("no_effect_check", (fun defs -> opt_no_effects := true; defs));
  ("realise_mappings", rewrite_defs_realise_mappings);
  ("toplevel_string_append", rewrite_defs_toplevel_string_append);
  ("pat_string_append", rewrite_defs_pat_string_append);
  ("mapping_builtins", rewrite_defs_mapping_patterns);
  ("rewrite_undefined", rewrite_undefined_if_gen false);
  ("rewrite_defs_vector_string_pats_to_bit_list", rewrite_defs_vector_string_pats_to_bit_list);
  ("pat_lits", rewrite_defs_pat_lits rewrite_lit_ocaml);
  ("vector_concat_assignments", rewrite_vector_concat_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_not_pats", rewrite_defs_not_pats);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("remove_numeral_pats", rewrite_defs_remove_numeral_pats);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  ("top_sort_defs", top_sort_defs);
  ("constraint", rewrite_constraint);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ("simple_types", rewrite_simple_types);
  ("overload_cast", rewrite_overload_cast);
  (* ("separate_numbs", rewrite_defs_separate_numbs) *)
  ]

let rewrite_defs_c = [
  ("no_effect_check", (fun defs -> opt_no_effects := true; defs));
  ("realise_mappings", rewrite_defs_realise_mappings);
  ("toplevel_string_append", rewrite_defs_toplevel_string_append);
  ("pat_string_append", rewrite_defs_pat_string_append);
  ("mapping_builtins", rewrite_defs_mapping_patterns);
  ("rewrite_undefined", rewrite_undefined_if_gen false);
  ("rewrite_defs_vector_string_pats_to_bit_list", rewrite_defs_vector_string_pats_to_bit_list);
  ("remove_not_pats", rewrite_defs_not_pats);
  ("pat_lits", rewrite_defs_pat_lits (fun _ -> true));
  ("vector_concat_assignments", rewrite_vector_concat_assignments);
  ("tuple_assignments", rewrite_tuple_assignments);
  ("simple_assignments", rewrite_simple_assignments);
  ("remove_vector_concat", rewrite_defs_remove_vector_concat);
  ("remove_bitvector_pats", rewrite_defs_remove_bitvector_pats);
  ("guarded_pats", rewrite_defs_guarded_pats);
  ("exp_lift_assign", rewrite_defs_exp_lift_assign);
  ("constraint", rewrite_constraint);
  ("trivial_sizeof", rewrite_trivial_sizeof);
  ("sizeof", rewrite_sizeof);
  ("merge_function_clauses", merge_funcls);
  ("recheck_defs", Optimize.recheck)
  ]

let rewrite_defs_interpreter = [
    ("no_effect_check", (fun defs -> opt_no_effects := true; defs));
    ("realise_mappings", rewrite_defs_realise_mappings);
    ("toplevel_string_append", rewrite_defs_toplevel_string_append);
    ("pat_string_append", rewrite_defs_pat_string_append);
    ("mapping_builtins", rewrite_defs_mapping_patterns);
    ("rewrite_undefined", rewrite_undefined_if_gen false);
    ("vector_concat_assignments", rewrite_vector_concat_assignments);
    ("tuple_assignments", rewrite_tuple_assignments);
    ("simple_assignments", rewrite_simple_assignments);
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
       then raise (Reporting.err_typ Parse_ast.Unknown
                    ("Found synonym in annotation " ^ string_of_typ typ1 ^ " vs " ^ string_of_typ typ2))
       else ());
      exp
    with
      Type_error (l, err) -> raise (Reporting.err_typ l (Type_error.string_of_type_error err))
  in
  let check_pat pat =
    prerr_endline ("CHECKING PAT: " ^ string_of_pat pat ^ " : " ^ string_of_typ (typ_of_pat pat));
    let _, _ = bind_pat_no_guard (env_of_pat pat) (strip_pat pat) (typ_of_pat pat) in
    pat
  in

  let rewrite_exp = { id_exp_alg with
    e_aux = (fun (exp, annot) -> check_annot (E_aux (exp, annot)));
    pat_alg = { id_pat_alg with p_aux = (fun (pat, annot) -> check_pat (P_aux (pat, annot))) } } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp);
                                          rewrite_pat = (fun _ -> check_pat) }

let rewrite_defs_check = [
  ("check_annotations", rewrite_check_annot);
  ]
