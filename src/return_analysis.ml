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
open Ast_util
open Type_check

let analyze_exp_returns exp =
  let returns = ref [] in
  let add_return annot = returns := annot :: !returns in

  print_endline ("\nAnalyzing " ^ string_of_exp exp);

  let rec analyze last (E_aux (e_aux, annot)) =
    let env = env_of_annot annot in
    match e_aux with
    | E_block exps ->
       begin match List.rev exps with
       | [] -> ()
       | (exp :: exps) ->
          List.iter (analyze false) exps;
          analyze last exp
       end

    | E_nondet exps -> List.iter (analyze last) exps

    | E_id id ->
       if last then
         add_return annot
       else
         ()

    | E_lit _ when last ->
       add_return annot

    | E_app _  when last ->
       add_return annot
    | E_app (_, exps) ->
       List.iter (analyze false) exps

    | E_if (_, then_exp, else_exp) ->
       analyze last then_exp; analyze last else_exp

    | E_return (E_aux (_, annot)) ->
       add_return annot

    | E_for (_, exp1, exp2, exp3, _, body) ->
       analyze false exp1; analyze false exp2; analyze false exp3;
       analyze last body

    | _ -> ()
  in
  analyze true exp;

  !returns

type existential =
  | Equal of nexp
  | Constraint of (kid -> n_constraint)
  | Anything

let existentialize_annot funcl_annot annot =
  let funcl_env = env_of_annot funcl_annot in
  let env = env_of_annot annot in
  match Env.expand_synonyms env (typ_of_annot annot) with
  | (Typ_aux (Typ_app (ty_id, [A_aux (A_nexp nexp, _)]), _) as typ)
       when Id.compare ty_id (mk_id "atom") = 0 ->
     let tyvars = Env.get_typ_vars funcl_env |> KBindings.bindings in
     let toplevel_kids =
       List.filter (fun (kid, k) -> match k with K_int -> true | _ -> false) tyvars |> List.map fst |> KidSet.of_list
     in
     let new_kids = KidSet.diff (tyvars_of_nexp nexp) toplevel_kids in

     if KidSet.cardinal new_kids = 0 then
       Some (Equal nexp)
     else if KidSet.cardinal new_kids = 1 then
       let ex_kid = KidSet.min_elt new_kids in
       (* Now we search for constraints that involve the existential
          kid, and only reference toplevel type variables. *)
       let constraints = List.concat (List.map constraint_conj (Env.get_constraints env)) in
       let constraints = List.filter (fun nc -> KidSet.mem ex_kid (tyvars_of_constraint nc)) constraints in
       let constraints =
         List.filter (fun nc -> KidSet.subset (tyvars_of_constraint nc) (KidSet.add ex_kid toplevel_kids)) constraints
       in

       match constraints with
       | c :: cs ->
          Some (Constraint (fun kid -> nc_subst_nexp ex_kid (Nexp_var kid) (List.fold_left nc_and c cs)))
       | [] ->
          Some Anything
     else
       Some Anything
  | _ ->
     None

let union_existential ex1 ex2 =
  match ex1, ex2 with
  | Equal nexp1, Equal nexp2 ->
     Constraint (fun kid -> nc_or (nc_eq (nvar kid) nexp1) (nc_eq (nvar kid) nexp2))

  | Equal nexp, Constraint c ->
     Constraint (fun kid -> nc_or (nc_eq (nvar kid) nexp) (c kid))

  | Constraint c, Equal nexp ->
     Constraint (fun kid -> nc_or (c kid) (nc_eq (nvar kid) nexp))

  | _, _ -> Anything

let typ_of_existential = function
  | Anything -> int_typ
  | Equal nexp -> atom_typ nexp
  | Constraint c -> exist_typ c (fun kid -> atom_typ (nvar kid))

let analyze_def_returns = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _)) ->
     let analyze_funcls = function
       | FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (pat, exp), _)), funcl_annot) ->
          let return_exs =
            List.map (fun annot -> existentialize_annot funcl_annot annot) (analyze_exp_returns exp)
          in
          begin match Util.option_all return_exs with
          | Some [] -> ()
          | Some (ex :: exs) ->
             print_endline (string_of_typ (typ_of_existential (List.fold_left union_existential ex exs)))
          | None -> ()
          end

       | _ -> ()
     in
     List.iter analyze_funcls funcls

  | def -> ()

let analyze_returns (Defs defs) = List.iter analyze_def_returns defs

