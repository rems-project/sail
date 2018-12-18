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

open PPrint
open Util
open Ast
open Ast_util
open Type_check

let bullet f xs =
  group (separate_map hardline (fun x -> string "* " ^^ nest 2 (f x)) xs)

let pp_nexp, pp_n_constraint =
  let pp_nexp' nexp =
    string (string_of_nexp nexp)
  in

  let pp_n_constraint' nc =
    string (string_of_n_constraint nc)
  in
  pp_nexp', pp_n_constraint'

let rec nexp_subst sv subst (Nexp_aux (nexp, l)) = Nexp_aux (nexp_subst_aux sv subst nexp, l)
and nexp_subst_aux sv subst = function
  | Nexp_id v -> Nexp_id v
  | Nexp_var kid -> if Kid.compare kid sv = 0 then subst else Nexp_var kid
  | Nexp_constant c -> Nexp_constant c
  | Nexp_times (nexp1, nexp2) -> Nexp_times (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_sum (nexp1, nexp2) -> Nexp_sum (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_minus (nexp1, nexp2) -> Nexp_minus (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_app (id, nexps) -> Nexp_app (id, List.map (nexp_subst sv subst) nexps)
  | Nexp_exp nexp -> Nexp_exp (nexp_subst sv subst nexp)
  | Nexp_neg nexp -> Nexp_neg (nexp_subst sv subst nexp)

let rec nexp_set_to_or l subst = function
  | [] -> typ_error l "Cannot substitute into empty nexp set"
  | [int] -> NC_equal (subst, nconstant int)
  | (int :: ints) -> NC_or (mk_nc (NC_equal (subst, nconstant int)), mk_nc (nexp_set_to_or l subst ints))

let rec nc_subst_nexp sv subst (NC_aux (nc, l)) = NC_aux (nc_subst_nexp_aux l sv subst nc, l)
and nc_subst_nexp_aux l sv subst = function
  | NC_equal (n1, n2) -> NC_equal (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_ge (n1, n2) -> NC_bounded_ge (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_le (n1, n2) -> NC_bounded_le (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_not_equal (n1, n2) -> NC_not_equal (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_set (kid, ints) as set_nc ->
     if Kid.compare kid sv = 0
     then nexp_set_to_or l (mk_nexp subst) ints
     else set_nc
  | NC_or (nc1, nc2) -> NC_or (nc_subst_nexp sv subst nc1, nc_subst_nexp sv subst nc2)
  | NC_and (nc1, nc2) -> NC_and (nc_subst_nexp sv subst nc1, nc_subst_nexp sv subst nc2)
  | NC_false -> NC_false
  | NC_true -> NC_true

type suggestion =
  | Suggest_add_constraint of n_constraint
  | Suggest_none

(* Temporary hack while I work on using these suggestions in asl_parser *)
let rec analyze_unresolved_quant2 locals ncs = function
  | QI_aux (QI_const nc, _) ->
     let gen_kids = List.filter is_kid_generated (KidSet.elements (tyvars_of_constraint nc)) in
     if gen_kids = [] then
       Suggest_add_constraint nc
     else
       (* If there are generated kind-identifiers in the constraint,
          we don't want to make a suggestion based on them, so try to
          look for generated kid free nexps in the set of constraints
          that are equal to the generated identifier. This often
          occurs due to how the type-checker introduces new type
          variables. *)
       let is_subst v = function
         | NC_aux (NC_equal (Nexp_aux (Nexp_var v', _), nexp), _)
              when Kid.compare v v' = 0 && not (KidSet.exists is_kid_generated (tyvars_of_nexp nexp)) ->
            [(v, nexp)]
         | NC_aux (NC_equal (nexp, Nexp_aux (Nexp_var v', _)), _)
              when Kid.compare v v' = 0 && not (KidSet.exists is_kid_generated (tyvars_of_nexp nexp)) ->
            [(v, nexp)]
         | _ -> []
       in
       let substs = List.concat (List.map (fun v -> List.concat (List.map (fun nc -> is_subst v nc) ncs)) gen_kids) in
       let nc = List.fold_left (fun nc (v, nexp) -> nc_subst_nexp v (unaux_nexp nexp) nc) nc substs in
       if not (KidSet.exists is_kid_generated (tyvars_of_constraint nc)) then
         Suggest_add_constraint nc
       else
         (* If we have a really anonymous type-variable, try to find a
            regular variable that corresponds to it. *)
         let is_linked v = function
           | (id, (Immutable, (Typ_aux (Typ_app (ty_id, [A_aux (A_nexp (Nexp_aux (Nexp_var v', _)), _)]), _) as typ)))
                when Id.compare ty_id (mk_id "atom") = 0 && Kid.compare v v' = 0 ->
              [(v, nid id, typ)]
           | (id, (mut, typ)) ->
              []
         in
         let substs = List.concat (List.map (fun v -> List.concat (List.map (fun nc -> is_linked v nc) (Bindings.bindings locals))) gen_kids) in
         let nc = List.fold_left (fun nc (v, nexp, _) -> nc_subst_nexp v (unaux_nexp nexp) nc) nc substs in
         if not (KidSet.exists is_kid_generated (tyvars_of_constraint nc)) then
           Suggest_none
         else
           Suggest_none

  | QI_aux (QI_id kopt, _) ->
     Suggest_none

let rec analyze_unresolved_quant locals ncs = function
  | QI_aux (QI_const nc, _) ->
     let gen_kids = List.filter is_kid_generated (KidSet.elements (tyvars_of_constraint nc)) in
     if gen_kids = [] then
       string ("Try adding the constraint: " ^ string_of_n_constraint nc)
     else
       (* If there are generated kind-identifiers in the constraint,
          we don't want to make a suggestion based on them, so try to
          look for generated kid free nexps in the set of constraints
          that are equal to the generated identifier. This often
          occurs due to how the type-checker introduces new type
          variables. *)
       let is_subst v = function
         | NC_aux (NC_equal (Nexp_aux (Nexp_var v', _), nexp), _)
              when Kid.compare v v' = 0 && not (KidSet.exists is_kid_generated (tyvars_of_nexp nexp)) ->
            [(v, nexp)]
         | NC_aux (NC_equal (nexp, Nexp_aux (Nexp_var v', _)), _)
              when Kid.compare v v' = 0 && not (KidSet.exists is_kid_generated (tyvars_of_nexp nexp)) ->
            [(v, nexp)]
         | _ -> []
       in
       let substs = List.concat (List.map (fun v -> List.concat (List.map (fun nc -> is_subst v nc) ncs)) gen_kids) in
       let nc = List.fold_left (fun nc (v, nexp) -> nc_subst_nexp v (unaux_nexp nexp) nc) nc substs in
       if not (KidSet.exists is_kid_generated (tyvars_of_constraint nc)) then
         string ("Try adding the constraint " ^ string_of_n_constraint nc)
       else
         (* If we have a really anonymous type-variable, try to find a
            regular variable that corresponds to it. *)
         let is_linked v = function
           | (id, (Immutable, (Typ_aux (Typ_app (ty_id, [A_aux (A_nexp (Nexp_aux (Nexp_var v', _)), _)]), _) as typ)))
                when Id.compare ty_id (mk_id "atom") = 0 && Kid.compare v v' = 0 ->
              [(v, nid id, typ)]
           | (id, (mut, typ)) ->
              []
         in
         let substs = List.concat (List.map (fun v -> List.concat (List.map (fun nc -> is_linked v nc) (Bindings.bindings locals))) gen_kids) in
         (string "Try adding named type variables for"
          ^//^ string (Util.string_of_list ", " (fun (_, nexp, typ) -> string_of_nexp nexp ^ " : " ^ string_of_typ typ) substs))
         ^^ twice hardline ^^
         let nc = List.fold_left (fun nc (v, nexp, _) -> nc_subst_nexp v (unaux_nexp nexp) nc) nc substs in
         if not (KidSet.exists is_kid_generated (tyvars_of_constraint nc)) then
           string ("The property " ^ string_of_n_constraint nc ^ " must hold")
         else
           empty

  | QI_aux (QI_id kopt, _) ->
     empty

let rec pp_type_error = function
  | Err_no_casts (exp, typ_from, typ_to, trigger, reasons) ->
     let coercion =
       group (string "Tried performing type coercion from" ^/^ Pretty_print_sail.doc_typ typ_from
              ^/^ string "to" ^/^ Pretty_print_sail.doc_typ typ_to
              ^/^ string "on" ^/^ Pretty_print_sail.doc_exp exp)
     in
     coercion ^^ hardline
     ^^ (string "Coercion failed because:" ^//^ pp_type_error trigger)
     ^^ if not (reasons = []) then
          hardline
          ^^ (string "Possible reasons:" ^//^ separate_map hardline pp_type_error reasons)
        else
          empty

  | Err_no_overloading (id, errs) ->
     string ("No overloadings for " ^ string_of_id id ^ ", tried:") ^//^
       group (separate_map hardline (fun (id, err) -> string (string_of_id id) ^^ colon ^//^ pp_type_error err) errs)

  | Err_subtype (typ1, typ2, constrs, locs) ->
     (separate space [ string (string_of_typ typ1);
                       string "is not a subtype of";
                       string (string_of_typ typ2) ])
     ^/^ string "in context"
     ^/^ bullet pp_n_constraint constrs
     ^/^ string "where"
     ^/^ bullet (fun (kid, l) -> string (string_of_kid kid ^ " bound at " ^ Reporting.loc_to_string l ^ "\n")) (KBindings.bindings locs)

  | Err_no_num_ident id ->
     string "No num identifier" ^^ space ^^ string (string_of_id id)

  | Err_unresolved_quants (id, quants, locals, ncs) ->
     (string "Could not resolve quantifiers for" ^^ space ^^ string (string_of_id id)
      ^//^ group (separate_map hardline (fun quant -> string (string_of_quant_item quant)) quants))
     ^^ twice hardline
     ^^ group (separate_map hardline (analyze_unresolved_quant locals ncs) quants)

  (* We only got err, because of previous error, err' *)
  | Err_because (err, err') ->
     pp_type_error err
     ^^ hardline ^^ string "This error occured because of a previous error:"
     ^//^ pp_type_error err'
    
  | Err_other str -> string str

let rec string_of_type_error err =
  let open PPrint in
  let b = Buffer.create 20 in
  ToBuffer.pretty 1. 400 b (pp_type_error err);
  "\n" ^ Buffer.contents b

let rec collapse_errors = function
  | (Err_no_overloading (_, (err :: errs)) as no_collapse) ->
      let err = collapse_errors (snd err) in
      let errs = List.map (fun (_, err) -> collapse_errors err) errs in
      let fold_equal msg err =
        match msg, err with
        | Some msg, Err_no_overloading _ -> Some msg
        | Some msg, Err_other _ -> Some msg
        | Some msg, Err_no_casts _ -> Some msg
        | Some msg, err when msg = string_of_type_error err -> Some msg
        | _, _ -> None
      in
      begin match List.fold_left fold_equal (Some (string_of_type_error err)) errs with
      | Some _ -> err
      | None -> no_collapse
      end
  | err -> err

let check : 'a. Env.t -> 'a defs -> tannot defs * Env.t =
  fun env defs ->
  try Type_check.check env defs with
  | Type_error (l, err) -> raise (Reporting.err_typ l (string_of_type_error err))
