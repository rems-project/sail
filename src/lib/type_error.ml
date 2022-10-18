(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Util
open Ast
open Ast_defs
open Ast_util
open Type_check

type suggestion =
  | Suggest_add_constraint of n_constraint
  | Suggest_none

let analyze_unresolved_quant locals ncs = function
  | QI_aux (QI_constraint nc, _) ->
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
       let nc = List.fold_left (fun nc (v, nexp) -> constraint_subst v (arg_nexp nexp) nc) nc substs in
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
         let nc = List.fold_left (fun nc (v, nexp, _) -> constraint_subst v (arg_nexp nexp) nc) nc substs in
         if not (KidSet.exists is_kid_generated (tyvars_of_constraint nc)) then
           Suggest_none
         else
           Suggest_none

  | QI_aux (QI_id _, _) ->
     Suggest_none

let readable_name (Kid_aux (Var str, l)) =
  Kid_aux (Var (String.concat "" (String.split_on_char '#' str)), l)

let error_string_of_kid substs kid =
  match KBindings.find_opt kid substs with
  | Some nexp -> string_of_nexp nexp
  | None -> string_of_kid kid

let error_string_of_nexp substs nexp =
  string_of_nexp (subst_kids_nexp substs nexp)

let error_string_of_nc substs nexp =
  string_of_n_constraint (subst_kids_nc substs nexp)
  
let error_string_of_typ substs typ =
  string_of_typ (subst_kids_typ substs typ)
  
let message_of_type_error =
  let open Error_format in
  let rec msg = function
    | Err_inner (err, l', prefix, err') ->
       Seq [msg err;
            Line "";
            Location (Util.((prefix ^ " ") |> yellow |> clear), None, l', msg err')]

    | Err_other str -> Line str

    | Err_no_overloading (id, errs) ->
       Seq [Line ("No overloading for " ^ string_of_id id ^ ", tried:");
            List (List.map (fun (id, err) -> string_of_id id, msg err) errs)]

    | Err_unresolved_quants (id, quants, locals, ncs) ->
       Seq [Line ("Could not resolve quantifiers for " ^ string_of_id id);
            Line (bullet ^ " " ^ Util.string_of_list ("\n" ^ bullet ^ " ") string_of_quant_item quants)]

    | Err_failed_constraint (check, locals, ncs) ->
       Line ("Failed to prove constraint: " ^ string_of_n_constraint check)

    | Err_subtype (typ1, typ2, nc, all_constraints, all_vars) ->
       let nc_vars = match nc with Some nc -> tyvars_of_constraint nc | None -> KidSet.empty in
       let vars =
         KBindings.bindings all_vars
         |> List.filter (fun (v, _) -> is_kid_generated v && KidSet.mem v (KidSet.union nc_vars (KidSet.union (tyvars_of_typ typ1) (tyvars_of_typ typ2)))) in
       let var_constraints = List.map (fun (v, l) -> (v, l, List.filter (fun nexp-> KidSet.mem v (tyvars_of_constraint nexp)) all_constraints)) vars in

       let substs =
         List.fold_left (fun (substs, new_vars) (v, _) ->
             if is_kid_generated v then
               let v' = readable_name v in
               if not (KBindings.mem v' all_vars) && not (KidSet.mem v' new_vars) then
                 (KBindings.add v (nvar v') substs, KidSet.add v' new_vars)
               else
                 (substs, new_vars)
             else
               (substs, new_vars)
           ) (KBindings.empty, KidSet.empty) vars
         |> fst in
       
       let format_var_constraints l =
         function
         | [] -> Seq []
         | [nc] -> Line ("satisfies constraint: " ^ error_string_of_nc substs nc)
         | ncs -> Seq (Line "satisfies constraints:"
                       :: List.map (fun nc -> Line (error_string_of_nc substs nc)) ncs)
       in
       With ((fun ppf -> { ppf with loc_color = Util.yellow }),
             Seq (Line (error_string_of_typ substs typ1 ^ " is not a subtype of " ^ error_string_of_typ substs typ2)
                  :: (match nc with Some nc -> [Line ("as " ^ error_string_of_nc substs nc ^ " could not be proven")] | None -> [])
                  @ List.map (fun (v, l, ncs) ->
                        Seq [Line "";
                             Line ("Variable " ^ error_string_of_kid substs v ^ ":");
                             Location ("", Some "bound here", l, format_var_constraints l ncs)])
                      var_constraints))

  | Err_no_num_ident id ->
     Line ("No num identifier " ^ string_of_id id)

  | Err_no_casts (exp, typ_from, typ_to, trigger, reasons) ->
     let coercion =
       Line ("Tried performing type coercion from " ^ string_of_typ typ_from
             ^ " to " ^ string_of_typ typ_to
             ^ " on " ^ string_of_exp exp)
     in
     Seq ([coercion; Line "Coercion failed because:"; msg trigger]
          @ if not (reasons = []) then
              Line "Possible reasons:" :: List.map msg reasons
            else
              [])
  in
  msg

let string_of_type_error err =
  let open Error_format in
  let b = Buffer.create 20 in
  format_message (message_of_type_error err) (buffer_formatter b);
  Buffer.contents b

let rec collapse_errors = function
  | (Err_no_overloading (_, errs) as no_collapse) ->
     let errs = List.map (fun (_, err) -> collapse_errors err) errs in
     let interesting = function
       | Err_other _ -> false
       | Err_no_casts _ -> false
       | _ -> true
     in
     begin match List.filter interesting errs with
     | err :: errs ->
        let fold_equal msg err =
          match msg, err with
          | Some msg, Err_no_overloading _ -> Some msg
          | Some msg, Err_no_casts _ -> Some msg
          | Some msg, err when msg = string_of_type_error err -> Some msg
          | _, _ -> None
        in
        begin match List.fold_left fold_equal (Some (string_of_type_error err)) errs with
        | Some _ -> err
        | None -> no_collapse
        end
     | [] -> no_collapse
     end
  | Err_inner (err1, l, prefix, err2) ->
     let err1 = collapse_errors err1 in
     let err2 = collapse_errors err2 in
     if string_of_type_error err1 = string_of_type_error err2 then
       err1
     else
       Err_inner (err1, l, prefix, err2)
  | err -> err

let check_defs : 'a. Env.t -> 'a def list -> tannot def list * Env.t =
  fun env defs ->
  try Type_check.check_defs env defs with
  | Type_error (env, l, err) ->
     raise (Reporting.err_typ l (string_of_type_error err))
         
let check : 'a. Env.t -> 'a ast -> tannot ast * Env.t =
  fun env defs ->
  try Type_check.check env defs with
  | Type_error (env, l, err) -> raise (Reporting.err_typ l (string_of_type_error err))
