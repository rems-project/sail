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

let find_properties (Defs defs) =
  let rec find_prop acc = function
    | DEF_pragma (("property" | "counterexample") as prop_type, command, l) :: defs ->
       begin match Util.find_next (function DEF_spec _ -> true | _ -> false) defs with
       | _, Some (DEF_spec vs, defs) ->
          find_prop ((prop_type, command, l, vs) :: acc) defs
       | _, _ ->
          raise (Reporting.err_general l "Property is not attached to any function signature")
       end
    | def :: defs -> find_prop acc defs
    | [] -> acc
  in
  find_prop [] defs
  |> List.map (fun ((_, _, _, vs) as prop) -> (id_of_val_spec vs, prop))
  |> List.fold_left (fun m (id, prop) -> Bindings.add id prop m) Bindings.empty

let add_property_guards props (Defs defs) =
  let open Type_check in
  let rec add_property_guards' acc = function
    | (DEF_fundef (FD_aux (FD_function (r_opt, t_opt, e_opt, funcls), fd_aux) as fdef) as def) :: defs ->
       begin match Bindings.find_opt (id_of_fundef fdef) props with
       | Some (_, _, pragma_l, VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (quant, _), _), _, _, _), _)) ->
          begin match quant_split quant with
          | _, [] -> add_property_guards' (def :: acc) defs
          | _, constraints ->
             let add_constraints_to_funcl (FCL_aux (FCL_Funcl (id, Pat_aux (pexp, pexp_aux)), fcl_aux)) =
               let add_guard exp =
                 (* FIXME: Use an assert *)
                 let exp' = mk_exp (E_if (mk_exp (E_constraint (List.fold_left nc_and nc_true constraints)),
                                          strip_exp exp,
                                          mk_lit_exp L_true)) in
                 try Type_check.check_exp (env_of exp) exp' (typ_of exp) with
                 | Type_error (_, l, err) ->
                    let msg =
                      "\nType error when generating guard for a property.\n\
                       When generating guards we convert type quantifiers from the function signature\n\
                       into runtime checks so it must be possible to reconstruct the quantifier from\n\
                       the function arguments. For example:\n\n\
                       \
                       function f : forall 'n, 'n <= 100. (x: int('n)) -> bool\n\n\
                       \
                       would cause the runtime check x <= 100 to be added to the function body.\n\
                       To fix this error, ensure that all quantifiers have corresponding function arguments.\n"
                    in
                    raise (Reporting.err_typ pragma_l (Type_error.string_of_type_error err ^ msg))
               in
               let mk_funcl p = FCL_aux (FCL_Funcl (id, Pat_aux (p, pexp_aux)), fcl_aux) in
               match pexp with
               | Pat_exp (pat, exp) ->
                  mk_funcl (Pat_exp (pat, add_guard exp))
               | Pat_when (pat, guard, exp) ->
                  mk_funcl (Pat_when (pat, guard, add_guard exp))
             in

             let funcls = List.map add_constraints_to_funcl funcls in
             let fdef = FD_aux (FD_function (r_opt, t_opt, e_opt, funcls), fd_aux) in

             add_property_guards' (DEF_fundef fdef :: acc) defs
          end
       | None -> add_property_guards' (def :: acc) defs
       end

    | def :: defs -> add_property_guards' (def :: acc) defs
    | [] -> List.rev acc
  in
  Defs (add_property_guards' [] defs)

let rewrite defs =
  add_property_guards (find_properties defs) defs
