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
open Rewriter

let is_typ_ord_uvar = function
  | Type_check.U_typ _ -> true
  | Type_check.U_order _ -> true
  | _ -> false

(* We have to be careful about whether the typechecker has renamed anything returned by instantiation_of.
   This part of the typechecker API is a bit ugly. *)
let fix_instantiation instantiation =
  let instantiation = KBindings.bindings (KBindings.filter (fun _ uvar -> is_typ_ord_uvar uvar) instantiation) in
  let instantiation = List.map (fun (kid, uvar) -> Type_check.orig_kid kid, uvar) instantiation in
  List.fold_left (fun m (k, v) -> KBindings.add k v m) KBindings.empty instantiation

let rec polymorphic_functions is_kopt (Defs defs) =
  match defs with
  | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ) , _), id, _, externs), _)) :: defs ->
     let is_type_polymorphic = List.exists is_kopt (quant_kopts typq) in
     if is_type_polymorphic then
       IdSet.add id (polymorphic_functions is_kopt (Defs defs))
     else
       polymorphic_functions is_kopt (Defs defs)
  | _ :: defs -> polymorphic_functions is_kopt (Defs defs)
  | [] -> IdSet.empty

let id_of_instantiation id instantiation =
  let string_of_binding (kid, uvar) = string_of_kid kid ^ " => " ^ Type_check.string_of_uvar uvar in
  let str = Util.zencode_string (Util.string_of_list ", " string_of_binding (KBindings.bindings instantiation)) ^ "#" in
  prepend_id str id

let string_of_instantiation instantiation =
  let string_of_binding (kid, uvar) = string_of_kid kid ^ " => " ^ Type_check.string_of_uvar uvar in
  Util.zencode_string (Util.string_of_list ", " string_of_binding (KBindings.bindings instantiation))

(* Returns a list of all the instantiations of a function id in an
   ast. *)
let rec instantiations_of id ast =
  let instantiations = ref [] in

  let inspect_exp = function
    | E_aux (E_app (id', _), _) as exp when Id.compare id id' = 0 ->
       let instantiation = fix_instantiation (Type_check.instantiation_of exp) in
       instantiations := instantiation :: !instantiations;
       exp
    | exp -> exp
  in

  let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> inspect_exp (E_aux (exp, annot))) } in
  let _ = rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp) } ast in

  !instantiations

let rec rewrite_polymorphic_calls id ast =
  let vs_ids = Initial_check.val_spec_ids ast in

  let rewrite_e_aux = function
    | E_aux (E_app (id', args), annot) as exp when Id.compare id id' = 0 ->
       let instantiation = fix_instantiation (Type_check.instantiation_of exp) in
       let spec_id = id_of_instantiation id instantiation in
       (* Make sure we only generate specialized calls when we've
          specialized the valspec. The valspec may not be generated if
          a polymorphic function calls another polymorphic function.
          In this case a specialization of the first may require that
          the second needs to be specialized again, but this may not
          have happened yet. *)
       if IdSet.mem spec_id vs_ids then
         E_aux (E_app (spec_id, args), annot)
       else
         exp
    | exp -> exp
  in

  let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> rewrite_e_aux (E_aux (exp, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp) } ast

let rec typ_frees ?exs:(exs=KidSet.empty) (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_id v -> KidSet.empty
  | Typ_var kid when KidSet.mem kid exs -> KidSet.empty
  | Typ_var kid -> KidSet.singleton kid
  | Typ_tup typs -> List.fold_left KidSet.union KidSet.empty (List.map (typ_frees ~exs:exs) typs)
  | Typ_app (f, args) -> List.fold_left KidSet.union KidSet.empty (List.map (typ_arg_frees ~exs:exs) args)
  | Typ_exist (kids, nc, typ) -> typ_frees ~exs:(KidSet.of_list kids) typ
  | Typ_fn (typ1, typ2, _) -> KidSet.union (typ_frees ~exs:exs typ1) (typ_frees ~exs:exs typ2)
and typ_arg_frees ?exs:(exs=KidSet.empty) (Typ_arg_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | Typ_arg_nexp n -> KidSet.empty
  | Typ_arg_typ typ -> typ_frees ~exs:exs typ
  | Typ_arg_order ord -> KidSet.empty

let specialize_id_valspec instantiations id ast =
  match split_defs (is_valspec id) ast with
  | None -> failwith ("Valspec " ^ string_of_id id ^ " does not exist!")
  | Some (pre_ast, vs, post_ast) ->
     let typschm, externs, is_cast, annot = match vs with
       | DEF_spec (VS_aux (VS_val_spec (typschm, _, externs, is_cast), annot)) -> typschm, externs, is_cast, annot
       | _ -> assert false (* unreachable *)
     in
     let TypSchm_aux (TypSchm_ts (typq, typ), _) = typschm in

     (* Keep track of the specialized ids to avoid generating things twice. *)
     let spec_ids = ref IdSet.empty in

     let specialize_instance instantiation =
       (* Replace the polymorphic type variables in the type with their concrete instantiation. *)
       let typ = Type_check.subst_unifiers instantiation typ in
       let frees = KidSet.elements (typ_frees typ) in

       (* Remove type variables from the type quantifier. *)
       let kopts, constraints = quant_split typq in
       let kopts = List.filter (fun kopt -> not (is_typ_kopt kopt || is_order_kopt kopt)) kopts in
       let typq = mk_typquant (List.map (mk_qi_id BK_type) frees @ List.map mk_qi_kopt kopts @ List.map mk_qi_nc constraints) in
       let typschm = mk_typschm typq typ in

       let spec_id = id_of_instantiation id instantiation in

       if IdSet.mem spec_id !spec_ids then [] else
         begin
           spec_ids := IdSet.add spec_id !spec_ids;
           [DEF_spec (VS_aux (VS_val_spec (typschm, spec_id, externs, is_cast), annot))]
         end
     in

     let specializations = List.map specialize_instance instantiations |> List.concat in

     append_ast pre_ast (append_ast (Defs (vs :: specializations)) post_ast)

let specialize_id_fundef instantiations id ast =
  match split_defs (is_fundef id) ast with
  | None -> ast
  | Some (pre_ast, DEF_fundef fundef, post_ast) ->
     let spec_ids = ref IdSet.empty in
     let specialize_fundef instantiation =
       let spec_id = id_of_instantiation id instantiation in
       if IdSet.mem spec_id !spec_ids then [] else
         begin
           spec_ids := IdSet.add spec_id !spec_ids;
           [DEF_fundef (rename_fundef spec_id fundef)]
         end
     in
     let fundefs = List.map specialize_fundef instantiations |> List.concat in
     append_ast pre_ast (append_ast (Defs fundefs) post_ast)
  | Some _ -> assert false (* unreachable *)

let specialize_id_overloads instantiations id (Defs defs) =
  let ids = IdSet.of_list (List.map (id_of_instantiation id) instantiations) in

  let rec rewrite_overloads defs =
    match defs with
    | DEF_overload (overload_id, overloads) :: defs ->
       let overloads = List.concat (List.map (fun id' -> if Id.compare id' id = 0 then IdSet.elements ids else [id']) overloads) in
       DEF_overload (overload_id, overloads) :: rewrite_overloads defs
    | def :: defs -> def :: rewrite_overloads defs
    | [] -> []
  in

  Defs (rewrite_overloads defs)

(* Once we've specialized a definition, it's original valspec should
   be unused, unless another polymorphic function called it. We
   therefore remove all unused valspecs. Remaining polymorphic
   valspecs are then re-specialized. This process is iterated until
   the whole spec is specialized. *)
let remove_unused_valspecs ast =
  let calls = ref (IdSet.of_list [mk_id "main"; mk_id "execute"; mk_id "decode"; mk_id "initialize_registers"]) in
  let vs_ids = Initial_check.val_spec_ids ast in

  let inspect_exp = function
    | E_aux (E_app (call, _), _) as exp ->
       calls := IdSet.add call !calls;
       exp
    | exp -> exp
  in

  let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> inspect_exp (E_aux (exp, annot))) } in
  let _ = rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp) } ast in

  let unused = IdSet.filter (fun vs_id -> not (IdSet.mem vs_id !calls)) vs_ids in

  let rec remove_unused (Defs defs) id =
    match defs with
    | def :: defs when is_fundef id def -> remove_unused (Defs defs) id
    | def :: defs when is_valspec id def -> remove_unused (Defs defs) id
    | DEF_overload (overload_id, overloads) :: defs ->
       begin
         match List.filter (fun id' -> Id.compare id id' <> 0) overloads with
         | [] -> remove_unused (Defs defs) id
         | overloads -> DEF_overload (overload_id, overloads) :: remove_unused (Defs defs) id
       end
    | def :: defs -> def :: remove_unused (Defs defs) id
    | [] -> []
  in

  List.fold_left (fun ast id -> Defs (remove_unused ast id)) ast (IdSet.elements unused)

let specialize_id id ast =
  let instantiations = instantiations_of id ast in

  let ast = specialize_id_valspec instantiations id ast in
  let ast = specialize_id_fundef instantiations id ast in
  specialize_id_overloads instantiations id ast

(* When we generate specialized versions of functions, we need to
   ensure that the types they are specialized to appear before the
   function definitions in the AST. Therefore we pull all the type
   definitions (and default definitions) to the start of the AST. *)
let reorder_typedefs (Defs defs) =
  let tdefs = ref [] in

  let rec filter_typedefs = function
    | (DEF_default _ | DEF_type _) as tdef :: defs ->
       tdefs := tdef :: !tdefs;
       filter_typedefs defs
    | def :: defs -> def :: filter_typedefs defs
    | [] -> []
  in

  let others = filter_typedefs defs in
  Defs (List.rev !tdefs @ others)

let specialize_ids ids ast =
  let ast = List.fold_left (fun ast id -> specialize_id id ast) ast (IdSet.elements ids) in
  let ast = reorder_typedefs ast in
  let ast, _ = Type_check.check Type_check.initial_env ast in
  let ast = List.fold_left (fun ast id -> rewrite_polymorphic_calls id ast) ast (IdSet.elements ids) in
  let ast, env = Type_check.check Type_check.initial_env ast in
  let ast = remove_unused_valspecs ast in
  ast, env

let rec specialize ast env =
  let ids = polymorphic_functions (fun kopt -> is_typ_kopt kopt || is_order_kopt kopt) ast in
  if IdSet.is_empty ids then
    ast, env
  else
    let ast, env = specialize_ids ids ast in
    specialize ast env
