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
open Slice

module NG = Graph.Make(Node)
module NodeSet = NG.NS

let global_effect_order ast =
  let callgraph = graph_of_ast ast in
  let effect_order = NG.topsort_condensed (NG.reverse callgraph) in
  List.map (fun scc ->
      scc,
      List.fold_left (fun deps node_in_scc ->
          NodeSet.union deps (NG.reachable (NodeSet.singleton node_in_scc) NodeSet.empty callgraph)
        ) NodeSet.empty (NodeSet.elements scc)
    ) effect_order

let global_effect_inference (Defs defs) =
  let open Rewriter in
  let rec fundefs = function
    | DEF_fundef fdef :: defs -> Bindings.add (id_of_fundef fdef) fdef (fundefs defs)
    | _ :: defs -> fundefs defs
    | [] -> Bindings.empty
  in
  (* Compute just the effects introduced by each function, without
     considering the effects of any functions they call *)
  let fold_funcl_pexp alg (FCL_aux (FCL_Funcl (_, pexp), _)) = fold_pexp alg pexp in
  let fold_function_pexps alg (FD_aux (FD_function (_, _, _, funcls), _)) = List.map (fold_funcl_pexp alg) funcls in
  let fundef_self_effect fdef =
    fold_function_pexps { (pure_algebra no_effect union_effects) with e_aux = (fun (_, (_, annot)) -> Type_check.effect_of_annot annot) } fdef
    |> List.fold_left union_effects no_effect
  in
  let fundef_self_effects = Bindings.map fundef_self_effect (fundefs defs) in

  (* Now we get the effect order, i.e. a topologically sorted list of
     AST reverse callgraph strongly-connected-components (SCCs), where
     each SCC is mapped to a set of all it's callees *)
  let global_effects = ref Bindings.empty in
  let effect_order = global_effect_order (Defs defs) in
  List.iter (fun (scc, callees) ->
      (* Effects directly introduced by the mutually recursive functions in the SCC *)
      let scc_self_effects =
        List.fold_left (fun eff n ->
            union_effects eff (Util.option_default no_effect (Bindings.find_opt (node_id n) fundef_self_effects))
          ) no_effect (NodeSet.elements scc) in
      (* The cumulative effects for each callee should already be in global effects *)
      let callee_effects =
        List.fold_left (fun eff n ->
            union_effects eff (Util.option_default no_effect (Bindings.find_opt (node_id n) !global_effects))
          ) no_effect (NodeSet.elements callees) in
      List.iter (function
          | Function id -> global_effects := Bindings.add id (union_effects scc_self_effects callee_effects) !global_effects
          | _ -> ()
        ) (NodeSet.elements scc)
    ) effect_order;
  !global_effects
