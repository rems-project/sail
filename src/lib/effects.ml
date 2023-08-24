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

open Ast
open Ast_defs
open Ast_util
open Rewriter
open Type_check

type side_effect =
  | Throw
  | Exit
  | IncompleteMatch
  | Register
  | External
  | Undefined
  | Scattered
  | NonExec
  | Outcome of id

let string_of_side_effect = function
  | Throw -> "throws exception"
  | Exit -> "exit statement"
  | IncompleteMatch -> "incomplete pattern match"
  | Register -> "register access"
  | External -> "calls external function not marked pure"
  | Undefined -> "contains undefined literal"
  | Scattered -> "scattered function"
  | NonExec -> "not executable"
  | Outcome id -> "outcome " ^ string_of_id id

module Effect = struct
  type t = side_effect
  let compare e1 e2 =
    match (e1, e2) with
    | Throw, Throw -> 0
    | Exit, Exit -> 0
    | IncompleteMatch, IncompleteMatch -> 0
    | Register, Register -> 0
    | External, External -> 0
    | Undefined, Undefined -> 0
    | Scattered, Scattered -> 0
    | NonExec, NonExec -> 0
    | Outcome id1, Outcome id2 -> Id.compare id1 id2
    | Throw, _ -> 1
    | _, Throw -> -1
    | Exit, _ -> 1
    | _, Exit -> -1
    | IncompleteMatch, _ -> 1
    | _, IncompleteMatch -> -1
    | External, _ -> 1
    | _, External -> -1
    | Undefined, _ -> 1
    | _, Undefined -> -1
    | Scattered, _ -> 1
    | _, Scattered -> -1
    | NonExec, _ -> 1
    | _, NonExec -> -1
    | Outcome _, _ -> 1
    | _, Outcome _ -> -1
end

module EffectSet = Set.Make (Effect)

let throws = EffectSet.mem Throw

let non_exec = EffectSet.mem NonExec

let pure = EffectSet.is_empty

let effectful set = not (pure set)

let has_outcome id = EffectSet.mem (Outcome id)

module PC_config = struct
  type t = tannot
  let typ_of_t = Type_check.typ_of_tannot
  let add_attribute l attr arg = Type_check.map_uannot (add_attribute l attr arg)
end

module PC = Pattern_completeness.Make (PC_config)

let funcls_info = function
  | FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (pat, _), _)), _) :: _ -> Some (id, typ_of_pat pat, env_of_pat pat)
  | FCL_aux (FCL_funcl (id, Pat_aux (Pat_when (pat, _, _), _)), _) :: _ -> Some (id, typ_of_pat pat, env_of_pat pat)
  | _ -> None

let infer_def_direct_effects asserts_termination def =
  let effects = ref EffectSet.empty in

  let scan_lexp lexp_aux annot =
    let env = env_of_annot annot in
    begin
      match lexp_aux with
      | LE_typ (_, id) | LE_id id -> begin
          match Env.lookup_id id env with Register _ -> effects := EffectSet.add Register !effects | _ -> ()
        end
      | LE_deref _ -> effects := EffectSet.add Register !effects
      | _ -> ()
    end;
    LE_aux (lexp_aux, annot)
  in

  let scan_exp e_aux annot =
    let env = env_of_annot annot in
    begin
      match e_aux with
      | E_id id -> begin
          match Env.lookup_id id env with Register _ -> effects := EffectSet.add Register !effects | _ -> ()
        end
      | E_lit (L_aux (L_undef, _)) -> effects := EffectSet.add Undefined !effects
      | E_throw _ -> effects := EffectSet.add Throw !effects
      | E_exit _ | E_assert _ -> effects := EffectSet.add Exit !effects
      | E_app (f, _) when Id.compare f (mk_id "__deref") = 0 -> effects := EffectSet.add Register !effects
      | E_match (_, _) ->
          if Option.is_some (snd annot |> untyped_annot |> get_attribute "incomplete") then
            effects := EffectSet.add IncompleteMatch !effects
      | E_loop (_, Measure_aux (Measure_some _, _), _, _) when asserts_termination ->
          effects := EffectSet.add Exit !effects
      | _ -> ()
    end;
    E_aux (e_aux, annot)
  in

  let scan_pat p_aux annot =
    begin
      match p_aux with P_string_append _ -> effects := EffectSet.add NonExec !effects | _ -> ()
    end;
    P_aux (p_aux, annot)
  in

  let pat_alg = { id_pat_alg with p_aux = (fun (p_aux, annot) -> scan_pat p_aux annot) } in

  let rw_exp _ exp =
    fold_exp
      {
        id_exp_alg with
        e_aux = (fun (e_aux, annot) -> scan_exp e_aux annot);
        le_aux = (fun (l_aux, annot) -> scan_lexp l_aux annot);
        pat_alg;
      }
      exp
  in
  ignore (rewrite_ast_defs { rewriters_base with rewrite_exp = rw_exp; rewrite_pat = (fun _ -> fold_pat pat_alg) } [def]);

  begin
    match def with
    | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, Some { pure = false; _ }), _)), _) ->
        effects := EffectSet.add External !effects
    | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, funcls), (l, _))), def_annot) -> begin
        match funcls_info funcls with
        | Some (id, typ, env) ->
            if Option.is_some (get_def_attribute "incomplete" def_annot) then
              effects := EffectSet.add IncompleteMatch !effects
        | None -> Reporting.unreachable l __POS__ "Empty funcls in infer_def_direct_effects"
      end
    | DEF_aux (DEF_mapdef _, _) -> effects := EffectSet.add IncompleteMatch !effects
    | DEF_aux (DEF_scattered _, _) -> effects := EffectSet.add Scattered !effects
    | _ -> ()
  end;

  !effects

let infer_mapdef_extra_direct_effects def =
  let forward_effects = ref EffectSet.empty in
  let backward_effects = ref EffectSet.empty in

  let scan_mpat set mp_aux annot =
    match mp_aux with
    | Some (MP_string_append _ as aux) ->
        set := EffectSet.add NonExec !set;
        Some (MP_aux (aux, annot))
    | Some aux -> Some (MP_aux (aux, annot))
    | None -> None
  in
  let rw_mpat set = fold_mpat { id_mpat_alg with p_aux = (fun (mp_aux, annot) -> scan_mpat set mp_aux annot) } in
  let scan_mpexp set (MPat_aux (aux, _)) =
    match aux with MPat_pat mpat -> ignore (rw_mpat set mpat) | MPat_when (mpat, _) -> ignore (rw_mpat set mpat)
  in
  let scan_mapcl (MCL_aux (aux, _)) =
    match aux with
    | MCL_bidir (forward, backward) ->
        scan_mpexp forward_effects forward;
        scan_mpexp backward_effects backward
    | MCL_forwards (forward, _) -> scan_mpexp forward_effects forward
    | MCL_backwards (backward, _) -> scan_mpexp backward_effects backward
  in

  begin
    match def with
    | DEF_aux (DEF_mapdef (MD_aux (MD_mapping (_, _, mapcls), _)), _) -> List.iter scan_mapcl mapcls
    | _ -> ()
  end;

  (!forward_effects, !backward_effects)

(* A top-level definition can have a side effect if it contains an
   expression which could have some side effect *)
let can_have_direct_side_effect (DEF_aux (aux, _)) =
  match aux with
  | DEF_type _ -> false
  | DEF_fundef _ -> true
  | DEF_mapdef _ -> false
  | DEF_impl _ -> true
  | DEF_let _ -> true
  | DEF_val _ -> true
  | DEF_outcome _ -> true
  | DEF_instantiation _ -> false
  | DEF_fixity _ -> false
  | DEF_overload _ -> false
  | DEF_default _ -> false
  | DEF_scattered _ -> true
  | DEF_measure _ -> true
  | DEF_loop_measures _ -> true
  | DEF_register _ -> true
  | DEF_internal_mutrec _ -> true
  | DEF_pragma _ -> false

type side_effect_info = {
  functions : EffectSet.t Bindings.t;
  letbinds : EffectSet.t Bindings.t;
  mappings : EffectSet.t Bindings.t;
}

let empty_side_effect_info = { functions = Bindings.empty; letbinds = Bindings.empty; mappings = Bindings.empty }

let function_is_pure id info = match Bindings.find_opt id info.functions with Some eff -> pure eff | None -> true

let is_function = function Callgraph.Function _ -> true | _ -> false

let is_mapping = function Callgraph.Mapping _ -> true | _ -> false

(* Normally we only add effects once, but occasionally we need to add
   more (e.g., if a function is external for some targets, but defined
   in Sail for others). *)
let add_effects id effect_set effect_map =
  Bindings.update id
    (function Some effects -> Some (EffectSet.union effects effect_set) | None -> Some effect_set)
    effect_map

let infer_side_effects asserts_termination ast =
  let module NodeSet = Set.Make (Callgraph.Node) in
  let cg = Callgraph.graph_of_ast ast in

  let total = List.length ast.defs in
  let direct_effects = ref Bindings.empty in
  let fun_termination_asserts = ref IdSet.empty in
  let infer_fun_termination_assert def =
    if asserts_termination then (
      match def with
      | DEF_aux (DEF_measure (id, _, _), _) -> fun_termination_asserts := IdSet.add id !fun_termination_asserts
      | _ -> ()
    )
  in
  List.iteri
    (fun i def ->
      Util.progress "Effects (direct) " (string_of_int (i + 1) ^ "/" ^ string_of_int total) (i + 1) total;
      (* Handle mapping separately to allow different effects for both directions *)
      begin
        match def with
        | DEF_aux (DEF_mapdef mdef, _) ->
            let effs = infer_def_direct_effects asserts_termination def in
            let fw, bk = infer_mapdef_extra_direct_effects def in
            let id = id_of_mapdef mdef in
            direct_effects := add_effects id effs !direct_effects;
            direct_effects := add_effects (append_id id "_forwards") fw !direct_effects;
            direct_effects := add_effects (append_id id "_backwards") bk !direct_effects
        | _ when can_have_direct_side_effect def ->
            infer_fun_termination_assert def;
            let effs = infer_def_direct_effects asserts_termination def in
            let ids = ids_of_def def in
            IdSet.iter (fun id -> direct_effects := add_effects id effs !direct_effects) ids
        | _ -> ()
      end
    )
    ast.defs;

  (* If asserts_termination is true then we will have a set of
     recursive functions where the target will assert that the
     termination measure is respected, so add suitable effects for the
     assert.  While loops are handled in infer_def_direct_effects
     above. *)
  direct_effects :=
    IdSet.fold (fun id -> add_effects id (EffectSet.singleton Exit)) !fun_termination_asserts !direct_effects;

  let function_effects = ref Bindings.empty in
  let letbind_effects = ref Bindings.empty in
  let mapping_effects = ref Bindings.empty in

  let all_nodes = Callgraph.G.nodes cg in
  let total = List.length all_nodes in
  List.iteri
    (fun i node ->
      Util.progress "Effects (transitive) " (string_of_int (i + 1) ^ "/" ^ string_of_int total) (i + 1) total;
      match node with
      | Callgraph.Function id | Callgraph.Letbind id | Callgraph.Mapping id ->
          let reachable = Callgraph.G.reachable (NodeSet.singleton node) NodeSet.empty cg in
          (* First, a function has any side effects it directly causes *)
          let side_effects =
            match Bindings.find_opt id !direct_effects with Some effs -> effs | None -> EffectSet.empty
          in
          (* Second, a function has any side effects from any reachable callee function *)
          let side_effects =
            NodeSet.fold
              (fun node side_effects ->
                match Bindings.find_opt (Callgraph.node_id node) !direct_effects with
                | Some effs -> EffectSet.union effs side_effects
                | None -> side_effects
              )
              reachable side_effects
          in
          (* Third, if a function or any callee invokes an outcome, it has that effect *)
          let side_effects =
            NodeSet.filter (function Callgraph.Outcome _ -> true | _ -> false) reachable
            |> NodeSet.elements
            |> List.map (fun node -> Outcome (Callgraph.node_id node))
            |> EffectSet.of_list |> EffectSet.union side_effects
          in
          if is_function node then function_effects := Bindings.add id side_effects !function_effects
          else if is_mapping node then mapping_effects := Bindings.add id side_effects !mapping_effects
          else letbind_effects := Bindings.add id side_effects !letbind_effects
      | _ -> ()
    )
    all_nodes;

  { functions = !function_effects; letbinds = !letbind_effects; mappings = !mapping_effects }

let check_side_effects effect_info ast =
  let allowed_nonexec = ref IdSet.empty in
  List.iter
    (fun (DEF_aux (aux, _) as def) ->
      match aux with
      | DEF_pragma ("non_exec", name, _) -> allowed_nonexec := IdSet.add (mk_id name) !allowed_nonexec
      | DEF_let _ ->
          IdSet.iter
            (fun id ->
              match Bindings.find_opt id effect_info.letbinds with
              | Some eff when not (pure eff) ->
                  raise
                    (Reporting.err_general (id_loc id)
                       ("Top-level let statement must not have any side effects. Found side effects: "
                       ^ Util.string_of_list ", " string_of_side_effect (EffectSet.elements eff)
                       )
                    )
              | _ -> ()
            )
            (ids_of_def def)
      | DEF_fundef fdef ->
          let id = id_of_fundef fdef in
          let eff =
            Bindings.find_opt (id_of_fundef fdef) effect_info.functions |> Option.value ~default:EffectSet.empty
          in
          if non_exec eff && not (IdSet.mem id !allowed_nonexec) then
            raise
              (Reporting.err_general (id_loc id)
                 ("Function " ^ string_of_id id ^ " calls function marked non-executable")
              )
      | _ -> ()
    )
    ast.defs

let copy_function_effect id_from effect_info id_to =
  match Bindings.find_opt id_from effect_info.functions with
  | Some eff -> { effect_info with functions = Bindings.add id_to eff effect_info.functions }
  | None -> effect_info

let add_function_effect id_from effect_info id_to =
  match Bindings.find_opt id_from effect_info.functions with
  | Some eff -> { effect_info with functions = add_effects id_to eff effect_info.functions }
  | None -> effect_info

let copy_mapping_to_function id_from effect_info id_to =
  match Bindings.find_opt id_from effect_info.mappings with
  (* Avoid copying the mapping effect to the function if it already
     exists - this likely means the function has been manually
     defined. *)
  | Some eff ->
      let existing_effects =
        match Bindings.find_opt id_to effect_info.functions with
        | Some existing_eff -> existing_eff
        | None -> EffectSet.empty
      in
      { effect_info with functions = Bindings.add id_to (EffectSet.union eff existing_effects) effect_info.functions }
  | _ -> effect_info

let add_monadic_built_in id effect_info =
  { effect_info with functions = add_effects id (EffectSet.singleton External) effect_info.functions }

let rewrite_attach_effects effect_info =
  let rewrite_lexp_aux ((child_eff, lexp_aux), (l, tannot)) =
    let env = env_of_tannot tannot in
    let eff =
      match lexp_aux with
      | LE_typ (_, id) | LE_id id -> begin
          match Env.lookup_id id env with Register _ -> monadic_effect | _ -> no_effect
        end
      | LE_deref _ -> monadic_effect
      | _ -> no_effect
    in
    let eff = union_effects eff child_eff in
    (eff, LE_aux (lexp_aux, (l, add_effect_annot tannot eff)))
  in

  let rewrite_e_aux ((child_eff, e_aux), (l, tannot)) =
    let env = env_of_tannot tannot in
    let eff =
      match e_aux with
      | E_app (f, _) when string_of_id f = "early_return" -> monadic_effect
      | E_app (f, _) -> begin
          match Bindings.find_opt f effect_info.functions with
          | Some side_effects -> if pure side_effects then no_effect else monadic_effect
          | None -> no_effect
        end
      | E_lit (L_aux (L_undef, _)) -> monadic_effect
      | E_id id -> begin match Env.lookup_id id env with Register _ -> monadic_effect | _ -> no_effect end
      | E_throw _ -> monadic_effect
      | E_exit _ | E_assert _ -> monadic_effect
      | _ -> no_effect
    in
    let eff = union_effects eff child_eff in
    (eff, E_aux (e_aux, (l, add_effect_annot tannot eff)))
  in

  let rw_exp =
    fold_exp { (compute_exp_alg no_effect union_effects) with e_aux = rewrite_e_aux; le_aux = rewrite_lexp_aux }
  in
  rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ exp -> snd (rw_exp exp)) }

let string_of_effectset set = String.concat ", " (List.map string_of_side_effect (EffectSet.elements set))

let dump_effect_bindings bindings =
  Bindings.iter (fun id set -> Printf.eprintf "  %s: %s\n%!" (string_of_id id) (string_of_effectset set)) bindings

let dump_effects effect_info =
  prerr_endline "Function effects:";
  dump_effect_bindings effect_info.functions;
  prerr_endline "Letbind effects:";
  dump_effect_bindings effect_info.letbinds;
  prerr_endline "Mapping effects:";
  dump_effect_bindings effect_info.mappings
