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
open Util
open Lazy

module Big_int = Nat_big_num

open Type_internal

let set_tc_debug level = opt_tc_debug := level

(* opt_no_lexp_bounds_check turns off the bounds checking in vector
   assignments in l-expressions *)
let opt_no_lexp_bounds_check = ref false

(* opt_expand_valspec expands typedefs in valspecs during type check.
   We prefer not to do it for latex output but it is otherwise a good idea. *)
let opt_expand_valspec = ref true

(* Don't expand bitfields (when using old syntax), used for LaTeX output *)
let opt_no_bitfield_expansion = ref false

(* Only allow mutable variables to be declared with var *)
let opt_strict_var = ref false

let orig_kid (Kid_aux (Var v, l) as kid) =
  try
    let i = String.rindex v '#' in
    if i >= 3 && String.sub v 0 3 = "'fv" then Kid_aux (Var ("'" ^ String.sub v (i + 1) (String.length v - i - 1)), l)
    else kid
  with Not_found -> kid

(* Rewrite mangled names of type variables to the original names *)
let rec orig_nexp (Nexp_aux (nexp, l)) =
  let rewrap nexp = Nexp_aux (nexp, l) in
  match nexp with
  | Nexp_var kid -> rewrap (Nexp_var (orig_kid kid))
  | Nexp_times (n1, n2) -> rewrap (Nexp_times (orig_nexp n1, orig_nexp n2))
  | Nexp_sum (n1, n2) -> rewrap (Nexp_sum (orig_nexp n1, orig_nexp n2))
  | Nexp_minus (n1, n2) -> rewrap (Nexp_minus (orig_nexp n1, orig_nexp n2))
  | Nexp_exp n -> rewrap (Nexp_exp (orig_nexp n))
  | Nexp_neg n -> rewrap (Nexp_neg (orig_nexp n))
  | _ -> rewrap nexp

let is_list (Typ_aux (typ_aux, _)) =
  match typ_aux with Typ_app (f, [A_aux (A_typ typ, _)]) when string_of_id f = "list" -> Some typ | _ -> None

let is_unknown_type = function Typ_aux (Typ_internal_unknown, _) -> true | _ -> false

let is_atom (Typ_aux (typ_aux, _)) =
  match typ_aux with Typ_app (f, [_]) when string_of_id f = "atom" -> true | _ -> false

let is_atom_bool (Typ_aux (typ_aux, _)) =
  match typ_aux with Typ_app (f, [_]) when string_of_id f = "atom_bool" -> true | _ -> false

let rec typ_constraints (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_internal_unknown -> []
  | Typ_id _ -> []
  | Typ_var _ -> []
  | Typ_tuple typs -> List.concat (List.map typ_constraints typs)
  | Typ_app (_, args) -> List.concat (List.map typ_arg_constraints args)
  | Typ_exist (_, _, typ) -> typ_constraints typ
  | Typ_fn (arg_typs, ret_typ) -> List.concat (List.map typ_constraints arg_typs) @ typ_constraints ret_typ
  | Typ_bidir (typ1, typ2) -> typ_constraints typ1 @ typ_constraints typ2

and typ_arg_constraints (A_aux (typ_arg_aux, _)) =
  match typ_arg_aux with A_nexp _ -> [] | A_typ typ -> typ_constraints typ | A_bool nc -> [nc]

(* Replace A_nexp nexp with A_nexp nexp' in typ, intended for use after typ_nexps. *)
let rec replace_nexp_typ nexp nexp' (Typ_aux (typ_aux, l) as typ) =
  let rep_typ = replace_nexp_typ nexp nexp' in
  match typ_aux with
  | Typ_internal_unknown | Typ_id _ | Typ_var _ -> typ
  | Typ_tuple typs -> Typ_aux (Typ_tuple (List.map rep_typ typs), l)
  | Typ_app (f, args) -> Typ_aux (Typ_app (f, List.map (replace_nexp_typ_arg nexp nexp') args), l)
  | Typ_exist (kids, nc, typ) -> Typ_aux (Typ_exist (kids, nc, rep_typ typ), l)
  | Typ_fn (arg_typs, ret_typ) -> Typ_aux (Typ_fn (List.map rep_typ arg_typs, rep_typ ret_typ), l)
  | Typ_bidir (typ1, typ2) -> Typ_aux (Typ_bidir (rep_typ typ1, rep_typ typ2), l)

and replace_nexp_typ_arg nexp nexp' (A_aux (typ_arg_aux, l) as arg) =
  match typ_arg_aux with
  | A_nexp n -> if Nexp.compare n nexp == 0 then A_aux (A_nexp nexp', l) else arg
  | A_typ typ -> A_aux (A_typ (replace_nexp_typ nexp nexp' typ), l)
  | A_bool nc -> A_aux (A_bool (replace_nexp_nc nexp nexp' nc), l)

and replace_nexp_nc nexp nexp' (NC_aux (nc_aux, l) as nc) =
  let rep_nc = replace_nexp_nc nexp nexp' in
  let rep n = if Nexp.compare n nexp == 0 then nexp' else n in
  match nc_aux with
  | NC_equal (n1, n2) -> NC_aux (NC_equal (rep n1, rep n2), l)
  | NC_bounded_ge (n1, n2) -> NC_aux (NC_bounded_ge (rep n1, rep n2), l)
  | NC_bounded_le (n1, n2) -> NC_aux (NC_bounded_le (rep n1, rep n2), l)
  | NC_bounded_gt (n1, n2) -> NC_aux (NC_bounded_gt (rep n1, rep n2), l)
  | NC_bounded_lt (n1, n2) -> NC_aux (NC_bounded_lt (rep n1, rep n2), l)
  | NC_not_equal (n1, n2) -> NC_aux (NC_not_equal (rep n1, rep n2), l)
  | NC_set _ | NC_true | NC_false | NC_var _ -> nc
  | NC_or (nc1, nc2) -> NC_aux (NC_or (rep_nc nc1, rep_nc nc2), l)
  | NC_and (nc1, nc2) -> NC_aux (NC_and (rep_nc nc1, rep_nc nc2), l)
  | NC_app (f, args) -> NC_aux (NC_app (f, List.map (replace_nexp_typ_arg nexp nexp') args), l)

(* Similarly for constraints *)
let rec replace_nc_typ nc nc' (Typ_aux (typ_aux, l) as typ) =
  let rep_typ = replace_nc_typ nc nc' in
  match typ_aux with
  | Typ_internal_unknown | Typ_id _ | Typ_var _ -> typ
  | Typ_tuple typs -> Typ_aux (Typ_tuple (List.map rep_typ typs), l)
  | Typ_app (f, args) -> Typ_aux (Typ_app (f, List.map (replace_nc_typ_arg nc nc') args), l)
  | Typ_exist (kids, nc, typ) -> Typ_aux (Typ_exist (kids, nc, rep_typ typ), l)
  | Typ_fn (arg_typs, ret_typ) -> Typ_aux (Typ_fn (List.map rep_typ arg_typs, rep_typ ret_typ), l)
  | Typ_bidir (typ1, typ2) -> Typ_aux (Typ_bidir (rep_typ typ1, rep_typ typ2), l)

and replace_nc_typ_arg nc nc' (A_aux (typ_arg_aux, l) as arg) =
  match typ_arg_aux with
  | A_nexp _ -> arg
  | A_typ typ -> A_aux (A_typ (replace_nc_typ nc nc' typ), l)
  | A_bool nc'' -> if NC.compare nc nc'' == 0 then A_aux (A_bool nc', l) else arg

let rec name_pat (P_aux (aux, _)) =
  match aux with
  | P_id id | P_as (_, id) -> Some ("_" ^ string_of_id id)
  | P_typ (_, pat) | P_var (pat, _) -> name_pat pat
  | _ -> None

(**************************************************************************)
(* 1. The Typing Environment                                              *)
(**************************************************************************)

type env = Type_env.env

module Env : sig
  include module type of Type_env
end = struct
  include Type_env
end

let destruct_numeric = Type_internal.destruct_numeric
let destruct_boolean = Type_internal.destruct_boolean
let destruct_exist = Type_internal.destruct_exist
let destruct_exist_plain = Type_internal.destruct_exist_plain

let get_bitfield_ranges id env = snd (Env.get_bitfield id env)

let get_bitfield_range id field env = try Bindings.find_opt field (get_bitfield_ranges id env) with Not_found -> None

let expand_bind_synonyms l env (typq, typ) = (typq, Env.expand_synonyms (Env.add_typquant l typq env) typ)

let wf_binding l env (typq, typ) =
  let env = Env.add_typquant l typq env in
  Env.wf_typ env typ

let wf_typschm env (TypSchm_aux (TypSchm_ts (typq, typ), l)) = wf_binding l env (typq, typ)

let dvector_typ _env n typ = vector_typ n typ
let bits_typ _env n = bitvector_typ n

let add_existential l kopts nc env =
  let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) env kopts in
  Env.add_constraint nc env

let add_typ_vars l kopts env =
  List.fold_left
    (fun env (KOpt_aux (_, kl) as kopt) -> Env.add_typ_var (Parse_ast.Hint ("derived from here", kl, l)) kopt env)
    env kopts

let is_exist = function Typ_aux (Typ_exist (_, _, _), _) -> true | _ -> false

let exist_typ l constr typ =
  let fresh = fresh_existential l K_int in
  mk_typ (Typ_exist ([fresh], constr (kopt_kid fresh), typ (kopt_kid fresh)))

let bind_numeric l typ env =
  match destruct_numeric (Env.expand_synonyms env typ) with
  | Some (kids, nc, nexp) -> (nexp, add_existential l (List.map (mk_kopt K_int) kids) nc env)
  | None -> typ_error l ("Expected " ^ string_of_typ typ ^ " to be numeric")

let check_shadow_leaks l inner_env outer_env typ =
  typ_debug (lazy ("Shadow leaks: " ^ string_of_typ typ));
  let vars = tyvars_of_typ typ in
  List.iter
    (fun var ->
      if Env.shadows var inner_env > Env.shadows var outer_env then
        typ_error l ("Type variable " ^ string_of_kid var ^ " would leak into a scope where it is shadowed")
      else (
        match Env.get_typ_var_loc_opt var outer_env with
        | Some _ -> ()
        | None -> (
            match Env.get_typ_var_loc_opt var inner_env with
            | Some leak_l ->
                typ_raise l
                  (err_because
                     ( Err_other
                         ("The type variable " ^ string_of_kid var
                        ^ " would leak into an outer scope.\n\nTry adding a type annotation to this expression."
                         ),
                       leak_l,
                       Err_other ("Type variable " ^ string_of_kid var ^ " was introduced here")
                     )
                  )
            | None -> Reporting.unreachable l __POS__ "Found a type with an unknown type variable"
          )
      )
    )
    (KidSet.elements vars);
  typ

(** Pull an (potentially)-existentially qualified type into the global
   typing environment **)
let bind_existential l name typ env =
  match destruct_exist ~name (Env.expand_synonyms env typ) with
  | Some (kids, nc, typ) -> (typ, add_existential l kids nc env)
  | None -> (typ, env)

let bind_tuple_existentials l name (Typ_aux (aux, annot) as typ) env =
  match aux with
  | Typ_tuple typs ->
      let typs, env =
        List.fold_right
          (fun typ (typs, env) ->
            let typ, env = bind_existential l name typ env in
            (typ :: typs, env)
          )
          typs ([], env)
      in
      (Typ_aux (Typ_tuple typs, annot), env)
  | _ -> (typ, env)

let destruct_range env typ =
  let kopts, constr, Typ_aux (typ_aux, _) =
    Option.value ~default:([], nc_true, typ) (destruct_exist (Env.expand_synonyms env typ))
  in
  match typ_aux with
  | Typ_app (f, [A_aux (A_nexp n, _)]) when string_of_id f = "atom" || string_of_id f = "implicit" ->
      Some (List.map kopt_kid kopts, constr, n, n)
  | Typ_app (f, [A_aux (A_nexp n1, _); A_aux (A_nexp n2, _)]) when string_of_id f = "range" ->
      Some (List.map kopt_kid kopts, constr, n1, n2)
  | _ -> None

let destruct_vector env typ =
  let destruct_vector' = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _); A_aux (A_typ vtyp, _)]), _) when string_of_id id = "vector" ->
        Some (nexp_simp n1, vtyp)
    | _ -> None
  in
  destruct_vector' (Env.expand_synonyms env typ)

let destruct_bitvector env typ =
  let destruct_bitvector' = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _)]), _) when string_of_id id = "bitvector" -> Some (nexp_simp n1)
    | _ -> None
  in
  destruct_bitvector' (Env.expand_synonyms env typ)

let vector_start_index env typ =
  let len, _ = vector_typ_args_of typ in
  match Env.get_default_order env with
  | Ord_aux (Ord_inc, _) -> nint 0
  | Ord_aux (Ord_dec, _) -> nexp_simp (nminus len (nint 1))

let rec is_typ_monomorphic (Typ_aux (typ, l)) =
  match typ with
  | Typ_id _ -> true
  | Typ_tuple typs -> List.for_all is_typ_monomorphic typs
  | Typ_app (_, args) -> List.for_all is_typ_arg_monomorphic args
  | Typ_fn (arg_typs, ret_typ) -> List.for_all is_typ_monomorphic arg_typs && is_typ_monomorphic ret_typ
  | Typ_bidir (typ1, typ2) -> is_typ_monomorphic typ1 && is_typ_monomorphic typ2
  | Typ_exist _ | Typ_var _ -> false
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"

and is_typ_arg_monomorphic (A_aux (arg, _)) =
  match arg with A_nexp _ -> true | A_typ typ -> is_typ_monomorphic typ | A_bool _ -> true

(**************************************************************************)
(* 2. Subtyping and constraint solving                                    *)
(**************************************************************************)

type ('a, 'b) filter = Keep of 'a | Remove of 'b

let rec filter_keep = function Keep x :: xs -> x :: filter_keep xs | Remove _ :: xs -> filter_keep xs | [] -> []

let rec filter_remove = function Keep _ :: xs -> filter_remove xs | Remove x :: xs -> x :: filter_remove xs | [] -> []

let filter_split f g xs =
  let xs = List.map f xs in
  (filter_keep xs, g (filter_remove xs))

let rec simp_typ (Typ_aux (typ_aux, l)) = Typ_aux (simp_typ_aux typ_aux, l)

and simp_typ_aux = function
  | Typ_exist (kids1, nc1, Typ_aux (Typ_exist (kids2, nc2, typ), _)) ->
      simp_typ_aux (Typ_exist (kids1 @ kids2, nc_and nc1 nc2, typ))
  (* This removes redundant boolean variables in existentials, such
     that {('p: Bool) ('q:Bool) ('r: Bool), nc('r). bool('p & 'q & 'r)}
     would become {('s:Bool) ('r: Bool), nc('r). bool('s & 'r)},
     wherein all the redundant boolean variables have been combined
     into a single one. Making this simplification allows us to avoid
     having to pass large numbers of pointless variables to SMT if we
     ever bind this existential. *)
  | Typ_exist (vars, nc, Typ_aux (Typ_app (Id_aux (Id "atom_bool", _), [A_aux (A_bool b, _)]), l)) ->
      let kids = KidSet.of_list (List.map kopt_kid vars) in
      let constrained = tyvars_of_constraint nc in
      let conjs = constraint_conj b in
      let is_redundant = function
        | NC_aux (NC_var v, _) when KidSet.mem v kids && not (KidSet.mem v constrained) -> Remove v
        | nc -> Keep nc
      in
      let conjs, redundant = filter_split is_redundant KidSet.of_list conjs in
      begin
        match conjs with
        | [] -> Typ_id (mk_id "bool")
        | conj :: conjs when KidSet.is_empty redundant ->
            Typ_exist (vars, nc, atom_bool_typ (List.fold_left nc_and conj conjs))
        | conjs ->
            let vars = List.filter (fun v -> not (KidSet.mem (kopt_kid v) redundant)) vars in
            let var = fresh_existential l K_bool in
            Typ_exist (var :: vars, nc, atom_bool_typ (List.fold_left nc_and (nc_var (kopt_kid var)) conjs))
      end
  | typ_aux -> typ_aux

(* Here's how the constraint generation works for subtyping

   X(b,c...) --> {a. Y(a,b,c...)} \subseteq {a. Z(a,b,c...)}

   this is equivalent to

   \forall b c. X(b,c) --> \forall a. Y(a,b,c) --> Z(a,b,c)

   \forall b c. X(b,c) --> \forall a. !Y(a,b,c) \/ !Z^-1(a,b,c)

   \forall b c. X(b,c) --> !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

   \forall b c. !X(b,c) \/ !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

   !\exists b c. X(b,c) /\ \exists a. Y(a,b,c) /\ Z^-1(a,b,c)

   !\exists a b c. X(b,c) /\ Y(a,b,c) /\ Z^-1(a,b,c)

   which is then a problem we can feed to the constraint solver expecting unsat.
*)

let prove_smt ~assumptions:ncs (NC_aux (_, l) as nc) =
  match Constraint.call_smt l (List.fold_left nc_and (nc_not nc) ncs) with
  | Constraint.Unsat ->
      typ_debug (lazy "unsat");
      true
  | Constraint.Sat ->
      typ_debug (lazy "sat");
      false
  | Constraint.Unknown -> (
      (* Work around versions of z3 that are confused by 2^n in
         constraints, even when such constraints are irrelevant *)
      let ncs' = List.concat (List.map constraint_conj ncs) in
      let ncs' = List.filter (fun nc -> KidSet.is_empty (constraint_power_variables nc)) ncs' in
      match Constraint.call_smt l (List.fold_left nc_and (nc_not nc) ncs') with
      | Constraint.Unsat ->
          typ_debug (lazy "unsat");
          true
      | Constraint.Sat | Constraint.Unknown ->
          typ_debug (lazy "sat/unknown");
          false
    )

let solve_unique env (Nexp_aux (_, l) as nexp) =
  typ_print
    ( lazy
      (Util.("Solve " |> red |> clear)
      ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env)
      ^ " |- " ^ string_of_nexp nexp ^ " = ?"
      )
      );
  match nexp with
  | Nexp_aux (Nexp_constant n, _) -> Some n
  | _ ->
      let env = Env.add_typ_var l (mk_kopt K_int (mk_kid "solve#")) env in
      let vars = Env.get_typ_vars env in
      let _vars = KBindings.filter (fun _ k -> match k with K_int | K_bool -> true | _ -> false) vars in
      let constr = List.fold_left nc_and (nc_eq (nvar (mk_kid "solve#")) nexp) (Env.get_constraints env) in
      Constraint.solve_unique_smt l constr (mk_kid "solve#")

let debug_pos (file, line, _, _) = "(" ^ file ^ "/" ^ string_of_int line ^ ") "

let prove pos env nc =
  let ncs = Env.get_constraints env in
  typ_print
    ( lazy
      (Util.("Prove " |> red |> clear)
      ^ string_of_list ", " string_of_n_constraint ncs
      ^ " |- " ^ string_of_n_constraint nc
      )
      );
  let (NC_aux (nc_aux, _) as nc) = constraint_simp (Env.expand_constraint_synonyms env nc) in
  if !Constraint.opt_smt_verbose then
    prerr_endline
      (Util.("Prove " |> red |> clear)
      ^ debug_pos pos
      ^ string_of_list ", " string_of_n_constraint ncs
      ^ " |- " ^ string_of_n_constraint nc
      );
  match nc_aux with NC_true -> true | _ -> prove_smt ~assumptions:ncs nc

(**************************************************************************)
(* 3. Unification                                                         *)
(**************************************************************************)

let rec nexp_frees ?(exs = KidSet.empty) (Nexp_aux (nexp, _)) =
  match nexp with
  | Nexp_id _ -> KidSet.empty
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_constant _ -> KidSet.empty
  | Nexp_times (n1, n2) -> KidSet.union (nexp_frees ~exs n1) (nexp_frees ~exs n2)
  | Nexp_sum (n1, n2) -> KidSet.union (nexp_frees ~exs n1) (nexp_frees ~exs n2)
  | Nexp_minus (n1, n2) -> KidSet.union (nexp_frees ~exs n1) (nexp_frees ~exs n2)
  | Nexp_app (_, ns) -> List.fold_left KidSet.union KidSet.empty (List.map (fun n -> nexp_frees ~exs n) ns)
  | Nexp_exp n -> nexp_frees ~exs n
  | Nexp_neg n -> nexp_frees ~exs n

let rec nexp_identical (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
  match (nexp1, nexp2) with
  | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2 = 0
  | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2 = 0
  | Nexp_constant c1, Nexp_constant c2 -> Big_int.equal c1 c2
  | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_exp n1, Nexp_exp n2 -> nexp_identical n1 n2
  | Nexp_neg n1, Nexp_neg n2 -> nexp_identical n1 n2
  | Nexp_app (f1, args1), Nexp_app (f2, args2) when List.length args1 = List.length args2 ->
      Id.compare f1 f2 = 0 && List.for_all2 nexp_identical args1 args2
  | _, _ -> false

let rec nc_identical (NC_aux (nc1, _)) (NC_aux (nc2, _)) =
  match (nc1, nc2) with
  | NC_equal (n1a, n1b), NC_equal (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_not_equal (n1a, n1b), NC_not_equal (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_ge (n1a, n1b), NC_bounded_ge (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_gt (n1a, n1b), NC_bounded_gt (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_le (n1a, n1b), NC_bounded_le (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_lt (n1a, n1b), NC_bounded_lt (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_or (nc1a, nc1b), NC_or (nc2a, nc2b) -> nc_identical nc1a nc2a && nc_identical nc1b nc2b
  | NC_and (nc1a, nc1b), NC_and (nc2a, nc2b) -> nc_identical nc1a nc2a && nc_identical nc1b nc2b
  | NC_true, NC_true -> true
  | NC_false, NC_false -> true
  | NC_set (kid1, ints1), NC_set (kid2, ints2) when List.length ints1 = List.length ints2 ->
      Kid.compare kid1 kid2 = 0 && List.for_all2 (fun i1 i2 -> i1 = i2) ints1 ints2
  | NC_var kid1, NC_var kid2 -> Kid.compare kid1 kid2 = 0
  | NC_app (id1, args1), NC_app (id2, args2) when List.length args1 = List.length args2 ->
      Id.compare id1 id2 = 0 && List.for_all2 typ_arg_identical args1 args2
  | _, _ -> false

and typ_arg_identical (A_aux (arg1, _)) (A_aux (arg2, _)) =
  match (arg1, arg2) with
  | A_nexp n1, A_nexp n2 -> nexp_identical n1 n2
  | A_typ typ1, A_typ typ2 -> typ_identical typ1 typ2
  | A_bool nc1, A_bool nc2 -> nc_identical nc1 nc2
  | _, _ -> false

and typ_identical (Typ_aux (typ1, _)) (Typ_aux (typ2, _)) =
  match (typ1, typ2) with
  | Typ_id v1, Typ_id v2 -> Id.compare v1 v2 = 0
  | Typ_var kid1, Typ_var kid2 -> Kid.compare kid1 kid2 = 0
  | Typ_fn (arg_typs1, ret_typ1), Typ_fn (arg_typs2, ret_typ2) when List.length arg_typs1 = List.length arg_typs2 ->
      List.for_all2 typ_identical arg_typs1 arg_typs2 && typ_identical ret_typ1 ret_typ2
  | Typ_bidir (typ1, typ2), Typ_bidir (typ3, typ4) -> typ_identical typ1 typ3 && typ_identical typ2 typ4
  | Typ_tuple typs1, Typ_tuple typs2 -> begin
      try List.for_all2 typ_identical typs1 typs2 with Invalid_argument _ -> false
    end
  | Typ_app (f1, args1), Typ_app (f2, args2) -> begin
      try Id.compare f1 f2 = 0 && List.for_all2 typ_arg_identical args1 args2 with Invalid_argument _ -> false
    end
  | Typ_exist (kopts1, nc1, typ1), Typ_exist (kopts2, nc2, typ2) when List.length kopts1 = List.length kopts2 ->
      List.for_all2 (fun k1 k2 -> KOpt.compare k1 k2 = 0) kopts1 kopts2
      && nc_identical nc1 nc2 && typ_identical typ1 typ2
  | _, _ -> false

let expanded_typ_identical env typ1 typ2 = typ_identical (Env.expand_synonyms env typ1) (Env.expand_synonyms env typ2)

exception Unification_error of l * string

let unify_error l str = raise (Unification_error (l, str))

let merge_unifiers env l kid uvar1 uvar2 =
  match (uvar1, uvar2) with
  | Some arg1, Some arg2 when typ_arg_identical arg1 arg2 -> Some arg1
  (* If the unifiers are equivalent nexps, use one, preferably a variable *)
  | Some (A_aux (A_nexp nexp1, _) as arg1), Some (A_aux (A_nexp nexp2, _) as arg2)
    when prove __POS__ env (nc_eq nexp1 nexp2) -> begin
      match (nexp1, nexp2) with
      | Nexp_aux (Nexp_var _, _), _ -> Some arg1
      | _, Nexp_aux (Nexp_var _, _) -> Some arg2
      | _, _ -> Some arg1
    end
  | Some arg1, Some arg2 ->
      unify_error l
        ("Multiple non-identical unifiers for " ^ string_of_kid kid ^ ": " ^ string_of_typ_arg arg1 ^ " and "
       ^ string_of_typ_arg arg2
        )
  | None, Some u2 -> Some u2
  | Some u1, None -> Some u1
  | None, None -> None

let merge_uvars env l unifiers1 unifiers2 = KBindings.merge (merge_unifiers env l) unifiers1 unifiers2

let rec unify_typ l env goals (Typ_aux (aux1, _) as typ1) (Typ_aux (aux2, _) as typ2) =
  typ_debug
    ( lazy
      (Util.("Unify type " |> magenta |> clear)
      ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2 ^ " goals "
      ^ string_of_list ", " string_of_kid (KidSet.elements goals)
      )
      );
  match (aux1, aux2) with
  | (Typ_internal_unknown, _ | _, Typ_internal_unknown) when Env.allow_unknowns env -> KBindings.empty
  | Typ_var v, _ when KidSet.mem v goals -> KBindings.singleton v (arg_typ typ2)
  | Typ_var v1, Typ_var v2 when Kid.compare v1 v2 = 0 -> KBindings.empty
  (* We need special cases for unifying range(n, m), nat, and int vs atom('n) *)
  | Typ_id int, Typ_app (atom, [A_aux (A_nexp _, _)]) when string_of_id int = "int" && string_of_id atom = "atom" ->
      KBindings.empty
  | Typ_id nat, Typ_app (atom, [A_aux (A_nexp n, _)]) when string_of_id nat = "nat" && string_of_id atom = "atom" ->
      if prove __POS__ env (nc_gteq n (nint 0)) then KBindings.empty
      else unify_error l (string_of_typ typ2 ^ " must be a natural number")
  | Typ_app (range, [A_aux (A_nexp n1, _); A_aux (A_nexp n2, _)]), Typ_app (atom, [A_aux (A_nexp m, _)])
    when string_of_id range = "range" && string_of_id atom = "atom" ->
      let n1, n2 = (nexp_simp n1, nexp_simp n2) in
      begin
        match (n1, n2) with
        | Nexp_aux (Nexp_constant _, _), Nexp_aux (Nexp_constant _, _) ->
            if prove __POS__ env (nc_and (nc_lteq n1 m) (nc_lteq m n2)) then KBindings.empty
            else unify_error l (string_of_typ typ1 ^ " is not contained within " ^ string_of_typ typ1)
        | _, _ -> merge_uvars env l (unify_nexp l env goals n1 m) (unify_nexp l env goals n2 m)
      end
  | Typ_app (id1, args1), Typ_app (id2, args2) when List.length args1 = List.length args2 && Id.compare id1 id2 = 0 ->
      List.fold_left (merge_uvars env l) KBindings.empty (List.map2 (unify_typ_arg l env goals) args1 args2)
  | Typ_app (id1, []), Typ_id id2 when Id.compare id1 id2 = 0 -> KBindings.empty
  | Typ_id id1, Typ_app (id2, []) when Id.compare id1 id2 = 0 -> KBindings.empty
  | Typ_id id1, Typ_id id2 when Id.compare id1 id2 = 0 -> KBindings.empty
  | Typ_tuple typs1, Typ_tuple typs2 when List.length typs1 = List.length typs2 ->
      List.fold_left (merge_uvars env l) KBindings.empty (List.map2 (unify_typ l env goals) typs1 typs2)
  | Typ_fn (arg_typs1, ret_typ1), Typ_fn (arg_typs2, ret_typ2) when List.length arg_typs1 = List.length arg_typs2 ->
      merge_uvars env l
        (List.fold_left (merge_uvars env l) KBindings.empty (List.map2 (unify_typ l env goals) arg_typs1 arg_typs2))
        (unify_typ l env goals ret_typ1 ret_typ2)
  | _, _ -> unify_error l ("Could not unify " ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2)

and unify_typ_arg l env goals (A_aux (aux1, _) as typ_arg1) (A_aux (aux2, _) as typ_arg2) =
  match (aux1, aux2) with
  | A_typ typ1, A_typ typ2 -> unify_typ l env goals typ1 typ2
  | A_nexp nexp1, A_nexp nexp2 -> unify_nexp l env goals nexp1 nexp2
  | A_bool nc1, A_bool nc2 -> unify_constraint l env goals nc1 nc2
  | _, _ ->
      unify_error l
        ("Could not unify type arguments " ^ string_of_typ_arg typ_arg1 ^ " and " ^ string_of_typ_arg typ_arg2)

and unify_constraint l env goals (NC_aux (aux1, _) as nc1) (NC_aux (aux2, _) as nc2) =
  typ_debug
    ( lazy
      (Util.("Unify constraint " |> magenta |> clear)
      ^ string_of_n_constraint nc1 ^ " and " ^ string_of_n_constraint nc2
      )
      );
  match (aux1, aux2) with
  | NC_var v, _ when KidSet.mem v goals -> KBindings.singleton v (arg_bool nc2)
  | NC_var v, NC_var v' when Kid.compare v v' = 0 -> KBindings.empty
  | NC_and (nc1a, nc2a), NC_and (nc1b, nc2b) -> begin
      try
        let conjs1 = List.sort NC.compare (constraint_conj nc1) in
        let conjs2 = List.sort NC.compare (constraint_conj nc2) in
        let unify_merge uv nc1 nc2 = merge_uvars env l uv (unify_constraint l env goals nc1 nc2) in
        List.fold_left2 unify_merge KBindings.empty conjs1 conjs2
      with _ -> merge_uvars env l (unify_constraint l env goals nc1a nc1b) (unify_constraint l env goals nc2a nc2b)
    end
  | NC_or (nc1a, nc2a), NC_or (nc1b, nc2b) ->
      merge_uvars env l (unify_constraint l env goals nc1a nc1b) (unify_constraint l env goals nc2a nc2b)
  | NC_app (f1, args1), NC_app (f2, args2) when Id.compare f1 f2 = 0 && List.length args1 = List.length args2 ->
      List.fold_left (merge_uvars env l) KBindings.empty (List.map2 (unify_typ_arg l env goals) args1 args2)
  | NC_equal (n1a, n2a), NC_equal (n1b, n2b) ->
      merge_uvars env l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_not_equal (n1a, n2a), NC_not_equal (n1b, n2b) ->
      merge_uvars env l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_ge (n1a, n2a), NC_bounded_ge (n1b, n2b) ->
      merge_uvars env l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_gt (n1a, n2a), NC_bounded_gt (n1b, n2b) ->
      merge_uvars env l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_le (n1a, n2a), NC_bounded_le (n1b, n2b) ->
      merge_uvars env l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_lt (n1a, n2a), NC_bounded_lt (n1b, n2b) ->
      merge_uvars env l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_true, NC_true -> KBindings.empty
  | NC_false, NC_false -> KBindings.empty
  | _, _ ->
      unify_error l ("Could not unify constraints " ^ string_of_n_constraint nc1 ^ " and " ^ string_of_n_constraint nc2)

and unify_nexp l env goals (Nexp_aux (nexp_aux1, _) as nexp1) (Nexp_aux (nexp_aux2, _) as nexp2) =
  typ_debug
    ( lazy
      (Util.("Unify nexp " |> magenta |> clear)
      ^ string_of_nexp nexp1 ^ " and " ^ string_of_nexp nexp2 ^ " goals "
      ^ string_of_list ", " string_of_kid (KidSet.elements goals)
      )
      );
  if KidSet.is_empty (KidSet.inter (nexp_frees nexp1) goals) then begin
    if prove __POS__ env (NC_aux (NC_equal (nexp1, nexp2), Parse_ast.Unknown)) then KBindings.empty
    else
      unify_error l ("Integer expressions " ^ string_of_nexp nexp1 ^ " and " ^ string_of_nexp nexp2 ^ " are not equal")
  end
  else (
    match nexp_aux1 with
    | Nexp_id _ -> unify_error l "Unimplemented Nexp_id in unify nexp"
    | Nexp_var kid when KidSet.mem kid goals -> KBindings.singleton kid (arg_nexp nexp2)
    | Nexp_constant c1 -> begin
        match nexp_aux2 with
        | Nexp_constant c2 -> if c1 = c2 then KBindings.empty else unify_error l "Constants are not the same"
        | _ -> unify_error l "Unification error"
      end
    | Nexp_sum (n1a, n1b) ->
        if KidSet.is_empty (nexp_frees n1b) then unify_nexp l env goals n1a (nminus nexp2 n1b)
        else if KidSet.is_empty (nexp_frees n1a) then unify_nexp l env goals n1b (nminus nexp2 n1a)
        else begin
          match nexp_aux2 with
          | Nexp_sum (n2a, n2b) ->
              if KidSet.is_empty (nexp_frees n2a) then unify_nexp l env goals n2b (nminus nexp1 n2a)
              else if KidSet.is_empty (nexp_frees n2a) then unify_nexp l env goals n2a (nminus nexp1 n2b)
              else merge_uvars env l (unify_nexp l env goals n1a n2a) (unify_nexp l env goals n1b n2b)
          | _ ->
              unify_error l
                ("Both sides of Int expression " ^ string_of_nexp nexp1
               ^ " contain free type variables so it cannot be unified with " ^ string_of_nexp nexp2
                )
        end
    | Nexp_minus (n1a, n1b) ->
        if KidSet.is_empty (nexp_frees n1b) then unify_nexp l env goals n1a (nsum nexp2 n1b)
        else
          unify_error l ("Cannot unify minus Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
    | Nexp_times (n1a, n1b) ->
        (* If we have SMT operations div and mod, then we can use the
           property that

           mod(m, C) = 0 && C != 0 --> (C * n = m <--> n = m / C)

           to help us unify multiplications and divisions.

           In particular, the nexp rewriting used in monomorphisation adds
           constraints of the form 8 * 'n == 'p8_times_n, and we sometimes need
           to solve for 'n.
        *)
        let valid n c =
          prove __POS__ env (nc_eq (napp (mk_id "mod") [n; c]) (nint 0)) && prove __POS__ env (nc_neq c (nint 0))
        in
        (*if KidSet.is_empty (nexp_frees n1b) && valid nexp2 n1b then
            unify_nexp l env goals n1a (napp (mk_id "div") [nexp2; n1b])
          else if KidSet.is_empty (nexp_frees n1a) && valid nexp2 n1a then
            unify_nexp l env goals n1b (napp (mk_id "div") [nexp2; n1a]) *)
        if KidSet.is_empty (nexp_frees n1a) then begin
          match nexp_aux2 with
          | Nexp_times (n2a, n2b) when prove __POS__ env (NC_aux (NC_equal (n1a, n2a), Parse_ast.Unknown)) ->
              unify_nexp l env goals n1b n2b
          | Nexp_constant c2 -> begin
              match n1a with
              | Nexp_aux (Nexp_constant c1, _) when Big_int.equal (Big_int.modulus c2 c1) Big_int.zero ->
                  unify_nexp l env goals n1b (nconstant (Big_int.div c2 c1))
              | _ ->
                  unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
            end
          | Nexp_var kid when (not (KidSet.mem kid goals)) && valid nexp2 n1a ->
              unify_nexp l env goals n1b (napp (mk_id "div") [nexp2; n1a])
          | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
        end
        else if KidSet.is_empty (nexp_frees n1b) then begin
          match nexp_aux2 with
          | Nexp_times (n2a, n2b) when prove __POS__ env (NC_aux (NC_equal (n1b, n2b), Parse_ast.Unknown)) ->
              unify_nexp l env goals n1a n2a
          | Nexp_var kid when (not (KidSet.mem kid goals)) && valid nexp2 n1b ->
              unify_nexp l env goals n1a (napp (mk_id "div") [nexp2; n1b])
          | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
        end
        else unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
    | Nexp_exp n1 -> begin
        match nexp_aux2 with
        | Nexp_exp n2 -> unify_nexp l env goals n1 n2
        | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
      end
    | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
  )

let unify l env goals typ1 typ2 =
  typ_print
    ( lazy
      (Util.("Unify " |> magenta |> clear)
      ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2 ^ " for "
      ^ Util.string_of_list ", " string_of_kid (KidSet.elements goals)
      )
      );
  let typ1, typ2 = (Env.expand_synonyms env typ1, Env.expand_synonyms env typ2) in
  if not (KidSet.is_empty (KidSet.inter goals (tyvars_of_typ typ2))) then
    typ_error l
      ("Occurs check failed: " ^ string_of_typ typ2 ^ " contains "
      ^ Util.string_of_list ", " string_of_kid (KidSet.elements goals)
      )
  else unify_typ l env goals typ1 typ2

let subst_unifiers unifiers typ =
  List.fold_left (fun typ (v, arg) -> typ_subst v arg typ) typ (KBindings.bindings unifiers)

let subst_unifiers_typ_arg unifiers typ_arg =
  List.fold_left (fun typ_arg (v, arg) -> typ_arg_subst v arg typ_arg) typ_arg (KBindings.bindings unifiers)

let instantiate_quant (v, arg) (QI_aux (aux, l) as qi) =
  match aux with
  | QI_id kopt when Kid.compare (kopt_kid kopt) v = 0 ->
      typ_debug (lazy ("Instantiated " ^ string_of_quant_item qi));
      None
  | QI_id _ -> Some qi
  | QI_constraint nc -> Some (QI_aux (QI_constraint (constraint_subst v arg nc), l))

let instantiate_quants quants unifier = List.map (instantiate_quant unifier) quants |> Util.option_these

(* During typechecking, we can run into the following issue, where we
   have a function like

   val and_bool : forall ('p : Bool) ('q : Bool). (bool('p), bool('q)) -> bool('p & 'q)

   and we want to check something like Q & P <= bool(X & Y)

   where Q => bool(Y) & P => bool(X)

   if we instantiate using the return type (which is usually good)
   we'll run into the situtation where we have to check bool(Y)
   subtype bool(X) because the quantifiers will get instantiated in
   the wrong order, despite the expression being otherwise well-typed
   the trick here is to recognise that we shouldn't unify on goals in
   certain ambiguous positions in types. In this case with and_bool,
   they'll be unambigiously unified with the argument types so it's
   better to just not bother with the return type.
*)
let rec ambiguous_vars' (Typ_aux (aux, _)) =
  match aux with
  | Typ_app (_, args) -> List.fold_left KidSet.union KidSet.empty (List.map ambiguous_arg_vars args)
  | _ -> KidSet.empty

and ambiguous_arg_vars (A_aux (aux, _)) =
  match aux with A_bool nc -> ambiguous_nc_vars nc | A_nexp nexp -> ambiguous_nexp_vars nexp | _ -> KidSet.empty

and ambiguous_nc_vars (NC_aux (aux, _)) =
  match aux with
  | NC_and (nc1, nc2) -> KidSet.union (tyvars_of_constraint nc1) (tyvars_of_constraint nc2)
  | NC_bounded_le (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_bounded_lt (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_bounded_ge (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_bounded_gt (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_equal (n1, n2) | NC_not_equal (n1, n2) -> KidSet.union (ambiguous_nexp_vars n1) (ambiguous_nexp_vars n2)
  | _ -> KidSet.empty

and ambiguous_nexp_vars (Nexp_aux (aux, _)) =
  match aux with
  | Nexp_sum (nexp1, nexp2) -> KidSet.union (tyvars_of_nexp nexp1) (tyvars_of_nexp nexp2)
  | _ -> KidSet.empty

let ambiguous_vars typ =
  let vars = ambiguous_vars' typ in
  if KidSet.cardinal vars > 1 then vars else KidSet.empty

let rec is_typ_inhabited env (Typ_aux (aux, l) as typ) =
  match aux with
  | Typ_tuple typs -> List.for_all (is_typ_inhabited env) typs
  | Typ_app (id, [A_aux (A_nexp len, _)]) when Id.compare id (mk_id "bitvector") = 0 ->
      prove __POS__ env (nc_gteq len (nint 0))
  | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_typ _, _)]) when Id.compare id (mk_id "vector") = 0 ->
      prove __POS__ env (nc_gteq len (nint 0))
  | Typ_app (id, _) when Id.compare id (mk_id "list") = 0 -> true
  | Typ_app (id, args) when Env.is_variant id env ->
      let typq, constructors = Env.get_variant id env in
      let kopts, _ = quant_split typq in
      let unifiers =
        List.fold_left2 (fun kb kopt arg -> KBindings.add (kopt_kid kopt) arg kb) KBindings.empty kopts args
      in
      List.exists
        (fun (Tu_aux (Tu_ty_id (typ, _), _)) -> is_typ_inhabited env (subst_unifiers unifiers typ))
        constructors
  | Typ_id id when Env.is_record id env ->
      let _, fields = Env.get_record id env in
      List.for_all (fun (typ, _) -> is_typ_inhabited env typ) fields
  | Typ_app (id, args) when Env.is_record id env ->
      let typq, fields = Env.get_record id env in
      let kopts, _ = quant_split typq in
      let unifiers =
        List.fold_left2 (fun kb kopt arg -> KBindings.add (kopt_kid kopt) arg kb) KBindings.empty kopts args
      in
      List.for_all (fun (typ, _) -> is_typ_inhabited env (subst_unifiers unifiers typ)) fields
  | Typ_app (_, args) -> List.for_all (is_typ_arg_inhabited env) args
  | Typ_exist _ ->
      let typ, env = bind_existential l None typ env in
      is_typ_inhabited env typ
  | Typ_id _ -> true
  | Typ_var _ -> true
  | Typ_fn _ | Typ_bidir _ -> Reporting.unreachable l __POS__ "Inhabitedness check applied to function or mapping type"
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "Inhabitedness check applied to unknown type"

and is_typ_arg_inhabited env (A_aux (aux, _)) = match aux with A_typ typ -> is_typ_inhabited env typ | _ -> true

(**************************************************************************)
(* 3.5. Subtyping with existentials                                       *)
(**************************************************************************)

let destruct_atom_nexp env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_app (f, [A_aux (A_nexp n, _)]), _) when string_of_id f = "atom" || string_of_id f = "implicit" ->
      Some n
  | Typ_aux (Typ_app (f, [A_aux (A_nexp n, _); A_aux (A_nexp m, _)]), _)
    when string_of_id f = "range" && nexp_identical n m ->
      Some n
  | _ -> None

let destruct_atom_bool env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_app (f, [A_aux (A_bool nc, _)]), _) when string_of_id f = "atom_bool" -> Some nc
  | _ -> None

(* The kid_order function takes a set of Int-kinded kids, and returns
   a list of those kids in the order they appear in a type, as well as
   a set containing all the kids that did not occur in the type. We
   only care about Int-kinded kids because those are the only type
   that can appear in an existential. *)

let rec kid_order_nexp kind_map (Nexp_aux (aux, _)) =
  match aux with
  | Nexp_var kid when KBindings.mem kid kind_map ->
      ([mk_kopt (unaux_kind (KBindings.find kid kind_map)) kid], KBindings.remove kid kind_map)
  | Nexp_var _ | Nexp_id _ | Nexp_constant _ -> ([], kind_map)
  | Nexp_exp nexp | Nexp_neg nexp -> kid_order_nexp kind_map nexp
  | Nexp_times (nexp1, nexp2) | Nexp_sum (nexp1, nexp2) | Nexp_minus (nexp1, nexp2) ->
      let ord, kids = kid_order_nexp kind_map nexp1 in
      let ord', kids = kid_order_nexp kids nexp2 in
      (ord @ ord', kids)
  | Nexp_app (_, nexps) ->
      List.fold_left
        (fun (ord, kids) nexp ->
          let ord', kids = kid_order_nexp kids nexp in
          (ord @ ord', kids)
        )
        ([], kind_map) nexps

let rec kid_order kind_map (Typ_aux (aux, l) as typ) =
  match aux with
  | Typ_var kid when KBindings.mem kid kind_map ->
      ([mk_kopt (unaux_kind (KBindings.find kid kind_map)) kid], KBindings.remove kid kind_map)
  | Typ_id _ | Typ_var _ -> ([], kind_map)
  | Typ_tuple typs ->
      List.fold_left
        (fun (ord, kids) typ ->
          let ord', kids = kid_order kids typ in
          (ord @ ord', kids)
        )
        ([], kind_map) typs
  | Typ_app (_, args) ->
      List.fold_left
        (fun (ord, kids) arg ->
          let ord', kids = kid_order_arg kids arg in
          (ord @ ord', kids)
        )
        ([], kind_map) args
  | Typ_fn _ | Typ_bidir _ | Typ_exist _ ->
      typ_error l ("Existential or function type cannot appear within existential type: " ^ string_of_typ typ)
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"

and kid_order_arg kind_map (A_aux (aux, _)) =
  match aux with
  | A_typ typ -> kid_order kind_map typ
  | A_nexp nexp -> kid_order_nexp kind_map nexp
  | A_bool nc -> kid_order_constraint kind_map nc

and kid_order_constraint kind_map (NC_aux (aux, _)) =
  match aux with
  | (NC_var kid | NC_set (kid, _)) when KBindings.mem kid kind_map ->
      ([mk_kopt (unaux_kind (KBindings.find kid kind_map)) kid], KBindings.remove kid kind_map)
  | NC_var _ | NC_set _ -> ([], kind_map)
  | NC_true | NC_false -> ([], kind_map)
  | NC_equal (n1, n2)
  | NC_not_equal (n1, n2)
  | NC_bounded_le (n1, n2)
  | NC_bounded_ge (n1, n2)
  | NC_bounded_lt (n1, n2)
  | NC_bounded_gt (n1, n2) ->
      let ord1, kind_map = kid_order_nexp kind_map n1 in
      let ord2, kind_map = kid_order_nexp kind_map n2 in
      (ord1 @ ord2, kind_map)
  | NC_app (_, args) ->
      List.fold_left
        (fun (ord, kind_map) arg ->
          let ord', kind_map = kid_order_arg kind_map arg in
          (ord @ ord', kind_map)
        )
        ([], kind_map) args
  | NC_and (nc1, nc2) | NC_or (nc1, nc2) ->
      let ord1, kind_map = kid_order_constraint kind_map nc1 in
      let ord2, kind_map = kid_order_constraint kind_map nc2 in
      (ord1 @ ord2, kind_map)

let alpha_equivalent env typ1 typ2 =
  let counter = ref 0 in
  let new_kid () =
    let kid = mk_kid ("alpha#" ^ string_of_int !counter) in
    incr counter;
    kid
  in

  let rec relabel (Typ_aux (aux, l)) =
    let relabelled_aux =
      match aux with
      | Typ_internal_unknown -> Typ_internal_unknown
      | Typ_id _ | Typ_var _ -> aux
      | Typ_fn (arg_typs, ret_typ) -> Typ_fn (List.map relabel arg_typs, relabel ret_typ)
      | Typ_bidir (typ1, typ2) -> Typ_bidir (relabel typ1, relabel typ2)
      | Typ_tuple typs -> Typ_tuple (List.map relabel typs)
      | Typ_exist (kopts, nc, typ) ->
          let kind_map =
            List.fold_left (fun m kopt -> KBindings.add (kopt_kid kopt) (kopt_kind kopt) m) KBindings.empty kopts
          in
          let kopts1, kind_map = kid_order_constraint kind_map nc in
          let kopts2, _ = kid_order kind_map typ in
          let kopts = kopts1 @ kopts2 in
          let kopts =
            List.map (fun kopt -> (kopt_kid kopt, mk_kopt (unaux_kind (kopt_kind kopt)) (new_kid ()))) kopts
          in
          let nc = List.fold_left (fun nc (kid, nk) -> constraint_subst kid (arg_kopt nk) nc) nc kopts in
          let typ = List.fold_left (fun nc (kid, nk) -> typ_subst kid (arg_kopt nk) nc) typ kopts in
          let kopts = List.map snd kopts in
          Typ_exist (kopts, nc, typ)
      | Typ_app (id, args) -> Typ_app (id, List.map relabel_arg args)
    in
    Typ_aux (relabelled_aux, l)
  and relabel_arg (A_aux (aux, l) as arg) =
    (* FIXME relabel constraint *)
    match aux with A_nexp _ | A_bool _ -> arg | A_typ typ -> A_aux (A_typ (relabel typ), l)
  in

  let typ1 = relabel (Env.expand_synonyms env typ1) in
  counter := 0;
  let typ2 = relabel (Env.expand_synonyms env typ2) in
  typ_debug (lazy ("Alpha equivalence for " ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2));
  if typ_identical typ1 typ2 then (
    typ_debug (lazy "alpha-equivalent");
    true
  )
  else (
    typ_debug (lazy "Not alpha-equivalent");
    false
  )

let unifier_constraint env (v, arg) =
  match arg with A_aux (A_nexp nexp, _) -> Env.add_constraint (nc_eq (nvar v) nexp) env | _ -> env

let canonicalize env typ =
  let typ = Env.expand_synonyms env typ in
  let rec canon (Typ_aux (aux, l)) =
    match aux with
    | Typ_var v -> Typ_aux (Typ_var v, l)
    | Typ_internal_unknown -> Typ_aux (Typ_internal_unknown, l)
    | Typ_id id when string_of_id id = "int" -> exist_typ l (fun _ -> nc_true) (fun v -> atom_typ (nvar v))
    | Typ_id id -> Typ_aux (Typ_id id, l)
    | Typ_app (id, [A_aux (A_nexp lo, _); A_aux (A_nexp hi, _)]) when string_of_id id = "range" ->
        exist_typ l (fun v -> nc_and (nc_lteq lo (nvar v)) (nc_lteq (nvar v) hi)) (fun v -> atom_typ (nvar v))
    | Typ_app (id, args) -> Typ_aux (Typ_app (id, List.map canon_arg args), l)
    | Typ_tuple typs ->
        let typs = List.map canon typs in
        let fold_exist (kids, nc, typs) typ =
          match destruct_exist typ with
          | Some (kids', nc', typ') -> (kids @ kids', nc_and nc nc', typs @ [typ'])
          | None -> (kids, nc, typs @ [typ])
        in
        let kids, nc, typs = List.fold_left fold_exist ([], nc_true, []) typs in
        if kids = [] then Typ_aux (Typ_tuple typs, l) else Typ_aux (Typ_exist (kids, nc, Typ_aux (Typ_tuple typs, l)), l)
    | Typ_exist (kids, nc, typ) -> begin
        match destruct_exist (canon typ) with
        | Some (kids', nc', typ') -> Typ_aux (Typ_exist (kids @ kids', nc_and nc nc', typ'), l)
        | None -> Typ_aux (Typ_exist (kids, nc, typ), l)
      end
    | Typ_fn _ | Typ_bidir _ ->
        raise (Reporting.err_unreachable l __POS__ "Function type passed to Type_check.canonicalize")
  and canon_arg (A_aux (aux, l)) = A_aux ((match aux with A_typ typ -> A_typ (canon typ) | arg -> arg), l) in
  canon typ

let rec subtyp l env typ1 typ2 =
  let (Typ_aux (typ_aux1, _) as typ1) = Env.expand_synonyms env typ1 in
  let (Typ_aux (typ_aux2, _) as typ2) = Env.expand_synonyms env typ2 in
  typ_print (lazy (("Subtype " |> Util.green |> Util.clear) ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2));
  match (destruct_numeric typ1, destruct_numeric typ2) with
  (* Ensure alpha equivalent types are always subtypes of one another
     - this ensures that we can always re-check inferred types. *)
  | _, _ when alpha_equivalent env typ1 typ2 -> ()
  (* Special cases for two numeric (atom) types *)
  | Some (kids1, nc1, nexp1), Some ([], _, nexp2) ->
      let env = add_existential l (List.map (mk_kopt K_int) kids1) nc1 env in
      let prop = nc_eq nexp1 nexp2 in
      if prove __POS__ env prop then ()
      else typ_raise l (Err_subtype (typ1, typ2, Some prop, Env.get_constraint_reasons env, Env.get_typ_vars_info env))
  | Some (kids1, nc1, nexp1), Some (kids2, nc2, nexp2) ->
      let env = add_existential l (List.map (mk_kopt K_int) kids1) nc1 env in
      let env =
        add_typ_vars l
          (List.map (mk_kopt K_int) (KidSet.elements (KidSet.inter (nexp_frees nexp2) (KidSet.of_list kids2))))
          env
      in
      let kids2 = KidSet.elements (KidSet.diff (KidSet.of_list kids2) (nexp_frees nexp2)) in
      if not (kids2 = []) then
        typ_error l ("Universally quantified constraint generated: " ^ Util.string_of_list ", " string_of_kid kids2)
      else ();
      (* TODO: Check this *)
      let _vars =
        KBindings.filter (fun _ k -> match k with K_int | K_bool -> true | _ -> false) (Env.get_typ_vars env)
      in
      begin
        match Constraint.call_smt l (nc_eq nexp1 nexp2) with
        | Constraint.Sat ->
            let env = Env.add_constraint (nc_eq nexp1 nexp2) env in
            if prove __POS__ env nc2 then ()
            else
              typ_raise l (Err_subtype (typ1, typ2, Some nc2, Env.get_constraint_reasons env, Env.get_typ_vars_info env))
        | _ -> typ_error l ("Constraint " ^ string_of_n_constraint (nc_eq nexp1 nexp2) ^ " is not satisfiable")
      end
  | _, _ -> (
      match (typ_aux1, typ_aux2) with
      | _, Typ_internal_unknown when Env.allow_unknowns env -> ()
      | Typ_app (id1, _), Typ_id id2 when string_of_id id1 = "atom_bool" && string_of_id id2 = "bool" -> ()
      | Typ_tuple typs1, Typ_tuple typs2 when List.length typs1 = List.length typs2 ->
          List.iter2 (subtyp l env) typs1 typs2
      | Typ_app (id1, args1), Typ_app (id2, args2) when Id.compare id1 id2 = 0 && List.length args1 = List.length args2
        ->
          List.iter2 (subtyp_arg l env) args1 args2
      | Typ_id id1, Typ_id id2 when Id.compare id1 id2 = 0 -> ()
      | Typ_id id1, Typ_app (id2, []) when Id.compare id1 id2 = 0 -> ()
      | Typ_app (id1, []), Typ_id id2 when Id.compare id1 id2 = 0 -> ()
      | Typ_fn (typ_args1, ret_typ1), Typ_fn (typ_args2, ret_typ2) ->
          if List.compare_lengths typ_args1 typ_args2 <> 0 then
            typ_error l "Function types do not have the same number of arguments in subtype check";
          List.iter2 (subtyp l env) typ_args2 typ_args1;
          subtyp l env ret_typ1 ret_typ2
      | _, _ -> (
          match (destruct_exist_plain typ1, destruct_exist (canonicalize env typ2)) with
          | Some (kopts, nc, typ1), _ ->
              let env = add_existential l kopts nc env in
              subtyp l env typ1 typ2
          | None, Some (kopts, nc, typ2) ->
              typ_debug (lazy "Subtype check with unification");
              let orig_env = env in
              let typ1, env = bind_existential l None (canonicalize env typ1) env in
              let env = add_typ_vars l kopts env in
              let kids' =
                KidSet.elements (KidSet.diff (KidSet.of_list (List.map kopt_kid kopts)) (tyvars_of_typ typ2))
              in
              if not (kids' = []) then typ_error l "Universally quantified constraint generated" else ();
              let unifiers =
                try unify l env (KidSet.diff (tyvars_of_typ typ2) (tyvars_of_typ typ1)) typ2 typ1
                with Unification_error (_, m) -> typ_error l m
              in
              let nc =
                List.fold_left (fun nc (kid, uvar) -> constraint_subst kid uvar nc) nc (KBindings.bindings unifiers)
              in
              let env = List.fold_left unifier_constraint env (KBindings.bindings unifiers) in
              if prove __POS__ env nc then ()
              else
                typ_raise l
                  (Err_subtype (typ1, typ2, Some nc, Env.get_constraint_reasons orig_env, Env.get_typ_vars_info env))
          | None, None ->
              typ_raise l (Err_subtype (typ1, typ2, None, Env.get_constraint_reasons env, Env.get_typ_vars_info env))
        )
    )

and subtyp_arg l env (A_aux (aux1, _) as arg1) (A_aux (aux2, _) as arg2) =
  typ_print
    (lazy (("Subtype arg " |> Util.green |> Util.clear) ^ string_of_typ_arg arg1 ^ " and " ^ string_of_typ_arg arg2));
  let raise_failed_constraint nc =
    typ_raise l (Err_failed_constraint (nc, Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env))
  in
  match (aux1, aux2) with
  | A_nexp n1, A_nexp n2 ->
      let check = nc_eq n1 n2 in
      if not (prove __POS__ env check) then raise_failed_constraint check
  | A_typ typ1, A_typ typ2 -> subtyp l env typ1 typ2
  | A_bool nc1, A_bool nc2 ->
      let check = nc_and (nc_or (nc_not nc1) nc2) (nc_or (nc_not nc2) nc1) in
      if not (prove __POS__ env check) then raise_failed_constraint check
  | _, _ -> typ_error l "Mismatched argument types in sub-typing check"

let typ_equality l env typ1 typ2 =
  subtyp l env typ1 typ2;
  subtyp l env typ2 typ1

let subtype_check env typ1 typ2 =
  try
    subtyp Parse_ast.Unknown env typ1 typ2;
    true
  with Type_error _ -> false

(**************************************************************************)
(* 4. Removing sizeof expressions                                         *)
(**************************************************************************)

exception No_simple_rewrite

let rec move_to_front p ys = function
  | x :: xs when p x -> x :: (ys @ xs)
  | x :: xs -> move_to_front p (x :: ys) xs
  | [] -> ys

let rec rewrite_sizeof' l env (Nexp_aux (aux, _) as nexp) =
  let mk_exp exp = mk_exp ~loc:l exp in
  match aux with
  | Nexp_var v ->
      (* Use a simple heuristic to find the most likely local we can
         use, and move it to the front of the list. *)
      let str = string_of_kid v in
      let likely =
        try
          let n = if str.[1] = '_' then 2 else 1 in
          String.sub str n (String.length str - n)
        with Invalid_argument _ -> str
      in
      let locals = Env.get_locals env |> Bindings.bindings in
      let locals = move_to_front (fun local -> likely = string_of_id (fst local)) [] locals in
      let same_size (_, (_, Typ_aux (aux, _))) =
        match aux with
        | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var v', _)), _)])
          when string_of_id id = "atom" && Kid.compare v v' = 0 ->
            true
        | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "atom" -> prove __POS__ env (nc_eq (nvar v) n)
        | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var v', _)), _)]) when string_of_id id = "bitvector" ->
            Kid.compare v v' = 0
        | _ -> false
      in
      begin
        match List.find_opt same_size locals with
        | Some (id, _) -> mk_exp (E_app (mk_id "__size", [mk_exp (E_id id)]))
        | None -> raise No_simple_rewrite
      end
  | Nexp_constant c -> mk_lit_exp ~loc:l (L_num c)
  | Nexp_neg nexp ->
      let exp = rewrite_sizeof' l env nexp in
      mk_exp (E_app (mk_id "negate_atom", [exp]))
  | Nexp_sum (nexp1, nexp2) ->
      let exp1 = rewrite_sizeof' l env nexp1 in
      let exp2 = rewrite_sizeof' l env nexp2 in
      mk_exp (E_app (mk_id "add_atom", [exp1; exp2]))
  | Nexp_minus (nexp1, nexp2) ->
      let exp1 = rewrite_sizeof' l env nexp1 in
      let exp2 = rewrite_sizeof' l env nexp2 in
      mk_exp (E_app (mk_id "sub_atom", [exp1; exp2]))
  | Nexp_times (nexp1, nexp2) ->
      let exp1 = rewrite_sizeof' l env nexp1 in
      let exp2 = rewrite_sizeof' l env nexp2 in
      mk_exp (E_app (mk_id "mult_atom", [exp1; exp2]))
  | Nexp_exp nexp ->
      let exp = rewrite_sizeof' l env nexp in
      mk_exp (E_app (mk_id "pow2", [exp]))
  (* SMT solver div/mod is euclidian, so we must use those versions of
     div and mod in lib/smt.sail *)
  | Nexp_app (id, [nexp1; nexp2]) when string_of_id id = "div" ->
      let exp1 = rewrite_sizeof' l env nexp1 in
      let exp2 = rewrite_sizeof' l env nexp2 in
      mk_exp (E_app (mk_id "ediv_int", [exp1; exp2]))
  | Nexp_app (id, [nexp1; nexp2]) when string_of_id id = "mod" ->
      let exp1 = rewrite_sizeof' l env nexp1 in
      let exp2 = rewrite_sizeof' l env nexp2 in
      mk_exp (E_app (mk_id "emod_int", [exp1; exp2]))
  | Nexp_app _ | Nexp_id _ -> typ_error l ("Cannot re-write sizeof(" ^ string_of_nexp nexp ^ ")")

let rewrite_sizeof l env nexp =
  try rewrite_sizeof' l env nexp
  with No_simple_rewrite ->
    let locals = Env.get_locals env |> Bindings.bindings in
    let same_size (_, (_, Typ_aux (aux, _))) =
      match aux with
      | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "atom" -> prove __POS__ env (nc_eq nexp n)
      | _ -> false
    in
    begin
      match List.find_opt same_size locals with
      | Some (id, _) -> mk_exp (E_app (mk_id "__size", [mk_exp (E_id id)]))
      | None -> (
          match solve_unique env nexp with
          | Some n -> mk_lit_exp (L_num n)
          | None -> typ_error l ("Cannot re-write sizeof(" ^ string_of_nexp nexp ^ ")")
        )
    end

let rec rewrite_nc env (NC_aux (nc_aux, l)) = mk_exp ~loc:l (rewrite_nc_aux l env nc_aux)

and rewrite_nc_aux l env =
  let mk_exp exp = mk_exp ~loc:l exp in
  function
  | NC_bounded_ge (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id ">=", mk_exp (E_sizeof n2))
  | NC_bounded_gt (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id ">", mk_exp (E_sizeof n2))
  | NC_bounded_le (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "<=", mk_exp (E_sizeof n2))
  | NC_bounded_lt (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "<", mk_exp (E_sizeof n2))
  | NC_equal (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "==", mk_exp (E_sizeof n2))
  | NC_not_equal (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "!=", mk_exp (E_sizeof n2))
  | NC_and (nc1, nc2) -> E_app_infix (rewrite_nc env nc1, mk_id "&", rewrite_nc env nc2)
  | NC_or (nc1, nc2) -> E_app_infix (rewrite_nc env nc1, mk_id "|", rewrite_nc env nc2)
  | NC_false -> E_lit (mk_lit L_false)
  | NC_true -> E_lit (mk_lit L_true)
  | NC_set (_, []) -> E_lit (mk_lit L_false)
  | NC_set (kid, int :: ints) ->
      let kid_eq kid int = nc_eq (nvar kid) (nconstant int) in
      unaux_exp (rewrite_nc env (List.fold_left (fun nc int -> nc_or nc (kid_eq kid int)) (kid_eq kid int) ints))
  | NC_app (f, [A_aux (A_bool nc, _)]) when string_of_id f = "not" -> E_app (mk_id "not_bool", [rewrite_nc env nc])
  | NC_app (f, args) -> unaux_exp (rewrite_nc env (Env.expand_constraint_synonyms env (mk_nc (NC_app (f, args)))))
  | NC_var v ->
      (* Would be better to translate change E_sizeof to take a kid, then rewrite to E_sizeof *)
      E_id (id_of_kid v)

(**************************************************************************)
(* 5. Type checking expressions                                           *)
(**************************************************************************)

(* The type checker produces a fully annoted AST - tannot is the type
   of these type annotations.  The extra typ option is the expected type,
   that is, the type that the AST node was checked against, if there was one. *)
type tannot' = {
  env : Env.t;
  typ : typ;
  monadic : effect;
  expected : typ option;
  instantiation : typ_arg KBindings.t option;
}

type tannot = tannot' option * uannot

let untyped_annot tannot = snd tannot

let mk_tannot ?(uannot = empty_uannot) env typ : tannot =
  (Some { env; typ = Env.expand_synonyms env typ; monadic = no_effect; expected = None; instantiation = None }, uannot)

let mk_expected_tannot ?(uannot = empty_uannot) env typ expected : tannot =
  (Some { env; typ = Env.expand_synonyms env typ; monadic = no_effect; expected; instantiation = None }, uannot)

let get_instantiations = function None, _ -> None | Some t, _ -> t.instantiation

let empty_tannot = (None, empty_uannot)

let is_empty_tannot tannot = match fst tannot with None -> true | Some _ -> false

let map_uannot f (t, uannot) = (t, f uannot)

let destruct_tannot tannot = Option.map (fun t -> (t.env, t.typ)) (fst tannot)

let string_of_tannot tannot =
  match destruct_tannot tannot with Some (_, typ) -> "Some (_, " ^ string_of_typ typ ^ ")" | None -> "None"

let replace_typ typ = function Some t, u -> (Some { t with typ }, u) | None, u -> (None, u)

let replace_env env = function Some t, u -> (Some { t with env }, u) | None, u -> (None, u)

(* Helpers for implicit arguments in infer_funapp' *)
let is_not_implicit (Typ_aux (aux, _)) =
  match aux with
  | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var _, _)), _)]) when string_of_id id = "implicit" -> false
  | _ -> true

let implicit_to_int (Typ_aux (aux, l)) =
  match aux with
  | Typ_app (id, args) when string_of_id id = "implicit" -> Typ_aux (Typ_app (mk_id "atom", args), l)
  | _ -> Typ_aux (aux, l)

let rec get_implicits typs =
  match typs with
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var impl, _)), _)]), _) :: typs
    when string_of_id id = "implicit" ->
      impl :: get_implicits typs
  | _ :: typs -> get_implicits typs
  | [] -> []

let infer_lit env (L_aux (lit_aux, l)) =
  match lit_aux with
  | L_unit -> unit_typ
  | L_zero -> bit_typ
  | L_one -> bit_typ
  | L_num n -> atom_typ (nconstant n)
  | L_true -> atom_bool_typ nc_true
  | L_false -> atom_bool_typ nc_false
  | L_string _ -> string_typ
  | L_real _ -> real_typ
  | L_bin str -> bits_typ env (nint (String.length str))
  | L_hex str -> bits_typ env (nint (String.length str * 4))
  | L_undef -> typ_error l "Cannot infer the type of undefined"

let instantiate_simple_equations =
  let rec find_eqs kid (NC_aux (nc, _)) =
    match nc with
    | NC_equal (Nexp_aux (Nexp_var kid', _), nexp)
      when Kid.compare kid kid' == 0 && not (KidSet.mem kid (nexp_frees nexp)) ->
        [arg_nexp nexp]
    | NC_and (nexp1, nexp2) -> find_eqs kid nexp1 @ find_eqs kid nexp2
    | _ -> []
  in
  let find_eqs_quant kid (QI_aux (qi, _)) = match qi with QI_id _ -> [] | QI_constraint nc -> find_eqs kid nc in
  let rec inst_from_eq = function
    | [] -> KBindings.empty
    | QI_aux (QI_id kinded_kid, _) :: quants ->
        let kid = kopt_kid kinded_kid in
        let insts_tl = inst_from_eq quants in
        begin
          match List.concat (List.map (find_eqs_quant kid) quants) with
          | [] -> insts_tl
          | h :: _ -> KBindings.add kid h (KBindings.map (typ_arg_subst kid h) insts_tl)
        end
    | _ :: quants -> inst_from_eq quants
  in
  inst_from_eq

type destructed_vector = Destruct_vector of nexp * typ | Destruct_bitvector of nexp

let destruct_any_vector_typ l env typ =
  let destruct_any_vector_typ' l = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _)]), _) when string_of_id id = "bitvector" -> Destruct_bitvector n1
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _); A_aux (A_typ vtyp, _)]), _) when string_of_id id = "vector" ->
        Destruct_vector (n1, vtyp)
    | typ -> typ_error l ("Expected vector or bitvector type, got " ^ string_of_typ typ)
  in
  destruct_any_vector_typ' l (Env.expand_synonyms env typ)

let destruct_vector_typ l env typ =
  let destruct_vector_typ' l = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _); A_aux (A_typ vtyp, _)]), _) when string_of_id id = "vector" ->
        (n1, vtyp)
    | typ -> typ_error l ("Expected vector type, got " ^ string_of_typ typ)
  in
  destruct_vector_typ' l (Env.expand_synonyms env typ)

let destruct_bitvector_typ l env typ =
  let destruct_bitvector_typ' l = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _)]), _) when string_of_id id = "bitvector" -> n1
    | typ -> typ_error l ("Expected bitvector type, got " ^ string_of_typ typ)
  in
  destruct_bitvector_typ' l (Env.expand_synonyms env typ)

let env_of_annot (l, tannot) =
  match fst tannot with Some t -> t.env | None -> raise (Reporting.err_unreachable l __POS__ "no type annotation")

let env_of_tannot tannot =
  match fst tannot with
  | Some t -> t.env
  | None -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "no type annotation")

let typ_of_tannot tannot =
  match fst tannot with
  | Some t -> t.typ
  | None -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "no type annotation")

let typ_of_annot (l, tannot) =
  match fst tannot with Some t -> t.typ | None -> raise (Reporting.err_unreachable l __POS__ "no type annotation")

let typ_of (E_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of (E_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_pat (P_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_pat (P_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_pexp (Pat_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_pexp (Pat_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_mpat (MP_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_mpat (MP_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_mpexp (MPat_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_mpexp (MPat_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let lexp_typ_of (LE_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let expected_typ_of (l, tannot) =
  match fst tannot with Some t -> t.expected | None -> raise (Reporting.err_unreachable l __POS__ "no type annotation")

(* Flow typing *)

type simple_numeric = Equal of nexp | Constraint of (kid -> n_constraint) | Anything

let to_simple_numeric l kids nc (Nexp_aux (aux, _) as n) =
  match (aux, kids) with
  | Nexp_var v, [v'] when Kid.compare v v' = 0 -> Constraint (fun subst -> constraint_subst v (arg_nexp (nvar subst)) nc)
  | _, [] -> Equal n
  | _ -> typ_error l "Numeric type is non-simple"

let union_simple_numeric ex1 ex2 =
  match (ex1, ex2) with
  | Equal nexp1, Equal nexp2 -> Constraint (fun kid -> nc_or (nc_eq (nvar kid) nexp1) (nc_eq (nvar kid) nexp2))
  | Equal nexp, Constraint c -> Constraint (fun kid -> nc_or (nc_eq (nvar kid) nexp) (c kid))
  | Constraint c, Equal nexp -> Constraint (fun kid -> nc_or (c kid) (nc_eq (nvar kid) nexp))
  | _, _ -> Anything

let typ_of_simple_numeric = function
  | Anything -> int_typ
  | Equal nexp -> atom_typ nexp
  | Constraint c -> exist_typ Parse_ast.Unknown c (fun kid -> atom_typ (nvar kid))

let rec big_int_of_nexp (Nexp_aux (nexp, _)) =
  match nexp with
  | Nexp_constant c -> Some c
  | Nexp_times (n1, n2) -> Util.option_binop Big_int.add (big_int_of_nexp n1) (big_int_of_nexp n2)
  | Nexp_sum (n1, n2) -> Util.option_binop Big_int.add (big_int_of_nexp n1) (big_int_of_nexp n2)
  | Nexp_minus (n1, n2) -> Util.option_binop Big_int.add (big_int_of_nexp n1) (big_int_of_nexp n2)
  | Nexp_exp n -> Option.map (fun n -> Big_int.pow_int_positive 2 (Big_int.to_int n)) (big_int_of_nexp n)
  | _ -> None

let assert_nexp env exp = destruct_atom_nexp env (typ_of exp)

let combine_constraint b f x y =
  match (b, x, y) with
  | true, Some x, Some y -> Some (f x y)
  | true, Some x, None -> Some x
  | true, None, Some y -> Some y
  | false, Some x, Some y -> Some (f x y)
  | _, _, _ -> None

let rec assert_constraint env b (E_aux (exp_aux, _) as exp) =
  typ_debug ~level:2 (lazy ("Asserting constraint for " ^ string_of_exp exp ^ " : " ^ string_of_typ (typ_of exp)));
  match typ_of exp with
  | Typ_aux (Typ_app (Id_aux (Id "atom_bool", _), [A_aux (A_bool nc, _)]), _) -> Some nc
  | _ -> (
      match exp_aux with
      | E_constraint nc -> Some nc
      | E_lit (L_aux (L_true, _)) -> Some nc_true
      | E_lit (L_aux (L_false, _)) -> Some nc_false
      | E_let (_, e) -> assert_constraint env b e (* TODO: beware of fresh type vars *)
      | E_app (op, [x; y]) when string_of_id op = "or_bool" ->
          combine_constraint (not b) nc_or (assert_constraint env b x) (assert_constraint env b y)
      | E_app (op, [x; y]) when string_of_id op = "and_bool" ->
          combine_constraint b nc_and (assert_constraint env b x) (assert_constraint env b y)
      | E_app (op, [x; y]) when string_of_id op = "gteq_int" ->
          option_binop nc_gteq (assert_nexp env x) (assert_nexp env y)
      | E_app (op, [x; y]) when string_of_id op = "lteq_int" ->
          option_binop nc_lteq (assert_nexp env x) (assert_nexp env y)
      | E_app (op, [x; y]) when string_of_id op = "gt_int" -> option_binop nc_gt (assert_nexp env x) (assert_nexp env y)
      | E_app (op, [x; y]) when string_of_id op = "lt_int" -> option_binop nc_lt (assert_nexp env x) (assert_nexp env y)
      | E_app (op, [x; y]) when string_of_id op = "eq_int" -> option_binop nc_eq (assert_nexp env x) (assert_nexp env y)
      | E_app (op, [x; y]) when string_of_id op = "neq_int" ->
          option_binop nc_neq (assert_nexp env x) (assert_nexp env y)
      | _ -> None
    )

let add_opt_constraint l reason constr env =
  match constr with None -> env | Some constr -> Env.add_constraint ~reason:(l, reason) constr env

let solve_quant env = function QI_aux (QI_id _, _) -> false | QI_aux (QI_constraint nc, _) -> prove __POS__ env nc

let check_function_instantiation l id env bind1 bind2 =
  let direction check (typq1, typ1) (typq2, typ2) =
    if quant_items typq1 <> [] && quant_items typq2 <> [] then (
      let check_env = Env.add_typquant l typq1 env in
      let typq2, typ2 = Env.freshen_bind check_env (typq2, typ2) in
      let unifiers =
        try unify l check_env (quant_kopts typq2 |> List.map kopt_kid |> KidSet.of_list) typ2 typ1
        with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
      in

      let quants = List.fold_left instantiate_quants (quant_items typq2) (KBindings.bindings unifiers) in
      if not (List.for_all (solve_quant check_env) quants) then
        typ_raise l
          (Err_unresolved_quants (id, quants, Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env));
      let typ2 = subst_unifiers unifiers typ2 in

      check check_env typ1 typ2
    )
    else check env typ1 typ2
  in
  try direction (fun check_env typ1 typ2 -> subtyp l check_env typ1 typ2) bind1 bind2
  with Type_error (l1, err1) -> (
    try direction (fun check_env typ1 typ2 -> subtyp l check_env typ2 typ1) bind2 bind1
    with Type_error (l2, err2) -> typ_raise l2 (Err_inner (err2, l1, "Also tried", None, err1))
  )

type pattern_duplicate = Pattern_singleton of l | Pattern_duplicate of l * l

let is_enum_member id env = match Env.lookup_id id env with Enum _ -> true | _ -> false

(* Check if a pattern contains duplicate bindings, and raise a type
   error if this is the case *)
let check_pattern_duplicates env pat =
  let is_duplicate _ = function Pattern_duplicate _ -> true | _ -> false in
  let one_loc = function Pattern_singleton l -> l | Pattern_duplicate (l, _) -> l in
  let ids = ref Bindings.empty in
  let subrange_ids = ref Bindings.empty in
  let rec collect_duplicates (P_aux (aux, (l, _))) =
    let update_id = function
      | None -> Some (Pattern_singleton l)
      | Some (Pattern_singleton l2) -> Some (Pattern_duplicate (l2, l))
      | duplicate -> duplicate
    in
    match aux with
    | P_id id when not (is_enum_member id env) -> ids := Bindings.update id update_id !ids
    | P_vector_subrange (id, _, _) -> subrange_ids := Bindings.add id l !subrange_ids
    | P_as (p, id) ->
        ids := Bindings.update id update_id !ids;
        collect_duplicates p
    | P_id _ | P_lit _ | P_wild -> ()
    | P_not p | P_typ (_, p) | P_var (p, _) -> collect_duplicates p
    | P_or (p1, p2) | P_cons (p1, p2) ->
        collect_duplicates p1;
        collect_duplicates p2
    | P_app (_, ps) | P_vector ps | P_vector_concat ps | P_tuple ps | P_list ps | P_string_append ps ->
        List.iter collect_duplicates ps
    | P_struct (fpats, _) -> List.iter (fun (_, pat) -> collect_duplicates pat) fpats
  in
  collect_duplicates pat;
  match Bindings.choose_opt (Bindings.filter is_duplicate !ids) with
  | Some (id, Pattern_duplicate (l1, l2)) ->
      typ_raise l2
        (err_because
           ( Err_other ("Duplicate binding for " ^ string_of_id id ^ " in pattern"),
             l1,
             Err_other ("Previous binding of " ^ string_of_id id ^ " here")
           )
        )
  | _ ->
      Bindings.iter
        (fun subrange_id l ->
          match Bindings.find_opt subrange_id !ids with
          | Some pattern_info ->
              typ_raise l
                (err_because
                   ( Err_other
                       ("Vector subrange binding " ^ string_of_id subrange_id ^ " is also bound as a regular identifier"),
                     one_loc pattern_info,
                     Err_other "Regular binding is here"
                   )
                )
          | None -> ()
        )
        !subrange_ids;
      !ids

(* Test that the output of two calls to check pattern duplicates refer to the same identifiers *)
let same_bindings env lhs rhs =
  match Bindings.find_first_opt (fun id -> not (Bindings.mem id rhs)) lhs with
  | Some (id, _) ->
      typ_error (id_loc id) ("Identifier " ^ string_of_id id ^ " found on left hand side of mapping, but not on right")
  | None -> (
      match Bindings.find_first_opt (fun id -> not (Bindings.mem id lhs)) rhs with
      | Some (id, _) ->
          typ_error (id_loc id)
            ("Identifier " ^ string_of_id id ^ " found on right hand side of mapping, but not on left")
      | None -> ()
    )

let bitvector_typ_from_range l env n m =
  let len =
    match Env.get_default_order env with
    | Ord_aux (Ord_dec, _) ->
        if Big_int.greater_equal n m then Big_int.sub (Big_int.succ n) m
        else
          typ_error l
            (Printf.sprintf "First index %s must be greater than or equal to second index %s (when default Order dec)"
               (Big_int.to_string n) (Big_int.to_string m)
            )
    | Ord_aux (Ord_inc, _) ->
        if Big_int.less_equal n m then Big_int.sub (Big_int.succ m) n
        else
          typ_error l
            (Printf.sprintf "First index %s must be less than or equal to second index %s (when default Order inc)"
               (Big_int.to_string n) (Big_int.to_string m)
            )
  in
  bitvector_typ (nconstant len)

let bind_pattern_vector_subranges (P_aux (_, (l, _)) as pat) env =
  let id_ranges = pattern_vector_subranges pat in
  Bindings.fold
    (fun id ranges env ->
      match ranges with
      | [(n, m)] -> Env.add_local id (Immutable, bitvector_typ_from_range l env n m) env
      | _ :: (m, _) :: _ ->
          typ_error l
            (Printf.sprintf "Cannot bind %s as pattern subranges are non-contiguous. %s[%s] is not defined."
               (string_of_id id) (string_of_id id)
               (Big_int.to_string (Big_int.succ m))
            )
      | _ -> Reporting.unreachable l __POS__ "Found range pattern with no range"
    )
    id_ranges env

let crule r env exp typ =
  incr depth;
  typ_print (lazy (Util.("Check " |> cyan |> clear) ^ string_of_exp exp ^ " <= " ^ string_of_typ typ));
  try
    let checked_exp = r env exp typ in
    Env.wf_typ env (typ_of checked_exp);
    decr depth;
    checked_exp
  with Type_error (l, err) ->
    decr depth;
    typ_raise l err

let irule r env exp =
  incr depth;
  try
    let inferred_exp = r env exp in
    typ_print
      (lazy (Util.("Infer " |> blue |> clear) ^ string_of_exp exp ^ " => " ^ string_of_typ (typ_of inferred_exp)));
    Env.wf_typ env (typ_of inferred_exp);
    decr depth;
    inferred_exp
  with Type_error (l, err) ->
    decr depth;
    typ_raise l err

(* This function adds useful assertion messages to asserts missing them *)
let assert_msg = function
  | E_aux (E_lit (L_aux (L_string "", _)), (l, _)) ->
      let open Reporting in
      locate (fun _ -> l) (mk_lit_exp (L_string (short_loc_to_string l)))
  | msg -> msg

let strip_exp exp = map_exp_annot (fun (l, tannot) -> (l, untyped_annot tannot)) exp
let strip_pat pat = map_pat_annot (fun (l, tannot) -> (l, untyped_annot tannot)) pat
let strip_pexp pexp = map_pexp_annot (fun (l, tannot) -> (l, untyped_annot tannot)) pexp
let strip_lexp lexp = map_lexp_annot (fun (l, tannot) -> (l, untyped_annot tannot)) lexp

let strip_letbind lb = map_letbind_annot (fun (l, tannot) -> (l, untyped_annot tannot)) lb
let strip_mpat mpat = map_mpat_annot (fun (l, tannot) -> (l, untyped_annot tannot)) mpat
let strip_mpexp mpexp = map_mpexp_annot (fun (l, tannot) -> (l, untyped_annot tannot)) mpexp
let strip_mapcl mapcl = map_mapcl_annot (fun (l, tannot) -> (l, untyped_annot tannot)) mapcl
let strip_funcl funcl = map_funcl_annot (fun (l, tannot) -> (l, untyped_annot tannot)) funcl
let strip_val_spec vs = map_valspec_annot (fun (l, tannot) -> (l, untyped_annot tannot)) vs
let strip_register r = map_register_annot (fun (l, tannot) -> (l, untyped_annot tannot)) r
let strip_typedef td = map_typedef_annot (fun (l, tannot) -> (l, untyped_annot tannot)) td
let strip_def def = map_def_annot (fun (l, tannot) -> (l, untyped_annot tannot)) def
let strip_ast ast = map_ast_annot (fun (l, tannot) -> (l, untyped_annot tannot)) ast

(* A L-expression can either be declaring new variables, or updating existing variables, but never a mix of the two *)
type lexp_assignment_type = Declaration | Update

let is_update = function Update -> true | Declaration -> false

let is_declaration = function Update -> false | Declaration -> true

let rec lexp_assignment_type env (LE_aux (aux, (l, _))) =
  match aux with
  | LE_id v -> begin
      match Env.lookup_id v env with
      | Register _ | Local (Mutable, _) -> Update
      | Unbound _ -> Declaration
      | Local (Immutable, _) | Enum _ ->
          typ_error l ("Cannot modify immutable let-bound constant or enumeration constructor " ^ string_of_id v)
    end
  | LE_typ (_, v) -> begin
      match Env.lookup_id v env with
      | Register _ | Local (Mutable, _) ->
          Reporting.warn ("Redundant type annotation on assignment to " ^ string_of_id v) l "Type is already known";
          Update
      | Unbound _ -> Declaration
      | Local (Immutable, _) | Enum _ ->
          typ_error l ("Cannot modify immutable let-bound constant or enumeration constructor " ^ string_of_id v)
    end
  | LE_deref _ | LE_app _ -> Update
  | LE_field (lexp, _) -> begin
      match lexp_assignment_type env lexp with
      | Update -> Update
      | Declaration -> typ_error l "Field assignment can only be done to a variable that has already been declared"
    end
  | LE_vector (lexp, _) | LE_vector_range (lexp, _, _) -> begin
      match lexp_assignment_type env lexp with
      | Update -> Update
      | Declaration -> typ_error l "Vector assignment can only be done to a variable that has already been declared"
    end
  | LE_tuple lexps | LE_vector_concat lexps ->
      let lexp_is_update lexp = lexp_assignment_type env lexp |> is_update in
      let lexp_is_declaration lexp = lexp_assignment_type env lexp |> is_declaration in
      begin
        match (List.find_opt lexp_is_update lexps, List.find_opt lexp_is_declaration lexps) with
        | Some (LE_aux (_, (l_u, _))), Some (LE_aux (_, (l_d, _)) as lexp_d) ->
            typ_raise l_d
              (Err_inner
                 ( Err_other
                     ("Assignment declaring new variable " ^ string_of_lexp lexp_d
                    ^ " is also assigning to an existing variable"
                     ),
                   l_u,
                   "",
                   Some "existing variable",
                   Err_other ""
                 )
              )
        | None, _ -> Declaration
        | _, None -> Update
      end

let fresh_var =
  let counter = ref 0 in
  fun () ->
    let n = !counter in
    let () = counter := n + 1 in
    mk_id ("v#" ^ string_of_int n)

let rec exp_unconditionally_returns (E_aux (aux, _)) =
  match aux with
  | E_return _ -> true
  | E_block [] -> false
  | E_block exps -> exp_unconditionally_returns (List.hd (List.rev exps))
  | _ -> false

let forwards_attr l uannot = add_attribute l "forwards" "" (remove_attribute "forwards" uannot)
let backwards_attr l uannot = add_attribute l "backwards" "" (remove_attribute "backwards" uannot)

let tc_assume nc (E_aux (aux, annot)) = E_aux (E_internal_assume (nc, E_aux (aux, annot)), annot)

type ('a, 'b) pattern_functions = {
  infer : Env.t -> 'a -> 'b * Env.t * uannot exp list;
  bind : Env.t -> 'a -> typ -> 'b * Env.t * uannot exp list;
  typ_of : 'b -> typ;
  get_loc : 'a -> l;
  get_loc_typed : 'b -> l;
}

module PC_config = struct
  type t = tannot
  let typ_of_t = typ_of_tannot
  let add_attribute l attr arg = map_uannot (add_attribute l attr arg)
end

module PC = Pattern_completeness.Make (PC_config)

let pattern_completeness_ctx env =
  {
    Pattern_completeness.variants = Env.get_variants env;
    Pattern_completeness.structs = Env.get_records env;
    Pattern_completeness.enums = Env.get_enums env;
    Pattern_completeness.constraints = Env.get_constraints env;
  }

let rec check_exp env (E_aux (exp_aux, (l, uannot)) as exp : uannot exp) (Typ_aux (typ_aux, _) as typ) : tannot exp =
  let annot_exp exp typ' = E_aux (exp, (l, mk_expected_tannot ~uannot env typ' (Some typ))) in
  let update_uannot f (E_aux (aux, (l, (tannot, uannot)))) = E_aux (aux, (l, (tannot, f uannot))) in
  match (exp_aux, typ_aux) with
  | E_block exps, _ -> annot_exp (E_block (check_block l env exps (Some typ))) typ
  | E_match (exp, cases), _ ->
      let inferred_exp =
        if Option.is_some (get_attribute "mapping_match" uannot) then
          crule check_exp env exp (app_typ (mk_id "option") [mk_typ_arg (A_typ typ)])
        else irule infer_exp env exp
      in
      let inferred_typ = typ_of inferred_exp in
      let checked_cases = List.map (fun case -> check_case env inferred_typ case typ) cases in
      let checked_cases, attr_update =
        if Option.is_some (get_attribute "complete" uannot) || Option.is_some (get_attribute "incomplete" uannot) then
          (checked_cases, fun attrs -> attrs)
        else (
          let ctx = pattern_completeness_ctx env in
          match PC.is_complete_wildcarded l ctx checked_cases inferred_typ with
          | Some wildcarded -> (wildcarded, add_attribute (gen_loc l) "complete" "")
          | None -> (checked_cases, add_attribute (gen_loc l) "incomplete" "")
        )
      in
      annot_exp (E_match (inferred_exp, checked_cases)) typ |> update_uannot attr_update
  | E_try (exp, cases), _ ->
      let checked_exp = crule check_exp env exp typ in
      annot_exp (E_try (checked_exp, List.map (fun case -> check_case env exc_typ case typ) cases)) typ
  | E_cons (x, xs), _ -> begin
      match is_list (Env.expand_synonyms env typ) with
      | Some elem_typ ->
          let checked_xs = crule check_exp env xs typ in
          let checked_x = crule check_exp env x elem_typ in
          annot_exp (E_cons (checked_x, checked_xs)) typ
      | None -> typ_error l ("Cons " ^ string_of_exp exp ^ " must have list type, got " ^ string_of_typ typ)
    end
  | E_list xs, _ -> begin
      match is_list (Env.expand_synonyms env typ) with
      | Some elem_typ ->
          let checked_xs = List.map (fun x -> crule check_exp env x elem_typ) xs in
          annot_exp (E_list checked_xs) typ
      | None -> typ_error l ("List " ^ string_of_exp exp ^ " must have list type, got " ^ string_of_typ typ)
    end
  | E_struct_update (exp, fexps), _ ->
      let checked_exp = crule check_exp env exp typ in
      let rectyp_id =
        match Env.expand_synonyms env typ with
        | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
            rectyp_id
        | _ -> typ_error l ("The type " ^ string_of_typ typ ^ " is not a record")
      in
      let check_fexp (FE_aux (FE_fexp (field, exp), (l, _))) =
        let _, rectyp_q, field_typ = Env.get_accessor rectyp_id field env in
        let unifiers =
          try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ
          with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
        in
        let field_typ' = subst_unifiers unifiers field_typ in
        let checked_exp = crule check_exp env exp field_typ' in
        FE_aux (FE_fexp (field, checked_exp), (l, empty_tannot))
      in
      annot_exp (E_struct_update (checked_exp, List.map check_fexp fexps)) typ
  | E_struct fexps, _ ->
      let rectyp_id =
        match Env.expand_synonyms env typ with
        | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
            rectyp_id
        | _ -> typ_error l ("The type " ^ string_of_typ typ ^ " is not a record")
      in
      let record_fields = ref (Env.get_record rectyp_id env |> snd |> List.map snd |> IdSet.of_list) in
      let check_fexp (FE_aux (FE_fexp (field, exp), (l, _))) =
        record_fields := IdSet.remove field !record_fields;
        let _, rectyp_q, field_typ = Env.get_accessor rectyp_id field env in
        let unifiers =
          try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ
          with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
        in
        let field_typ' = subst_unifiers unifiers field_typ in
        let checked_exp = crule check_exp env exp field_typ' in
        FE_aux (FE_fexp (field, checked_exp), (l, empty_tannot))
      in
      let fexps = List.map check_fexp fexps in
      if IdSet.is_empty !record_fields then annot_exp (E_struct fexps) typ
      else
        typ_error l
          ("struct literal missing fields: " ^ string_of_list ", " string_of_id (IdSet.elements !record_fields))
  | E_let (LB_aux (letbind, (let_loc, _)), exp), _ -> begin
      match letbind with
      | LB_val ((P_aux (P_typ (ptyp, _), _) as pat), bind) ->
          Env.wf_typ env ptyp;
          let checked_bind = crule check_exp env bind ptyp in
          ignore (check_pattern_duplicates env pat);
          let env = bind_pattern_vector_subranges pat env in
          let tpat, inner_env = bind_pat_no_guard env pat ptyp in
          annot_exp
            (E_let (LB_aux (LB_val (tpat, checked_bind), (let_loc, empty_tannot)), crule check_exp inner_env exp typ))
            (check_shadow_leaks l inner_env env typ)
      | LB_val (pat, bind) ->
          let inferred_bind = irule infer_exp env bind in
          ignore (check_pattern_duplicates env pat);
          let tpat, inner_env = bind_pat_no_guard env pat (typ_of inferred_bind) in
          annot_exp
            (E_let (LB_aux (LB_val (tpat, inferred_bind), (let_loc, empty_tannot)), crule check_exp inner_env exp typ))
            (check_shadow_leaks l inner_env env typ)
    end
  | E_app_infix (x, op, y), _ -> check_exp env (E_aux (E_app (deinfix op, [x; y]), (l, uannot))) typ
  | E_app (f, [E_aux (E_constraint nc, _)]), _ when string_of_id f = "_prove" ->
      Env.wf_constraint env nc;
      if prove __POS__ env nc then annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
      else typ_error l ("Cannot prove " ^ string_of_n_constraint nc)
  | E_app (f, [E_aux (E_constraint nc, _)]), _ when string_of_id f = "_not_prove" ->
      Env.wf_constraint env nc;
      if prove __POS__ env nc then typ_error l ("Can prove " ^ string_of_n_constraint nc)
      else annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
  | E_app (f, [E_aux (E_typ (typ, exp), _)]), _ when string_of_id f = "_check" ->
      Env.wf_typ env typ;
      let _ = crule check_exp env exp typ in
      annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
  | E_app (f, [E_aux (E_typ (typ, exp), _)]), _ when string_of_id f = "_not_check" ->
      Env.wf_typ env typ;
      if
        try
          ignore (crule check_exp env exp typ);
          false
        with Type_error _ -> true
      then annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
      else typ_error l (Printf.sprintf "Expected _not_check(%s : %s) to fail" (string_of_exp exp) (string_of_typ typ))
  (* All constructors and mappings are treated as having one argument
     so Ctor(x, y) is checked as Ctor((x, y)) *)
  | E_app (f, x :: y :: zs), _ when Env.is_union_constructor f env || Env.is_mapping f env ->
      typ_print (lazy ("Checking multiple argument constructor or mapping: " ^ string_of_id f));
      crule check_exp env (mk_exp ~loc:l (E_app (f, [mk_exp ~loc:l (E_tuple (x :: y :: zs))]))) typ
  | E_app (mapping, xs), _ when Env.is_mapping mapping env ->
      let forwards_id = mk_id (string_of_id mapping ^ "_forwards") in
      let backwards_id = mk_id (string_of_id mapping ^ "_backwards") in
      typ_print
        ( lazy
          ("Trying forwards direction for mapping " ^ string_of_id mapping ^ "(" ^ string_of_list ", " string_of_exp xs
         ^ ")"
          )
          );
      begin
        try crule check_exp env (E_aux (E_app (forwards_id, xs), (l, uannot))) typ
        with Type_error (_, err1) ->
          typ_print
            ( lazy
              ("Trying backwards direction for mapping " ^ string_of_id mapping ^ "("
             ^ string_of_list ", " string_of_exp xs ^ ")"
              )
              );
          begin
            try crule check_exp env (E_aux (E_app (backwards_id, xs), (l, uannot))) typ
            with Type_error (_, err2) ->
              typ_raise l (Err_no_overloading (mapping, [(forwards_id, err1); (backwards_id, err2)]))
          end
      end
  | E_app (f, xs), _ when List.length (Env.get_overloads f env) > 0 ->
      let rec try_overload = function
        | errs, [] -> typ_raise l (Err_no_overloading (f, errs))
        | errs, f :: fs -> begin
            typ_print (lazy ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
            try crule check_exp env (E_aux (E_app (f, xs), (l, uannot))) typ
            with Type_error (_, err) ->
              typ_debug (lazy "Error");
              try_overload (errs @ [(f, err)], fs)
          end
      in
      try_overload ([], Env.get_overloads f env)
  | E_app (f, [x; y]), _ when string_of_id f = "and_bool" || string_of_id f = "or_bool" -> begin
      (* We have to ensure that the type of y in (x || y) and (x && y)
         is non-empty, otherwise it could force the entire type of the
         expression to become empty even when unevaluted due to
         short-circuiting. *)
      match destruct_exist (typ_of (irule infer_exp env y)) with
      | None | Some (_, NC_aux (NC_true, _), _) ->
          let inferred_exp = infer_funapp l env f [x; y] (Some typ) in
          expect_subtype env inferred_exp typ
      | Some _ ->
          let inferred_exp = infer_funapp l env f [x; mk_exp (E_typ (bool_typ, y))] (Some typ) in
          expect_subtype env inferred_exp typ
      | exception Type_error _ ->
          let inferred_exp = infer_funapp l env f [x; mk_exp (E_typ (bool_typ, y))] (Some typ) in
          expect_subtype env inferred_exp typ
    end
  | E_app (f, xs), _ ->
      let inferred_exp = infer_funapp l env f xs (Some typ) in
      expect_subtype env inferred_exp typ
  | E_return exp, _ ->
      let checked_exp =
        match Env.get_ret_typ env with
        | Some ret_typ -> crule check_exp env exp ret_typ
        | None -> typ_error l "Cannot use return outside a function"
      in
      annot_exp (E_return checked_exp) typ
  | E_tuple exps, Typ_tuple typs when List.length exps = List.length typs ->
      let checked_exps = List.map2 (fun exp typ -> crule check_exp env exp typ) exps typs in
      annot_exp (E_tuple checked_exps) typ
  | E_if (cond, then_branch, else_branch), _ ->
      let cond' = try irule infer_exp env cond with Type_error _ -> crule check_exp env cond bool_typ in
      begin
        match destruct_exist (typ_of cond') with
        | Some (kopts, nc, Typ_aux (Typ_app (ab, [A_aux (A_bool flow, _)]), _)) when string_of_id ab = "atom_bool" ->
            let env = add_existential l kopts nc env in
            let then_branch' =
              crule check_exp (Env.add_constraint ~reason:(l, "then branch") flow env) then_branch typ
            in
            let else_branch' =
              crule check_exp (Env.add_constraint ~reason:(l, "else branch") (nc_not flow) env) else_branch typ
            in
            annot_exp (E_if (cond', then_branch', else_branch')) typ
        | _ ->
            let cond' = expect_subtype env cond' bool_typ in
            let then_branch' =
              crule check_exp
                (add_opt_constraint l "then branch" (assert_constraint env true cond') env)
                then_branch typ
            in
            let else_branch' =
              crule check_exp
                (add_opt_constraint l "else branch" (Option.map nc_not (assert_constraint env false cond')) env)
                else_branch typ
            in
            annot_exp (E_if (cond', then_branch', else_branch')) typ
      end
  | E_exit exp, _ ->
      let checked_exp = crule check_exp env exp unit_typ in
      annot_exp (E_exit checked_exp) typ
  | E_throw exp, _ ->
      let checked_exp = crule check_exp env exp exc_typ in
      annot_exp (E_throw checked_exp) typ
  | E_var (lexp, bind, exp), _ -> begin
      match lexp_assignment_type env lexp with
      | Declaration ->
          let lexp, bind, env =
            match bind_assignment l env lexp bind with
            | E_aux (E_assign (lexp, bind), _), env -> (lexp, bind, env)
            | _, _ -> assert false
          in
          let checked_exp = crule check_exp env exp typ in
          annot_exp (E_var (lexp, bind, checked_exp)) typ
      | Update -> typ_error l "var expression can only be used to declare new variables, not update them"
    end
  | E_internal_return exp, _ ->
      let checked_exp = crule check_exp env exp typ in
      annot_exp (E_internal_return checked_exp) typ
  | E_internal_plet (pat, bind, body), _ ->
      let bind_exp, ptyp =
        match pat with
        | P_aux (P_typ (ptyp, _), _) ->
            Env.wf_typ env ptyp;
            let checked_bind = crule check_exp env bind ptyp in
            (checked_bind, ptyp)
        | _ ->
            let inferred_bind = irule infer_exp env bind in
            (inferred_bind, typ_of inferred_bind)
      in
      let tpat, env = bind_pat_no_guard env pat ptyp in
      (* Propagate constraint assertions on the lhs of monadic binds to the rhs *)
      let env =
        match bind_exp with
        | E_aux (E_assert (constr_exp, _), _) -> begin
            match assert_constraint env true constr_exp with
            | Some nc ->
                typ_print (lazy ("Adding constraint " ^ string_of_n_constraint nc ^ " for assert"));
                Env.add_constraint nc env
            | None -> env
          end
        | E_aux (E_if (cond, e_t, _), _) -> begin
            match unaux_exp (fst (uncast_exp e_t)) with
            | E_throw _ | E_block [E_aux (E_throw _, _)] ->
                add_opt_constraint l "if-throw" (Option.map nc_not (assert_constraint env false cond)) env
            | _ -> env
          end
        | _ -> env
      in
      let checked_body = crule check_exp env body typ in
      annot_exp (E_internal_plet (tpat, bind_exp, checked_body)) typ
  | E_vector vec, _ ->
      let len, vtyp =
        match destruct_any_vector_typ l env typ with
        | Destruct_vector (len, vtyp) -> (len, vtyp)
        | Destruct_bitvector len -> (len, bit_typ)
      in
      let checked_items = List.map (fun i -> crule check_exp env i vtyp) vec in
      if prove __POS__ env (nc_eq (nint (List.length vec)) (nexp_simp len)) then annot_exp (E_vector checked_items) typ
      else typ_error l "Vector literal with incorrect length" (* FIXME: improve error message *)
  | E_lit (L_aux (L_undef, _) as lit), _ ->
      if is_typ_monomorphic typ || Env.polymorphic_undefineds env then
        if is_typ_inhabited env (Env.expand_synonyms env typ) || Env.polymorphic_undefineds env then
          annot_exp (E_lit lit) typ
        else typ_error l ("Type " ^ string_of_typ typ ^ " is empty")
      else typ_error l ("Type " ^ string_of_typ typ ^ " must be monomorphic")
  | E_internal_assume (nc, exp), _ ->
      Env.wf_constraint env nc;
      let env = Env.add_constraint nc env in
      let exp' = crule check_exp env exp typ in
      annot_exp (E_internal_assume (nc, exp')) typ
  | _, _ ->
      let inferred_exp = irule infer_exp env exp in
      expect_subtype env inferred_exp typ

and check_block l env exps ret_typ =
  let final env exp = match ret_typ with Some typ -> crule check_exp env exp typ | None -> irule infer_exp env exp in
  let annot_exp exp typ exp_typ = E_aux (exp, (l, mk_expected_tannot env typ exp_typ)) in
  match Nl_flow.analyze exps with
  | [] -> (
      match ret_typ with
      | Some typ ->
          typ_equality l env typ unit_typ;
          []
      | None -> []
    )
  (* We need the special case for assign even if it's the last
     expression in the block because the block provides the scope when
     it's a declaration. *)
  | E_aux (E_assign (lexp, bind), (assign_l, _)) :: exps -> begin
      match lexp_assignment_type env lexp with
      | Update ->
          let texp, env = bind_assignment assign_l env lexp bind in
          texp :: check_block l env exps ret_typ
      | Declaration ->
          if !opt_strict_var then typ_error assign_l "Variables must be declared with an explicit var expression"
          else (
            let lexp, bind, env =
              match bind_assignment l env lexp bind with
              | E_aux (E_assign (lexp, bind), _), env -> (lexp, bind, env)
              | _, _ -> assert false
            in
            let rec last_typ = function [exp] -> typ_of exp | _ :: exps -> last_typ exps | [] -> unit_typ in
            let rest = check_block l env exps ret_typ in
            let typ = last_typ rest in
            [annot_exp (E_var (lexp, bind, annot_exp (E_block rest) typ ret_typ)) typ ret_typ]
          )
    end
  | [exp] -> [final env exp]
  | E_aux (E_app (f, [E_aux (E_constraint nc, _)]), _) :: exps when string_of_id f = "_assume" ->
      Env.wf_constraint env nc;
      let env = Env.add_constraint nc env in
      let annotated_exp = annot_exp (E_app (f, [annot_exp (E_constraint nc) bool_typ None])) unit_typ None in
      annotated_exp :: check_block l env exps ret_typ
  | E_aux (E_assert (constr_exp, msg), (assert_l, _)) :: exps ->
      let msg = assert_msg msg in
      let constr_exp = crule check_exp env constr_exp bool_typ in
      let checked_msg = crule check_exp env msg string_typ in
      let env, added_constraint =
        match assert_constraint env true constr_exp with
        | Some nc ->
            typ_print (lazy (adding ^ "constraint " ^ string_of_n_constraint nc ^ " for assert"));
            (Env.add_constraint ~reason:(assert_l, "assertion") nc env, true)
        | None -> (env, false)
      in
      let texp = annot_exp (E_assert (constr_exp, checked_msg)) unit_typ (Some unit_typ) in
      let checked_exps = check_block l env exps ret_typ in
      (* If we can prove false, then any code after the assertion is
         dead. In this inconsistent typing environment we can do some
         broken things, so we eliminate this dead code here *)
      if added_constraint && List.compare_length_with exps 1 >= 0 && prove __POS__ env nc_false then (
        let ret_typ = List.rev checked_exps |> List.hd |> typ_of in
        texp :: [crule check_exp env (mk_exp ~loc:assert_l (E_exit (mk_lit_exp L_unit))) ret_typ]
      )
      else texp :: checked_exps
  | (E_aux (E_if (cond, (E_aux (E_throw _, _) | E_aux (E_block [E_aux (E_throw _, _)], _)), _), _) as exp) :: exps ->
      let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
      let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
      let env = add_opt_constraint l "if-throw" (Option.map nc_not (assert_constraint env false cond')) env in
      texp :: check_block l env exps ret_typ
  | (E_aux (E_if (cond, then_exp, _), _) as exp) :: exps when exp_unconditionally_returns then_exp ->
      let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
      let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
      let env = add_opt_constraint l "unconditional if" (Option.map nc_not (assert_constraint env false cond')) env in
      texp :: check_block l env exps ret_typ
  | exp :: exps ->
      let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
      texp :: check_block l env exps ret_typ

and check_case env pat_typ pexp typ =
  let pat, guard, case, ((l, _) as annot) = destruct_pexp pexp in
  ignore (check_pattern_duplicates env pat);
  let env = bind_pattern_vector_subranges pat env in
  match bind_pat env pat pat_typ with
  | tpat, env, guards ->
      let guard =
        match (guard, guards) with None, h :: t -> Some (h, t) | Some x, l -> Some (x, l) | None, [] -> None
      in
      let guard =
        match guard with
        | Some (h, t) -> Some (List.fold_left (fun acc guard -> mk_exp (E_app_infix (acc, mk_id "&", guard))) h t)
        | None -> None
      in
      let checked_guard, env' =
        match guard with
        | None -> (None, env)
        | Some guard ->
            let checked_guard = check_exp env guard bool_typ in
            (Some checked_guard, add_opt_constraint l "guard pattern" (assert_constraint env true checked_guard) env)
      in
      let checked_case = crule check_exp env' case typ in
      construct_pexp (tpat, checked_guard, checked_case, (l, empty_tannot))
  (* AA: Not sure if we still need this *)
  | exception (Type_error _ as typ_exn) -> (
      match pat with
      | P_aux (P_lit lit, _) ->
          let guard' = mk_exp (E_app_infix (mk_exp (E_id (mk_id "p#")), mk_id "==", mk_exp (E_lit lit))) in
          let guard =
            match guard with None -> guard' | Some guard -> mk_exp (E_app_infix (guard, mk_id "&", guard'))
          in
          check_case env pat_typ (Pat_aux (Pat_when (mk_pat (P_id (mk_id "p#")), guard, case), annot)) typ
      | _ -> raise typ_exn
    )

and check_mpexp other_env env mpexp typ =
  let mpat, guard, (l, _) = destruct_mpexp mpexp in
  match bind_mpat false other_env env mpat typ with
  | checked_mpat, env, guards ->
      let guard =
        match (guard, guards) with None, h :: t -> Some (h, t) | Some x, l -> Some (x, l) | None, [] -> None
      in
      let guard =
        match guard with
        | Some (h, t) -> Some (List.fold_left (fun acc guard -> mk_exp (E_app_infix (acc, mk_id "&", guard))) h t)
        | None -> None
      in
      let checked_guard, _ =
        match guard with
        | None -> (None, env)
        | Some guard ->
            let checked_guard = check_exp env guard bool_typ in
            (Some checked_guard, env)
      in
      construct_mpexp (checked_mpat, checked_guard, (l, empty_tannot))

(* expect_subtype env exp typ takes a fully annoted (i.e. already type
   checked) expression exp, and checks that the annotated type is a
   subtype of the provided type, updating the type annotation to
   reflect this. *)
and expect_subtype env (E_aux (_, (l, _)) as annotated_exp) typ =
  let add_expected exp =
    match exp with
    | E_aux (exp, (l, (Some tannot, uannot))) -> E_aux (exp, (l, (Some { tannot with expected = Some typ }, uannot)))
    | _ -> Reporting.unreachable l __POS__ "Cannot switch type for unannotated expression"
  in
  typ_debug (lazy ("Expect subtype: from " ^ string_of_typ (typ_of annotated_exp) ^ " to " ^ string_of_typ typ));
  subtyp l env (typ_of annotated_exp) typ;
  add_expected annotated_exp

(* can_unify_with env goals exp typ takes an annotated expression, and
   checks that its annotated type can unify with the provided type. *)
and can_unify_with env goals (E_aux (_, (l, _)) as annotated_exp) typ =
  typ_debug (lazy ("Can unify with: from " ^ string_of_typ (typ_of annotated_exp) ^ " to " ^ string_of_typ typ));
  let atyp, env = bind_existential l None (typ_of annotated_exp) env in
  let atyp, env = bind_tuple_existentials l None atyp env in
  (annotated_exp, unify l env (KidSet.diff goals (ambiguous_vars typ)) typ atyp, env)

and bind_pat_no_guard env (P_aux (_, (l, _)) as pat) typ =
  match bind_pat env pat typ with
  | _, _, _ :: _ -> typ_error l "Literal patterns not supported here"
  | tpat, env, [] -> (tpat, env)

and bind_pat env (P_aux (pat_aux, (l, uannot)) as pat) typ =
  let typ, env = bind_existential l (name_pat pat) typ env in
  typ_print (lazy (Util.("Binding " |> yellow |> clear) ^ string_of_pat pat ^ " to " ^ string_of_typ typ));
  let annot_pat_uannot uannot pat typ' = P_aux (pat, (l, mk_expected_tannot ~uannot env typ' (Some typ))) in
  let annot_pat pat typ = annot_pat_uannot uannot pat typ in
  let switch_typ pat typ =
    match pat with
    | P_aux (pat_aux, (l, (Some tannot, uannot))) -> P_aux (pat_aux, (l, (Some { tannot with typ }, uannot)))
    | _ -> typ_error l "Cannot switch type for unannotated pattern"
  in
  let bind_tuple_pat (tpats, env, guards) pat typ =
    let tpat, env, guards' = bind_pat env pat typ in
    (tpat :: tpats, env, guards' @ guards)
  in
  match pat_aux with
  | P_id v -> begin
      (* If the identifier we're matching on is also a constructor of
         a union, that's probably a mistake, so warn about it. *)
      if Env.is_union_constructor v env then
        Reporting.warn
          (Printf.sprintf "Identifier %s found in pattern is also a union constructor at" (string_of_id v))
          l
          (Printf.sprintf "Suggestion: Maybe you meant to match against %s() instead?" (string_of_id v));
      match Env.lookup_id v env with
      | Local _ | Unbound _ -> (annot_pat (P_id v) typ, Env.add_local v (Immutable, typ) env, [])
      | Register _ -> typ_error l ("Cannot shadow register in pattern " ^ string_of_pat pat)
      | Enum enum ->
          subtyp l env enum typ;
          (annot_pat (P_id v) typ, env, [])
    end
  | P_var (pat, typ_pat) ->
      let env, typ = bind_typ_pat env typ_pat typ in
      let typed_pat, env, guards = bind_pat env pat typ in
      (annot_pat (P_var (typed_pat, typ_pat)) typ, env, guards)
  | P_wild ->
      let env =
        match get_attribute "int_wildcard" uannot with
        | Some (_, arg) ->
            (* If the patterh completeness checker replaced an numeric pattern, modify the environment as if it hadn't *)
            let _, env, _ =
              bind_pat env (P_aux (P_lit (L_aux (L_num (Big_int.of_string arg), gen_loc l)), (l, uannot))) typ
            in
            env
        | None -> env
      in
      (annot_pat P_wild typ, env, [])
  | P_or (pat1, pat2) ->
      let tpat1, _, guards1 = bind_pat (Env.no_bindings env) pat1 typ in
      let tpat2, _, guards2 = bind_pat (Env.no_bindings env) pat2 typ in
      (annot_pat (P_or (tpat1, tpat2)) typ, env, guards1 @ guards2)
  | P_not pat ->
      let tpat, _, guards = bind_pat (Env.no_bindings env) pat typ in
      (annot_pat (P_not tpat) typ, env, guards)
  | P_cons (hd_pat, tl_pat) -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let hd_pat, env, hd_guards = bind_pat env hd_pat ltyp in
          let tl_pat, env, tl_guards = bind_pat env tl_pat typ in
          (annot_pat (P_cons (hd_pat, tl_pat)) typ, env, hd_guards @ tl_guards)
      | _ -> typ_error l "Cannot match cons pattern against non-list type"
    end
  | P_string_append pats -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_id id, _) when Id.compare id (mk_id "string") = 0 ->
          let rec process_pats env = function
            | [] -> ([], env, [])
            | pat :: pats ->
                let pat', env, guards = bind_pat env pat typ in
                let pats', env, guards' = process_pats env pats in
                (pat' :: pats', env, guards @ guards')
          in
          let pats, env, guards = process_pats env pats in
          (annot_pat (P_string_append pats) typ, env, guards)
      | _ -> typ_error l "Cannot match string-append pattern against non-string type"
    end
  | P_list pats -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let rec process_pats env = function
            | [] -> ([], env, [])
            | pat :: pats ->
                let pat', env, guards = bind_pat env pat ltyp in
                let pats', env, guards' = process_pats env pats in
                (pat' :: pats', env, guards @ guards')
          in
          let pats, env, guards = process_pats env pats in
          (annot_pat (P_list pats) typ, env, guards)
      | _ ->
          typ_error l ("Cannot match list pattern " ^ string_of_pat pat ^ "  against non-list type " ^ string_of_typ typ)
    end
  | P_tuple [] -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_id typ_id, _) when string_of_id typ_id = "unit" -> (annot_pat (P_tuple []) typ, env, [])
      | _ -> typ_error l "Cannot match unit pattern against non-unit type"
    end
  | P_tuple pats -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_tuple typs, _) ->
          let tpats, env, guards =
            try List.fold_left2 bind_tuple_pat ([], env, []) pats typs
            with Invalid_argument _ -> typ_error l "Tuple pattern and tuple type have different length"
          in
          (annot_pat (P_tuple (List.rev tpats)) typ, env, guards)
      | _ ->
          typ_error l
            (Printf.sprintf "Cannot bind tuple pattern %s against non tuple type %s" (string_of_pat pat)
               (string_of_typ typ)
            )
    end
  | P_app (f, [pat]) when Env.is_union_constructor f env ->
      let typq, ctor_typ = Env.get_union_id f env in
      let quants = quant_items typq in
      begin
        match Env.expand_synonyms (Env.add_typquant l typq env) ctor_typ with
        | Typ_aux (Typ_fn ([arg_typ], ret_typ), _) -> begin
            try
              let goals = quant_kopts typq |> List.map kopt_kid |> KidSet.of_list in
              typ_debug (lazy ("Unifying " ^ string_of_bind (typq, ctor_typ) ^ " for pattern " ^ string_of_typ typ));
              let unifiers = unify l env goals ret_typ typ in
              let arg_typ' = subst_unifiers unifiers arg_typ in
              let quants' = List.fold_left instantiate_quants quants (KBindings.bindings unifiers) in
              if not (List.for_all (solve_quant env) quants') then
                typ_raise l
                  (Err_unresolved_quants
                     (f, quants', Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
                  );
              let _ret_typ' = subst_unifiers unifiers ret_typ in
              let arg_typ', env = bind_existential l None arg_typ' env in
              let tpat, env, guards = bind_pat env pat arg_typ' in
              (annot_pat (P_app (f, [tpat])) typ, env, guards)
            with Unification_error (l, m) ->
              typ_error l ("Unification error when pattern matching against union constructor: " ^ m)
          end
        | _ -> typ_error l ("Mal-formed constructor " ^ string_of_id f ^ " with type " ^ string_of_typ ctor_typ)
      end
  | P_app (f, [pat]) when Env.is_mapping f env -> begin
      let typq, mapping_typ = Env.get_val_spec f env in
      let quants = quant_items typq in
      match Env.expand_synonyms env mapping_typ with
      | Typ_aux (Typ_bidir (typ1, typ2), _) -> begin
          try
            typ_debug (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for pattern " ^ string_of_typ typ));

            (* FIXME: There's no obvious goals here *)
            let unifiers = unify l env (tyvars_of_typ typ2) typ2 typ in
            let arg_typ' = subst_unifiers unifiers typ1 in
            let quants' = List.fold_left instantiate_quants quants (KBindings.bindings unifiers) in
            if not (List.for_all (solve_quant env) quants') then
              typ_raise l
                (Err_unresolved_quants
                   (f, quants', Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
                );
            let _ret_typ' = subst_unifiers unifiers typ2 in
            let tpat, env, guards = bind_pat env pat arg_typ' in
            (annot_pat_uannot (backwards_attr (gen_loc l) uannot) (P_app (f, [tpat])) typ, env, guards)
          with Unification_error (l, _) -> (
            try
              typ_debug (lazy "Unifying mapping forwards failed, trying backwards.");
              typ_debug (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for pattern " ^ string_of_typ typ));
              let unifiers = unify l env (tyvars_of_typ typ1) typ1 typ in
              let arg_typ' = subst_unifiers unifiers typ2 in
              let quants' = List.fold_left instantiate_quants quants (KBindings.bindings unifiers) in
              if not (List.for_all (solve_quant env) quants') then
                typ_raise l
                  (Err_unresolved_quants
                     (f, quants', Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
                  );
              let _ret_typ' = subst_unifiers unifiers typ1 in
              let tpat, env, guards = bind_pat env pat arg_typ' in
              (annot_pat_uannot (forwards_attr (gen_loc l) uannot) (P_app (f, [tpat])) typ, env, guards)
            with Unification_error (l, m) ->
              typ_error l ("Unification error when pattern matching against mapping constructor: " ^ m)
          )
        end
      | _ -> typ_error l ("Mal-formed mapping " ^ string_of_id f)
    end
  | P_app (f, pats) when Env.is_union_constructor f env || Env.is_mapping f env ->
      (* Treat Ctor(x, y) as Ctor((x, y)), and the same for mappings *)
      bind_pat env (P_aux (P_app (f, [mk_pat (P_tuple pats)]), (l, uannot))) typ
  | P_app (f, _) when (not (Env.is_union_constructor f env)) && not (Env.is_mapping f env) ->
      typ_error l (string_of_id f ^ " is not a union constructor or mapping in pattern " ^ string_of_pat pat)
  | P_as (pat, id) ->
      let typed_pat, env, guards = bind_pat env pat typ in
      ( annot_pat (P_as (typed_pat, id)) (typ_of_pat typed_pat),
        Env.add_local id (Immutable, typ_of_pat typed_pat) env,
        guards
      )
  (* This is a special case for flow typing when we match a constant numeric literal. *)
  | P_lit (L_aux (L_num n, _) as lit) when is_atom typ ->
      let nexp = match destruct_atom_nexp env typ with Some n -> n | None -> assert false in
      (annot_pat (P_lit lit) (atom_typ (nconstant n)), Env.add_constraint (nc_eq nexp (nconstant n)) env, [])
  | P_lit (L_aux (L_true, _) as lit) when is_atom_bool typ ->
      let nc = match destruct_atom_bool env typ with Some nc -> nc | None -> assert false in
      (annot_pat (P_lit lit) (atom_bool_typ nc_true), Env.add_constraint nc env, [])
  | P_lit (L_aux (L_false, _) as lit) when is_atom_bool typ ->
      let nc = match destruct_atom_bool env typ with Some nc -> nc | None -> assert false in
      (annot_pat (P_lit lit) (atom_bool_typ nc_false), Env.add_constraint (nc_not nc) env, [])
  | P_vector_concat (pat :: pats) -> bind_vector_concat_pat l env uannot pat pats (Some typ)
  | P_struct (fpats, fwild) ->
      let rectyp_id =
        match Env.expand_synonyms env typ with
        | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
            rectyp_id
        | _ -> typ_error l ("The type " ^ string_of_typ typ ^ " is not a record")
      in
      let record_fields = ref (Env.get_record rectyp_id env |> snd |> List.map snd |> IdSet.of_list) in
      let bind_fpat (fpats, env, guards) (field, pat) =
        record_fields := IdSet.remove field !record_fields;
        let _, rectyp_q, field_typ = Env.get_accessor rectyp_id field env in
        let unifiers =
          try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ
          with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
        in
        let field_typ' = subst_unifiers unifiers field_typ in
        let typed_pat, env, new_guards = bind_pat env pat field_typ' in
        ((field, typed_pat) :: fpats, env, guards @ new_guards)
      in
      let fpats, env, guards = List.fold_left bind_fpat ([], env, []) fpats in
      if IdSet.is_empty !record_fields then (annot_pat (P_struct (List.rev fpats, FP_no_wild)) typ, env, guards)
      else (
        (* If we have a field wildcard .. then insert the missing `field = _` here *)
        match fwild with
        | FP_wild fwild_loc ->
            let missing_fields =
              List.map (fun id -> (id, mk_pat ~loc:fwild_loc P_wild)) (IdSet.elements !record_fields)
            in
            let missing_fpats, env, guards = List.fold_left bind_fpat ([], env, []) missing_fields in
            (annot_pat (P_struct (List.rev fpats @ missing_fpats, FP_no_wild)) typ, env, guards)
        | FP_no_wild ->
            typ_error l
              ("struct pattern missing fields: " ^ string_of_list ", " string_of_id (IdSet.elements !record_fields))
      )
  | _ -> (
      let inferred_pat, env, guards = infer_pat env pat in
      match subtyp l env typ (typ_of_pat inferred_pat) with
      | () -> (switch_typ inferred_pat (typ_of_pat inferred_pat), env, guards)
      | exception (Type_error _ as typ_exn) -> (
          match pat_aux with
          | P_lit lit ->
              let var = fresh_var () in
              let guard =
                locate (fun _ -> l) (mk_exp (E_app_infix (mk_exp (E_id var), mk_id "==", mk_exp (E_lit lit))))
              in
              let typed_pat, env, guards = bind_pat env (mk_pat (P_id var)) typ in
              (typed_pat, env, guard :: guards)
          | _ -> raise typ_exn
        )
    )

and infer_pat env (P_aux (pat_aux, (l, uannot)) as pat) =
  let annot_pat pat typ = P_aux (pat, (l, mk_tannot ~uannot env typ)) in
  match pat_aux with
  | P_id v -> begin
      match Env.lookup_id v env with
      | Local (Immutable, _) | Unbound _ ->
          typ_error l ("Cannot infer identifier in pattern " ^ string_of_pat pat ^ " - try adding a type annotation")
      | Local (Mutable, _) | Register _ ->
          typ_error l ("Cannot shadow mutable local or register in switch statement pattern " ^ string_of_pat pat)
      | Enum enum -> (annot_pat (P_id v) enum, env, [])
    end
  | P_app (f, _) when Env.is_union_constructor f env -> begin
      let _, ctor_typ = Env.get_val_spec f env in
      match Env.expand_synonyms env ctor_typ with
      | Typ_aux (Typ_fn (_, ret_typ), _) -> bind_pat env pat ret_typ
      | _ -> typ_error l ("Mal-formed constructor " ^ string_of_id f)
    end
  | P_app (f, _) when Env.is_mapping f env -> begin
      let _, mapping_typ = Env.get_val_spec f env in
      match Env.expand_synonyms env mapping_typ with
      | Typ_aux (Typ_bidir (typ1, typ2), _) -> begin
          try bind_pat env pat typ2 with Type_error _ -> bind_pat env pat typ1
        end
      | _ -> typ_error l ("Malformed mapping type " ^ string_of_id f)
    end
  | P_typ (typ_annot, pat) ->
      Env.wf_typ env typ_annot;
      let typed_pat, env, guards = bind_pat env pat typ_annot in
      (annot_pat (P_typ (typ_annot, typed_pat)) typ_annot, env, guards)
  | P_lit lit -> (annot_pat (P_lit lit) (infer_lit env lit), env, [])
  | P_vector (pat :: pats) ->
      let fold_pats (pats, env, guards) pat =
        let typed_pat, env, guards' = bind_pat env pat bit_typ in
        (pats @ [typed_pat], env, guards' @ guards)
      in
      let pats, env, guards = List.fold_left fold_pats ([], env, []) (pat :: pats) in
      let len = nexp_simp (nint (List.length pats)) in
      let etyp = typ_of_pat (List.hd pats) in
      (* BVS TODO: Non-bitvector P_vector *)
      List.iter (fun pat -> typ_equality l env etyp (typ_of_pat pat)) pats;
      (annot_pat (P_vector pats) (bits_typ env len), env, guards)
  | P_vector_concat (pat :: pats) -> bind_vector_concat_pat l env uannot pat pats None
  | P_vector_subrange (id, n, m) ->
      let typ = bitvector_typ_from_range l env n m in
      (annot_pat (P_vector_subrange (id, n, m)) typ, env, [])
  | P_string_append pats ->
      let fold_pats (pats, env, guards) pat =
        let inferred_pat, env, guards' = infer_pat env pat in
        typ_equality l env (typ_of_pat inferred_pat) string_typ;
        (pats @ [inferred_pat], env, guards' @ guards)
      in
      let typed_pats, env, guards = List.fold_left fold_pats ([], env, []) pats in
      (annot_pat (P_string_append typed_pats) string_typ, env, guards)
  | P_as (pat, id) ->
      let typed_pat, env, guards = infer_pat env pat in
      ( annot_pat (P_as (typed_pat, id)) (typ_of_pat typed_pat),
        Env.add_local id (Immutable, typ_of_pat typed_pat) env,
        guards
      )
  | _ -> typ_error l ("Couldn't infer type of pattern " ^ string_of_pat pat)

and bind_vector_concat_generic :
      'a 'b.
      ('a, 'b) pattern_functions ->
      ('b list -> typ -> 'b) ->
      l ->
      bool ->
      Env.t ->
      'a ->
      'a list ->
      typ option ->
      'b * Env.t * uannot exp list =
 fun funcs annotate l allow_unknown env pat pats typ_opt ->
  (* Try to infer a constant length, and the element type if non-bitvector *)
  let typ_opt =
    Option.bind typ_opt (fun typ ->
        match destruct_any_vector_typ l env typ with
        | Destruct_vector (len, elem_typ) -> Option.map (fun l -> (l, Some elem_typ)) (solve_unique env len)
        | Destruct_bitvector len -> Option.map (fun l -> (l, None)) (solve_unique env len)
    )
  in

  (* Try to infer any subpatterns, skipping those we cannot infer *)
  let fold_pats (pats, env, guards) pat =
    let wrap_some (x, y, z) = (Ok x, y, z) in
    let inferred_pat, env, guards' =
      if Option.is_none typ_opt then wrap_some (funcs.infer env pat)
      else (try wrap_some (funcs.infer env pat) with Type_error _ as exn -> (Error (pat, exn), env, []))
    in
    (inferred_pat :: pats, env, guards' @ guards)
  in
  let inferred_pats, env, guards = List.fold_left fold_pats ([], env, []) (pat :: pats) in
  let inferred_pats = List.rev inferred_pats in

  (* If we are checking a mapping we can have unknown types, in this
     case we can't continue, so just give the entire vector concat an
     unknown type. *)
  let have_unknown =
    allow_unknown
    && List.exists (function Ok pat -> is_unknown_type (funcs.typ_of pat) | Error _ -> false) inferred_pats
  in
  if have_unknown && List.for_all Result.is_ok inferred_pats then
    (annotate (List.map Result.get_ok inferred_pats) unknown_typ, env, guards)
  else (
    (* Will be none if the subpatterns are bitvectors *)
    let elem_typ =
      match typ_opt with
      | Some (_, elem_typ) -> elem_typ
      | None -> (
          match List.find_opt Result.is_ok inferred_pats with
          | Some (Ok pat) -> begin
              match destruct_any_vector_typ l env (funcs.typ_of pat) with
              | Destruct_vector (_, t) -> Some t
              | Destruct_bitvector _ -> None
            end
          | _ -> typ_error l "Could not infer type of subpatterns in vector concatenation pattern"
        )
    in

    (* We can handle a single None in inferred_pats from something like
       0b00 @ _ @ 0b00, because we know the wildcard will be bits('n - 4)
       where 'n is the total length of the pattern. *)
    let before_uninferred, rest = Util.take_drop Result.is_ok inferred_pats in
    let before_uninferred = List.map Result.get_ok before_uninferred in
    let uninferred, after_uninferred =
      match rest with
      | Error (first_uninferred, exn) :: rest ->
          begin
            match List.find_opt Result.is_error rest with
            | Some (Error (second_uninferred, _)) ->
                let msg =
                  "Cannot infer width here, as there are multiple subpatterns with unclear width in vector \
                   concatenation pattern"
                in
                typ_raise (funcs.get_loc second_uninferred)
                  (err_because
                     (Err_other msg, funcs.get_loc first_uninferred, Err_other "A previous subpattern is here")
                  )
            | _ -> ()
          end;
          begin
            match typ_opt with
            | Some (total_len, _) -> (Some (total_len, first_uninferred), List.map Result.get_ok rest)
            | None -> raise exn
          end
      | _ -> (None, [])
    in

    let check_constant_len l n =
      match solve_unique env n with
      | Some c -> nconstant c
      | None -> typ_error l "Could not infer constant length for vector concatenation subpattern"
    in

    (* Now we have two similar cases for ordinary vectors and bitvectors *)
    match elem_typ with
    | Some elem_typ ->
        let fold_len len pat =
          let l = funcs.get_loc_typed pat in
          let len', elem_typ' = destruct_vector_typ l env (funcs.typ_of pat) in
          let len' = check_constant_len l len' in
          typ_equality l env elem_typ elem_typ';
          nsum len len'
        in
        let before_len = List.fold_left fold_len (nint 0) before_uninferred in
        let after_len = List.fold_left fold_len (nint 0) after_uninferred in
        let inferred_len = nexp_simp (nsum before_len after_len) in
        begin
          match uninferred with
          | Some (total_len, uninferred_pat) ->
              let total_len = nconstant total_len in
              let uninferred_len = nexp_simp (nminus total_len inferred_len) in
              let checked_pat, env, guards' = funcs.bind env uninferred_pat (vector_typ uninferred_len elem_typ) in
              ( annotate (before_uninferred @ [checked_pat] @ after_uninferred) (vector_typ total_len elem_typ),
                env,
                guards' @ guards
              )
          | None -> (annotate before_uninferred (dvector_typ env inferred_len elem_typ), env, guards)
        end
    | None ->
        let fold_len len pat =
          let l = funcs.get_loc_typed pat in
          let len' = destruct_bitvector_typ l env (funcs.typ_of pat) in
          let len' = check_constant_len l len' in
          nsum len len'
        in
        let before_len = List.fold_left fold_len (nint 0) before_uninferred in
        let after_len = List.fold_left fold_len (nint 0) after_uninferred in
        let inferred_len = nexp_simp (nsum before_len after_len) in
        begin
          match uninferred with
          | Some (total_len, uninferred_pat) ->
              let total_len = nconstant total_len in
              let uninferred_len = nexp_simp (nminus total_len inferred_len) in
              let checked_pat, env, guards' = funcs.bind env uninferred_pat (bitvector_typ uninferred_len) in
              ( annotate (before_uninferred @ [checked_pat] @ after_uninferred) (bitvector_typ total_len),
                env,
                guards' @ guards
              )
          | None -> (annotate before_uninferred (bits_typ env inferred_len), env, guards)
        end
  )

and bind_vector_concat_pat l env uannot pat pats typ_opt =
  let annot_vcp pats typ = P_aux (P_vector_concat pats, (l, mk_tannot ~uannot env typ)) in
  let funcs = { infer = infer_pat; bind = bind_pat; typ_of = typ_of_pat; get_loc = pat_loc; get_loc_typed = pat_loc } in
  bind_vector_concat_generic funcs annot_vcp l false env pat pats typ_opt

and bind_vector_concat_mpat l allow_unknown other_env env uannot mpat mpats typ_opt =
  let annot_vcmp mpats typ = MP_aux (MP_vector_concat mpats, (l, mk_tannot ~uannot env typ)) in
  let funcs =
    {
      infer = infer_mpat allow_unknown other_env;
      bind = bind_mpat allow_unknown other_env;
      typ_of = typ_of_mpat;
      get_loc = mpat_loc;
      get_loc_typed = mpat_loc;
    }
  in
  bind_vector_concat_generic funcs annot_vcmp l allow_unknown env mpat mpats typ_opt

and bind_typ_pat env (TP_aux (typ_pat_aux, l) as typ_pat) (Typ_aux (typ_aux, _) as typ) =
  typ_print
    (lazy (Util.("Binding type pattern " |> yellow |> clear) ^ string_of_typ_pat typ_pat ^ " to " ^ string_of_typ typ));
  match (typ_pat_aux, typ_aux) with
  | TP_wild, _ -> (env, typ)
  | TP_var kid, _ -> begin
      match (typ_nexps typ, typ_constraints typ) with
      | [nexp], [] ->
          let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_int kid) env in
          let nexp = match shadow with Some s_v -> nexp_subst kid (arg_nexp (nvar s_v)) nexp | None -> nexp in
          ( Env.add_constraint ~reason:(l, "type pattern") (nc_eq (nvar kid) nexp) env,
            replace_nexp_typ nexp (Nexp_aux (Nexp_var kid, l)) typ
          )
      | [], [nc] ->
          let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_bool kid) env in
          let nc = match shadow with Some s_v -> constraint_subst kid (arg_bool (nc_var s_v)) nc | None -> nc in
          ( Env.add_constraint ~reason:(l, "type pattern")
              (nc_and (nc_or (nc_not nc) (nc_var kid)) (nc_or nc (nc_not (nc_var kid))))
              env,
            replace_nc_typ nc (NC_aux (NC_var kid, l)) typ
          )
      | [], [] ->
          typ_error l ("No numeric expressions in " ^ string_of_typ typ ^ " to bind " ^ string_of_kid kid ^ " to")
      | _, _ ->
          typ_error l
            ("Type " ^ string_of_typ typ ^ " has multiple numeric or boolean expressions. Cannot bind "
           ^ string_of_kid kid
            )
    end
  | TP_app (f1, tpats), Typ_app (f2, typs) when Id.compare f1 f2 = 0 && List.compare_lengths tpats typs = 0 ->
      let env, args =
        List.fold_right2
          (fun tp arg (env, args) ->
            let env, arg = bind_typ_pat_arg env tp arg in
            (env, arg :: args)
          )
          tpats typs (env, [])
      in
      (env, Typ_aux (Typ_app (f2, args), l))
  | _, _ -> typ_error l ("Couldn't bind type " ^ string_of_typ typ ^ " with " ^ string_of_typ_pat typ_pat)

and bind_typ_pat_arg env (TP_aux (typ_pat_aux, l) as typ_pat) (A_aux (typ_arg_aux, l_arg) as typ_arg) =
  match (typ_pat_aux, typ_arg_aux) with
  | TP_wild, _ -> (env, typ_arg)
  | TP_var kid, A_nexp nexp ->
      let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_int kid) env in
      let nexp = match shadow with Some s_v -> nexp_subst kid (arg_nexp (nvar s_v)) nexp | None -> nexp in
      (Env.add_constraint ~reason:(l, "type pattern") (nc_eq (nvar kid) nexp) env, arg_nexp ~loc:l (nvar kid))
  | TP_var kid, A_bool nc ->
      let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_bool kid) env in
      let nc = match shadow with Some s_v -> constraint_subst kid (arg_bool (nc_var s_v)) nc | None -> nc in
      let bound = nc_or (nc_and (nc_var kid) nc) (nc_and (nc_not (nc_var kid)) (nc_not nc)) in
      (Env.add_constraint ~reason:(l, "type pattern") bound env, arg_bool ~loc:l (nc_var kid))
  | _, A_typ typ ->
      let env, typ' = bind_typ_pat env typ_pat typ in
      (env, A_aux (A_typ typ', l_arg))
  | _, _ ->
      typ_error l ("Couldn't bind type argument " ^ string_of_typ_arg typ_arg ^ " with " ^ string_of_typ_pat typ_pat)

and bind_assignment assign_l env (LE_aux (lexp_aux, (lexp_l, uannot)) as lexp) exp =
  let annot_assign lexp exp =
    E_aux (E_assign (lexp, exp), (assign_l, mk_tannot env (mk_typ (Typ_id (mk_id "unit")))))
  in
  let has_typ v env = match Env.lookup_id v env with Local (Mutable, _) | Register _ -> true | _ -> false in
  match lexp_aux with
  | LE_app (f, xs) -> (check_exp env (E_aux (E_app (f, xs @ [exp]), (lexp_l, uannot))) unit_typ, env)
  | LE_typ (typ_annot, _) ->
      let checked_exp = crule check_exp env exp typ_annot in
      let tlexp, env' = bind_lexp env lexp (typ_of checked_exp) in
      (annot_assign tlexp checked_exp, env')
  | LE_id v when has_typ v env -> begin
      match Env.lookup_id v env with
      | Local (Mutable, vtyp) | Register vtyp ->
          let checked_exp = crule check_exp env exp vtyp in
          let tlexp, env' = bind_lexp env lexp (typ_of checked_exp) in
          (annot_assign tlexp checked_exp, env')
      | _ -> assert false
    end
  | _ -> (
      (* Here we have two options, we can infer the type from the
         expression, or we can infer the type from the
         l-expression. Both are useful in different cases, so try
         both. *)
      try
        let inferred_exp = irule infer_exp env exp in
        let tlexp, env' = bind_lexp env lexp (typ_of inferred_exp) in
        (annot_assign tlexp inferred_exp, env')
      with Type_error (l, err) -> (
        try
          let inferred_lexp = infer_lexp env lexp in
          let checked_exp = crule check_exp env exp (lexp_typ_of inferred_lexp) in
          (annot_assign inferred_lexp checked_exp, env)
        with Type_error (l', err') -> typ_raise l' (err_because (err', l, err))
      )
    )

and bind_lexp env (LE_aux (lexp_aux, (l, _)) as lexp) typ =
  typ_print (lazy ("Binding mutable " ^ string_of_lexp lexp ^ " to " ^ string_of_typ typ));
  let annot_lexp lexp typ = LE_aux (lexp, (l, mk_tannot env typ)) in
  match lexp_aux with
  | LE_typ (typ_annot, v) -> begin
      match Env.lookup_id v env with
      | Local (Immutable, _) | Enum _ ->
          typ_error l ("Cannot modify immutable let-bound constant or enumeration constructor " ^ string_of_id v)
      | Local (Mutable, vtyp) ->
          subtyp l env typ typ_annot;
          subtyp l env typ_annot vtyp;
          (annot_lexp (LE_typ (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env)
      | Register vtyp ->
          subtyp l env typ typ_annot;
          subtyp l env typ_annot vtyp;
          (annot_lexp (LE_typ (typ_annot, v)) typ, env)
      | Unbound _ ->
          subtyp l env typ typ_annot;
          (annot_lexp (LE_typ (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env)
    end
  | LE_id v -> begin
      match Env.lookup_id v env with
      | Local (Immutable, _) | Enum _ ->
          typ_error l ("Cannot modify immutable let-bound constant or enumeration constructor " ^ string_of_id v)
      | Local (Mutable, vtyp) ->
          subtyp l env typ vtyp;
          (annot_lexp (LE_id v) typ, env)
      | Register vtyp ->
          subtyp l env typ vtyp;
          (annot_lexp (LE_id v) typ, env)
      | Unbound _ -> (annot_lexp (LE_id v) typ, Env.add_local v (Mutable, typ) env)
    end
  | LE_tuple lexps -> begin
      let typ = Env.expand_synonyms env typ in
      let (Typ_aux (typ_aux, _)) = typ in
      match typ_aux with
      | Typ_tuple typs ->
          let bind_tuple_lexp lexp typ (tlexps, env) =
            let tlexp, env = bind_lexp env lexp typ in
            (tlexp :: tlexps, env)
          in
          let tlexps, env =
            try List.fold_right2 bind_tuple_lexp lexps typs ([], env)
            with Invalid_argument _ -> typ_error l "Tuple l-expression and tuple type have different length"
          in
          (annot_lexp (LE_tuple tlexps) typ, env)
      | _ -> typ_error l ("Cannot bind tuple l-expression against non tuple type " ^ string_of_typ typ)
    end
  | _ ->
      let inferred_lexp = infer_lexp env lexp in
      subtyp l env typ (lexp_typ_of inferred_lexp);
      (inferred_lexp, env)

and infer_lexp env (LE_aux (lexp_aux, (l, uannot)) as lexp) =
  let annot_lexp lexp typ = LE_aux (lexp, (l, mk_tannot ~uannot env typ)) in
  match lexp_aux with
  | LE_id v -> begin
      match Env.lookup_id v env with
      | Local (Mutable, typ) -> annot_lexp (LE_id v) typ
      | Register typ -> annot_lexp (LE_id v) typ
      | Local (Immutable, _) | Enum _ ->
          typ_error l ("Cannot modify let-bound constant or enumeration constructor " ^ string_of_id v)
      | Unbound _ -> typ_error l ("Cannot create a new identifier in this l-expression " ^ string_of_lexp lexp)
    end
  | LE_vector_range (v_lexp, exp1, exp2) -> begin
      let inferred_v_lexp = infer_lexp env v_lexp in
      let (Typ_aux (v_typ_aux, _)) = Env.expand_synonyms env (lexp_typ_of inferred_v_lexp) in
      match v_typ_aux with
      | Typ_app (id, [A_aux (A_nexp len, _)]) when Id.compare id (mk_id "bitvector") = 0 ->
          let inferred_exp1 = infer_exp env exp1 in
          let inferred_exp2 = infer_exp env exp2 in
          let nexp1, env = bind_numeric l (typ_of inferred_exp1) env in
          let nexp2, env = bind_numeric l (typ_of inferred_exp2) env in
          let slice_len, check =
            match Env.get_default_order env with
            | Ord_aux (Ord_inc, _) ->
                ( nexp_simp (nsum (nminus nexp2 nexp1) (nint 1)),
                  nc_and (nc_and (nc_lteq (nint 0) nexp1) (nc_lteq nexp1 nexp2)) (nc_lt nexp2 len)
                )
            | Ord_aux (Ord_dec, _) ->
                ( nexp_simp (nsum (nminus nexp1 nexp2) (nint 1)),
                  nc_and (nc_and (nc_lteq (nint 0) nexp2) (nc_lteq nexp2 nexp1)) (nc_lt nexp1 len)
                )
          in
          if !opt_no_lexp_bounds_check || prove __POS__ env check then
            annot_lexp (LE_vector_range (inferred_v_lexp, inferred_exp1, inferred_exp2)) (bitvector_typ slice_len)
          else
            typ_raise l
              (Err_failed_constraint (check, Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env))
      | _ -> typ_error l "Cannot assign slice of non vector type"
    end
  | LE_vector (v_lexp, exp) -> begin
      let inferred_v_lexp = infer_lexp env v_lexp in
      let (Typ_aux (v_typ_aux, _)) = Env.expand_synonyms env (lexp_typ_of inferred_v_lexp) in
      match v_typ_aux with
      | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_typ elem_typ, _)]) when Id.compare id (mk_id "vector") = 0 ->
          let inferred_exp = infer_exp env exp in
          let nexp, env = bind_numeric l (typ_of inferred_exp) env in
          let bounds_check = nc_and (nc_lteq (nint 0) nexp) (nc_lt nexp len) in
          if !opt_no_lexp_bounds_check || prove __POS__ env bounds_check then
            annot_lexp (LE_vector (inferred_v_lexp, inferred_exp)) elem_typ
          else
            typ_raise l
              (Err_failed_constraint
                 (bounds_check, Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
              )
      | Typ_app (id, [A_aux (A_nexp len, _)]) when Id.compare id (mk_id "bitvector") = 0 ->
          let inferred_exp = infer_exp env exp in
          let nexp, env = bind_numeric l (typ_of inferred_exp) env in
          let bounds_check = nc_and (nc_lteq (nint 0) nexp) (nc_lt nexp len) in
          if !opt_no_lexp_bounds_check || prove __POS__ env bounds_check then
            annot_lexp (LE_vector (inferred_v_lexp, inferred_exp)) bit_typ
          else
            typ_raise l
              (Err_failed_constraint
                 (bounds_check, Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
              )
      | Typ_id id -> begin
          match exp with
          | E_aux (E_id field, _) ->
              let field_lexp = Bitfield.set_bits_field_lexp v_lexp in
              let index_range =
                match get_bitfield_range id field env with
                | Some range -> range
                | None ->
                    typ_error l (Printf.sprintf "Unknown field %s in bitfield %s" (string_of_id field) (string_of_id id))
              in
              infer_lexp env (Bitfield.set_field_lexp index_range field_lexp)
          | _ -> typ_error l (string_of_exp exp ^ " is not a bitfield accessor")
        end
      | _ -> typ_error l "Cannot assign vector element of non vector or bitfield type"
    end
  | LE_vector_concat [] -> typ_error l "Cannot have empty vector concatenation l-expression"
  | LE_vector_concat (v_lexp :: v_lexps) -> begin
      let sum_vector_lengths first_elem_typ acc (Typ_aux (v_typ_aux, _)) =
        match v_typ_aux with
        | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_typ elem_typ, _)]) when Id.compare id (mk_id "vector") = 0 ->
            typ_equality l env elem_typ first_elem_typ;
            nsum acc len
        | _ -> typ_error l "Vector concatentation l-expression must only contain vector types of the same order"
      in
      let sum_bitvector_lengths acc (Typ_aux (v_typ_aux, _)) =
        match v_typ_aux with
        | Typ_app (id, [A_aux (A_nexp len, _)]) when Id.compare id (mk_id "bitvector") = 0 -> nsum acc len
        | _ -> typ_error l "Bitvector concatentation l-expression must only contain bitvector types of the same order"
      in
      let inferred_v_lexp = infer_lexp env v_lexp in
      let inferred_v_lexps = List.map (infer_lexp env) v_lexps in
      let (Typ_aux (v_typ_aux, _) as v_typ) = Env.expand_synonyms env (lexp_typ_of inferred_v_lexp) in
      let v_typs = List.map (fun lexp -> Env.expand_synonyms env (lexp_typ_of lexp)) inferred_v_lexps in
      match v_typ_aux with
      | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_typ elem_typ, _)]) when Id.compare id (mk_id "vector") = 0 ->
          let len = List.fold_left (sum_vector_lengths elem_typ) len v_typs in
          annot_lexp (LE_vector_concat (inferred_v_lexp :: inferred_v_lexps)) (vector_typ (nexp_simp len) elem_typ)
      | Typ_app (id, [A_aux (A_nexp len, _)]) when Id.compare id (mk_id "bitvector") = 0 ->
          let len = List.fold_left sum_bitvector_lengths len v_typs in
          annot_lexp (LE_vector_concat (inferred_v_lexp :: inferred_v_lexps)) (bitvector_typ (nexp_simp len))
      | _ ->
          typ_error l
            ("Vector concatentation l-expression must only contain bitvector or vector types, found "
           ^ string_of_typ v_typ
            )
    end
  | LE_field ((LE_aux (_, (l, _)) as lexp), field_id) ->
      let inferred_lexp = infer_lexp env lexp in
      let rectyp = lexp_typ_of inferred_lexp in
      begin
        match lexp_typ_of inferred_lexp with
        | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
            let _, rectyp_q, field_typ = Env.get_accessor rectyp_id field_id env in
            let unifiers =
              try unify l env (tyvars_of_typ rectyp_q) rectyp_q rectyp
              with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
            in
            let field_typ' = subst_unifiers unifiers field_typ in
            annot_lexp (LE_field (inferred_lexp, field_id)) field_typ'
        | _ -> typ_error l "Field l-expression has invalid type"
      end
  | LE_deref exp ->
      let inferred_exp = infer_exp env exp in
      begin
        match typ_of inferred_exp with
        | Typ_aux (Typ_app (r, [A_aux (A_typ vtyp, _)]), _) when string_of_id r = "register" ->
            annot_lexp (LE_deref inferred_exp) vtyp
        | _ ->
            typ_error l (string_of_typ (typ_of inferred_exp) ^ " must be a register type in " ^ string_of_exp exp ^ ")")
      end
  | LE_tuple lexps ->
      let inferred_lexps = List.map (infer_lexp env) lexps in
      annot_lexp (LE_tuple inferred_lexps) (tuple_typ (List.map lexp_typ_of inferred_lexps))
  | _ -> typ_error l ("Could not infer the type of " ^ string_of_lexp lexp)

and infer_exp env (E_aux (exp_aux, (l, uannot)) as exp) =
  let annot_exp exp typ = E_aux (exp, (l, mk_tannot ~uannot env typ)) in
  match exp_aux with
  | E_block exps ->
      let rec last_typ = function [exp] -> typ_of exp | _ :: exps -> last_typ exps | [] -> unit_typ in
      let inferred_block = check_block l env exps None in
      annot_exp (E_block inferred_block) (last_typ inferred_block)
  | E_id v -> begin
      match Env.lookup_id v env with
      | Local (_, typ) | Enum typ -> annot_exp (E_id v) typ
      | Register typ -> annot_exp (E_id v) typ
      | Unbound _ -> (
          match Bindings.find_opt v (Env.get_val_specs env) with
          | Some _ ->
              typ_error l
                ("Identifier " ^ string_of_id v ^ " is unbound (Did you mean to call the " ^ string_of_id v
               ^ " function?)"
                )
          | None -> typ_error l ("Identifier " ^ string_of_id v ^ " is unbound")
        )
    end
  | E_lit lit -> annot_exp (E_lit lit) (infer_lit env lit)
  | E_sizeof nexp -> irule infer_exp env (rewrite_sizeof l env (Env.expand_nexp_synonyms env nexp))
  | E_constraint nc ->
      Env.wf_constraint env nc;
      crule check_exp env (rewrite_nc env (Env.expand_constraint_synonyms env nc)) (atom_bool_typ nc)
  | E_field (exp, field) -> begin
      let inferred_exp = irule infer_exp env exp in
      match Env.expand_synonyms env (typ_of inferred_exp) with
      (* Accessing a field of a record *)
      | Typ_aux (Typ_id rectyp, _) when Env.is_record rectyp env -> begin
          let inferred_acc =
            infer_funapp' l env field (Env.get_accessor_fn rectyp field env) [strip_exp inferred_exp] None
          in
          match inferred_acc with
          | E_aux (E_app (field, [inferred_exp]), _) -> annot_exp (E_field (inferred_exp, field)) (typ_of inferred_acc)
          | _ -> assert false (* Unreachable *)
        end
      (* Not sure if we need to do anything different with args here. *)
      | Typ_aux (Typ_app (rectyp, _), _) when Env.is_record rectyp env -> begin
          let inferred_acc =
            infer_funapp' l env field (Env.get_accessor_fn rectyp field env) [strip_exp inferred_exp] None
          in
          match inferred_acc with
          | E_aux (E_app (field, [inferred_exp]), _) -> annot_exp (E_field (inferred_exp, field)) (typ_of inferred_acc)
          | _ -> assert false (* Unreachable *)
        end
      | _ ->
          typ_error l
            ("Field expression " ^ string_of_exp exp ^ " :: " ^ string_of_typ (typ_of inferred_exp) ^ " is not valid")
    end
  | E_tuple exps ->
      let inferred_exps = List.map (irule infer_exp env) exps in
      annot_exp (E_tuple inferred_exps) (mk_typ (Typ_tuple (List.map typ_of inferred_exps)))
  | E_assign (lexp, bind) -> begin
      match lexp_assignment_type env lexp with
      | Update -> fst (bind_assignment l env lexp bind)
      | Declaration ->
          typ_error l
            "Variable declaration with unclear (or no) scope. Use an explicit var statement instead, or place in a \
             block"
    end
  | E_struct_update (exp, fexps) ->
      let inferred_exp = irule infer_exp env exp in
      let typ = typ_of inferred_exp in
      let rectyp_id =
        match Env.expand_synonyms env typ with
        | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
            rectyp_id
        | _ -> typ_error l ("The type " ^ string_of_typ typ ^ " is not a record")
      in
      let check_fexp (FE_aux (FE_fexp (field, exp), (l, _))) =
        let _, rectyp_q, field_typ = Env.get_accessor rectyp_id field env in
        let unifiers =
          try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ
          with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
        in
        let field_typ' = subst_unifiers unifiers field_typ in
        let inferred_exp = crule check_exp env exp field_typ' in
        FE_aux (FE_fexp (field, inferred_exp), (l, empty_tannot))
      in
      annot_exp (E_struct_update (inferred_exp, List.map check_fexp fexps)) typ
  | E_typ (typ, exp) ->
      let checked_exp = crule check_exp env exp typ in
      annot_exp (E_typ (typ, checked_exp)) typ
  | E_app_infix (x, op, y) -> infer_exp env (E_aux (E_app (deinfix op, [x; y]), (l, uannot)))
  (* Treat a multiple argument constructor as a single argument constructor taking a tuple, Ctor(x, y) -> Ctor((x, y)). *)
  | E_app (ctor, x :: y :: zs) when Env.is_union_constructor ctor env ->
      typ_print (lazy ("Inferring multiple argument constructor: " ^ string_of_id ctor));
      irule infer_exp env (mk_exp ~loc:l (E_app (ctor, [mk_exp ~loc:l (E_tuple (x :: y :: zs))])))
  | E_app (mapping, xs) when Env.is_mapping mapping env ->
      let forwards_id = mk_id (string_of_id mapping ^ "_forwards") in
      let backwards_id = mk_id (string_of_id mapping ^ "_backwards") in
      typ_print
        ( lazy
          ("Trying forwards direction for mapping " ^ string_of_id mapping ^ "(" ^ string_of_list ", " string_of_exp xs
         ^ ")"
          )
          );
      begin
        try irule infer_exp env (E_aux (E_app (forwards_id, xs), (l, uannot)))
        with Type_error (_, err1) ->
          (* typ_print (lazy ("Error in forwards direction: " ^ string_of_type_error err1)); *)
          typ_print
            ( lazy
              ("Trying backwards direction for mapping " ^ string_of_id mapping ^ "("
             ^ string_of_list ", " string_of_exp xs ^ ")"
              )
              );
          begin
            try irule infer_exp env (E_aux (E_app (backwards_id, xs), (l, uannot)))
            with Type_error (_, err2) ->
              (* typ_print (lazy ("Error in backwards direction: " ^ string_of_type_error err2)); *)
              typ_raise l (Err_no_overloading (mapping, [(forwards_id, err1); (backwards_id, err2)]))
          end
      end
  | E_app (f, xs) when List.length (Env.get_overloads f env) > 0 ->
      let rec try_overload = function
        | errs, [] -> typ_raise l (Err_no_overloading (f, errs))
        | errs, f :: fs -> begin
            typ_print (lazy ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
            try irule infer_exp env (E_aux (E_app (f, xs), (l, uannot)))
            with Type_error (_, err) ->
              typ_debug (lazy "Error");
              try_overload (errs @ [(f, err)], fs)
          end
      in
      try_overload ([], Env.get_overloads f env)
  | E_app (f, [x; y]) when string_of_id f = "and_bool" || string_of_id f = "or_bool" -> begin
      match destruct_exist (typ_of (irule infer_exp env y)) with
      | None | Some (_, NC_aux (NC_true, _), _) -> infer_funapp l env f [x; y] None
      | Some _ -> infer_funapp l env f [x; mk_exp (E_typ (bool_typ, y))] None
      | exception Type_error _ -> infer_funapp l env f [x; mk_exp (E_typ (bool_typ, y))] None
    end
  | E_app (f, xs) -> infer_funapp l env f xs None
  | E_loop (loop_type, measure, cond, body) ->
      let checked_cond = crule check_exp env cond bool_typ in
      let checked_measure =
        match measure with
        | Measure_aux (Measure_none, l) -> Measure_aux (Measure_none, l)
        | Measure_aux (Measure_some exp, l) -> Measure_aux (Measure_some (crule check_exp env exp int_typ), l)
      in
      let nc = match loop_type with While -> assert_constraint env true checked_cond | Until -> None in
      let checked_body = crule check_exp (add_opt_constraint l "loop condition" nc env) body unit_typ in
      annot_exp (E_loop (loop_type, checked_measure, checked_cond, checked_body)) unit_typ
  | E_for (v, f, t, step, ord, body) -> begin
      let f, t, is_dec =
        match ord with
        | Ord_aux (Ord_inc, _) -> (f, t, false)
        | Ord_aux (Ord_dec, _) -> (t, f, true (* reverse direction to typechecking downto as upto loop *))
      in
      let inferred_f = irule infer_exp env f in
      let inferred_t = irule infer_exp env t in
      let checked_step = crule check_exp env step int_typ in
      match (destruct_numeric (typ_of inferred_f), destruct_numeric (typ_of inferred_t)) with
      | Some (kids1, nc1, nexp1), Some (kids2, nc2, nexp2) ->
          let loop_kid = mk_kid ("loop_" ^ string_of_id v) in
          let env =
            List.fold_left (fun env kid -> Env.add_typ_var l (mk_kopt K_int kid) env) env ((loop_kid :: kids1) @ kids2)
          in
          let env = Env.add_constraint (nc_and nc1 nc2) env in
          let env = Env.add_constraint (nc_and (nc_lteq nexp1 (nvar loop_kid)) (nc_lteq (nvar loop_kid) nexp2)) env in
          let loop_vtyp = atom_typ (nvar loop_kid) in
          let checked_body = crule check_exp (Env.add_local v (Immutable, loop_vtyp) env) body unit_typ in
          if not is_dec (* undo reverse direction in annotated ast for downto loop *) then
            annot_exp (E_for (v, inferred_f, inferred_t, checked_step, ord, checked_body)) unit_typ
          else annot_exp (E_for (v, inferred_t, inferred_f, checked_step, ord, checked_body)) unit_typ
      | _, _ -> typ_error l "Ranges in foreach overlap"
    end
  | E_if (cond, then_branch, else_branch) ->
      let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
      let then_branch' =
        irule infer_exp (add_opt_constraint l "then branch" (assert_constraint env true cond') env) then_branch
      in
      (* We don't have generic type union in Sail, but we can union simple numeric types. *)
      begin
        match destruct_numeric (Env.expand_synonyms env (typ_of then_branch')) with
        | Some (kids, nc, then_nexp) ->
            let then_sn = to_simple_numeric l kids nc then_nexp in
            let else_branch' =
              irule infer_exp
                (add_opt_constraint l "else branch" (Option.map nc_not (assert_constraint env false cond')) env)
                else_branch
            in
            begin
              match destruct_numeric (Env.expand_synonyms env (typ_of else_branch')) with
              | Some (kids, nc, else_nexp) ->
                  let else_sn = to_simple_numeric l kids nc else_nexp in
                  let typ = typ_of_simple_numeric (union_simple_numeric then_sn else_sn) in
                  annot_exp (E_if (cond', then_branch', else_branch')) typ
              | None -> typ_error l ("Could not infer type of " ^ string_of_exp else_branch)
            end
        | None -> begin
            match typ_of then_branch' with
            | Typ_aux (Typ_app (f, [_]), _) when string_of_id f = "atom_bool" ->
                let else_branch' =
                  crule check_exp
                    (add_opt_constraint l "else branch" (Option.map nc_not (assert_constraint env false cond')) env)
                    else_branch bool_typ
                in
                annot_exp (E_if (cond', then_branch', else_branch')) bool_typ
            | _ ->
                let else_branch' =
                  crule check_exp
                    (add_opt_constraint l "else branch" (Option.map nc_not (assert_constraint env false cond')) env)
                    else_branch (typ_of then_branch')
                in
                annot_exp (E_if (cond', then_branch', else_branch')) (typ_of then_branch')
          end
      end
  | E_vector_access (v, n) -> begin
      try infer_exp env (E_aux (E_app (mk_id "vector_access", [v; n]), (l, uannot))) with
      | Type_error (err_l, err) -> (
          try
            let inferred_v = infer_exp env v in
            begin
              match (typ_of inferred_v, n) with
              | Typ_aux (Typ_id id, _), E_aux (E_id field, _) ->
                  let access_id = (Bitfield.field_accessor_ids id field).get in
                  infer_exp env (mk_exp ~loc:l (E_app (access_id, [v])))
              | _, _ -> typ_error l "Vector access could not be interpreted as a bitfield access"
            end
          with Type_error (err_l', err') -> typ_raise err_l (err_because (err, err_l', err'))
        )
      | exn -> raise exn
    end
  | E_vector_update (v, n, exp) -> begin
      try infer_exp env (E_aux (E_app (mk_id "vector_update", [v; n; exp]), (l, uannot))) with
      | Type_error (err_l, err) -> (
          try
            let inferred_v = infer_exp env v in
            begin
              match (typ_of inferred_v, n) with
              | Typ_aux (Typ_id id, _), E_aux (E_id field, _) ->
                  let update_id = (Bitfield.field_accessor_ids id field).update in
                  infer_exp env (mk_exp ~loc:l (E_app (update_id, [v; exp])))
              | _, _ -> typ_error l "Vector update could not be interpreted as a bitfield update"
            end
          with Type_error (err_l', err') -> typ_raise err_l (err_because (err, err_l', err'))
        )
      | exn -> raise exn
    end
  | E_vector_update_subrange (v, n, m, exp) ->
      infer_exp env (E_aux (E_app (mk_id "vector_update_subrange", [v; n; m; exp]), (l, uannot)))
  | E_vector_append (v1, E_aux (E_vector [], _)) -> infer_exp env v1
  | E_vector_append (v1, v2) -> infer_exp env (E_aux (E_app (mk_id "append", [v1; v2]), (l, uannot)))
  | E_vector_subrange (v, n, m) -> infer_exp env (E_aux (E_app (mk_id "vector_subrange", [v; n; m]), (l, uannot)))
  | E_vector [] -> typ_error l "Cannot infer type of empty vector"
  | E_vector (item :: items as vec) ->
      let inferred_item = irule infer_exp env item in
      let checked_items = List.map (fun i -> crule check_exp env i (typ_of inferred_item)) items in
      begin
        match typ_of inferred_item with
        | Typ_aux (Typ_id id, _) when string_of_id id = "bit" ->
            let bitvec_typ = bits_typ env (nint (List.length vec)) in
            annot_exp (E_vector (inferred_item :: checked_items)) bitvec_typ
        | _ ->
            let vec_typ = dvector_typ env (nint (List.length vec)) (typ_of inferred_item) in
            annot_exp (E_vector (inferred_item :: checked_items)) vec_typ
      end
  | E_assert (test, msg) ->
      let msg = assert_msg msg in
      let checked_test = crule check_exp env test bool_typ in
      let checked_msg = crule check_exp env msg string_typ in
      annot_exp (E_assert (checked_test, checked_msg)) unit_typ
  | E_internal_return exp ->
      let inferred_exp = irule infer_exp env exp in
      annot_exp (E_internal_return inferred_exp) (typ_of inferred_exp)
  | E_internal_plet (pat, bind, body) ->
      let bind_exp, ptyp =
        match pat with
        | P_aux (P_typ (ptyp, _), _) ->
            Env.wf_typ env ptyp;
            let checked_bind = crule check_exp env bind ptyp in
            (checked_bind, ptyp)
        | _ ->
            let inferred_bind = irule infer_exp env bind in
            (inferred_bind, typ_of inferred_bind)
      in
      let tpat, env = bind_pat_no_guard env pat ptyp in
      (* Propagate constraint assertions on the lhs of monadic binds to the rhs *)
      let env =
        match bind_exp with
        | E_aux (E_assert (constr_exp, _), _) -> begin
            match assert_constraint env true constr_exp with
            | Some nc ->
                typ_print (lazy ("Adding constraint " ^ string_of_n_constraint nc ^ " for assert"));
                Env.add_constraint nc env
            | None -> env
          end
        | _ -> env
      in
      let inferred_body = irule infer_exp env body in
      annot_exp (E_internal_plet (tpat, bind_exp, inferred_body)) (typ_of inferred_body)
  | E_let (LB_aux (letbind, (let_loc, _)), exp) ->
      let bind_exp, pat, ptyp =
        match letbind with
        | LB_val ((P_aux (P_typ (ptyp, _), _) as pat), bind) ->
            Env.wf_typ env ptyp;
            let checked_bind = crule check_exp env bind ptyp in
            (checked_bind, pat, ptyp)
        | LB_val (pat, bind) ->
            let inferred_bind = irule infer_exp env bind in
            (inferred_bind, pat, typ_of inferred_bind)
      in
      ignore (check_pattern_duplicates env pat);
      let tpat, inner_env = bind_pat_no_guard env pat ptyp in
      let inferred_exp = irule infer_exp inner_env exp in
      annot_exp
        (E_let (LB_aux (LB_val (tpat, bind_exp), (let_loc, empty_tannot)), inferred_exp))
        (check_shadow_leaks l inner_env env (typ_of inferred_exp))
  | E_ref id when Env.is_register id env ->
      let typ = Env.get_register id env in
      annot_exp (E_ref id) (register_typ typ)
  | E_internal_assume (nc, exp) ->
      Env.wf_constraint env nc;
      let env = Env.add_constraint nc env in
      let exp' = irule infer_exp env exp in
      annot_exp (E_internal_assume (nc, exp')) (typ_of exp')
  | _ -> typ_error l ("Cannot infer type of: " ^ string_of_exp exp)

and infer_funapp l env f xs ret_ctx_typ = infer_funapp' l env f (Env.get_val_spec f env) xs ret_ctx_typ

and instantiation_of (E_aux (_, (l, tannot)) as exp) =
  match fst tannot with
  | Some t -> begin
      match t.instantiation with
      | Some inst -> inst
      | None -> raise (Reporting.err_unreachable l __POS__ "Passed non type-checked function to instantiation_of")
    end
  | _ -> invalid_arg ("instantiation_of expected application,  got " ^ string_of_exp exp)

and instantiation_of_without_type (E_aux (exp_aux, (l, _)) as exp) =
  let env = env_of exp in
  match exp_aux with
  | E_app (f, xs) -> instantiation_of (infer_funapp' l env f (Env.get_val_spec f env) (List.map strip_exp xs) None)
  | _ -> invalid_arg ("instantiation_of expected application,  got " ^ string_of_exp exp)

and infer_funapp' l env f (typq, f_typ) xs expected_ret_typ =
  typ_print (lazy (Util.("Function " |> cyan |> clear) ^ string_of_id f));
  let annot_exp exp typ inst =
    E_aux
      ( exp,
        ( l,
          (Some { env; typ; monadic = no_effect; expected = expected_ret_typ; instantiation = Some inst }, empty_uannot)
        )
      )
  in
  let is_bound env kid = KBindings.mem kid (Env.get_typ_vars env) in

  (* First we record all the type variables when we start checking the
     application, so we can distinguish them from existentials
     introduced by instantiating function arguments later. *)
  let universals = Env.get_typ_vars env in
  let universal_constraints = Env.get_constraints env in

  let all_unifiers = ref KBindings.empty in
  let record_unifiers unifiers =
    let previous_unifiers = !all_unifiers in
    let updated_unifiers = KBindings.map (subst_unifiers_typ_arg unifiers) previous_unifiers in
    all_unifiers := merge_uvars env l updated_unifiers unifiers
  in

  let quants, typ_args, typ_ret =
    match Env.expand_synonyms (Env.add_typquant l typq env) f_typ with
    | Typ_aux (Typ_fn (typ_args, typ_ret), _) -> (ref (quant_items typq), typ_args, ref typ_ret)
    | _ -> typ_error l (string_of_typ f_typ ^ " is not a function type")
  in

  let unifiers = instantiate_simple_equations !quants in
  typ_debug (lazy "Instantiating from equations");
  typ_debug
    ( lazy
      (string_of_list ", "
         (fun (kid, arg) -> string_of_kid kid ^ " => " ^ string_of_typ_arg arg)
         (KBindings.bindings unifiers)
      )
      );
  all_unifiers := unifiers;
  let typ_args = List.map (subst_unifiers unifiers) typ_args in
  List.iter (fun unifier -> quants := instantiate_quants !quants unifier) (KBindings.bindings unifiers);
  List.iter (fun (v, arg) -> typ_ret := typ_subst v arg !typ_ret) (KBindings.bindings unifiers);

  typ_debug (lazy ("Quantifiers " ^ Util.string_of_list ", " string_of_quant_item !quants));

  let implicits, typ_args, xs =
    let typ_args' = List.filter is_not_implicit typ_args in
    match (xs, typ_args') with
    (* Support the case where a function has only implicit arguments;
       allow it to be called either as f() or f(i...) *)
    | [E_aux (E_lit (L_aux (L_unit, _)), _)], [] -> (get_implicits typ_args, [], [])
    | _ ->
        if not (List.length typ_args = List.length xs) then
          if not (List.length typ_args' = List.length xs) then
            typ_error l
              (Printf.sprintf "Function %s applied to %d args, expected %d (%d explicit): %s" (string_of_id f)
                 (List.length xs) (List.length typ_args) (List.length typ_args')
                 (String.concat ", " (List.map string_of_typ typ_args))
              )
          else (get_implicits typ_args, typ_args', xs)
        else ([], List.map implicit_to_int typ_args, xs)
  in

  let typ_args =
    match expected_ret_typ with
    | None -> typ_args
    | Some expect when is_exist (Env.expand_synonyms env expect) || is_exist !typ_ret -> typ_args
    | Some expect -> (
        let goals = quant_kopts (mk_typquant !quants) |> List.map kopt_kid |> KidSet.of_list in
        try
          let unifiers = unify l env (KidSet.diff goals (ambiguous_vars !typ_ret)) !typ_ret expect in
          record_unifiers unifiers;
          let unifiers = KBindings.bindings unifiers in
          typ_debug
            ( lazy
              (Util.("Unifiers " |> magenta |> clear)
              ^ Util.string_of_list ", " (fun (v, arg) -> string_of_kid v ^ " => " ^ string_of_typ_arg arg) unifiers
              )
              );
          List.iter (fun unifier -> quants := instantiate_quants !quants unifier) unifiers;
          List.iter (fun (v, arg) -> typ_ret := typ_subst v arg !typ_ret) unifiers;
          List.map (fun typ -> List.fold_left (fun typ (v, arg) -> typ_subst v arg typ) typ unifiers) typ_args
        with Unification_error _ -> typ_args
      )
  in

  (* We now iterate throught the function arguments, checking them and
     instantiating quantifiers. *)
  let instantiate env arg typ remaining_typs =
    if KidSet.for_all (is_bound env) (tyvars_of_typ typ) then (crule check_exp env arg typ, remaining_typs, env)
    else (
      let goals = quant_kopts (mk_typquant !quants) |> List.map kopt_kid |> KidSet.of_list in
      typ_debug (lazy ("Quantifiers " ^ Util.string_of_list ", " string_of_quant_item !quants));
      let inferred_arg = irule infer_exp env arg in
      let inferred_arg, unifiers, env =
        try can_unify_with env goals inferred_arg typ with Unification_error (l, m) -> typ_error l m
      in
      record_unifiers unifiers;
      let unifiers = KBindings.bindings unifiers in
      typ_debug
        ( lazy
          (Util.("Unifiers " |> magenta |> clear)
          ^ Util.string_of_list ", " (fun (v, arg) -> string_of_kid v ^ " => " ^ string_of_typ_arg arg) unifiers
          )
          );
      List.iter (fun unifier -> quants := instantiate_quants !quants unifier) unifiers;
      List.iter (fun (v, arg) -> typ_ret := typ_subst v arg !typ_ret) unifiers;
      let remaining_typs =
        List.map (fun typ -> List.fold_left (fun typ (v, arg) -> typ_subst v arg typ) typ unifiers) remaining_typs
      in
      (inferred_arg, remaining_typs, env)
    )
  in
  let fold_instantiate (xs, args, env) x =
    match args with
    | arg :: remaining_args ->
        let x, remaining_args, env = instantiate env x arg remaining_args in
        (x :: xs, remaining_args, env)
    | [] -> raise (Reporting.err_unreachable l __POS__ "Empty arguments during instantiation")
  in
  let xs, _, env = List.fold_left fold_instantiate ([], typ_args, env) xs in
  let xs = List.rev xs in

  let solve_implicit impl =
    match KBindings.find_opt impl !all_unifiers with
    | Some (A_aux (A_nexp (Nexp_aux (Nexp_constant c, _)), _)) -> irule infer_exp env (mk_lit_exp (L_num c))
    | Some (A_aux (A_nexp n, _)) -> irule infer_exp env (mk_exp (E_sizeof n))
    | _ ->
        typ_error l
          ("Cannot solve implicit " ^ string_of_kid impl ^ " in "
          ^ string_of_exp (mk_exp (E_app (f, List.map strip_exp xs)))
          )
  in
  let xs = List.map solve_implicit implicits @ xs in

  if not (List.for_all (solve_quant env) !quants) then
    typ_raise l
      (Err_unresolved_quants (f, !quants, Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env))
  else ();

  let ty_vars = KBindings.bindings (Env.get_typ_vars env) |> List.map (fun (v, k) -> mk_kopt k v) in
  let existentials = List.filter (fun kopt -> not (KBindings.mem (kopt_kid kopt) universals)) ty_vars in
  let num_new_ncs = List.length (Env.get_constraints env) - List.length universal_constraints in
  let ex_constraints = take num_new_ncs (Env.get_constraints env) in

  typ_debug (lazy ("Existentials: " ^ string_of_list ", " string_of_kinded_id existentials));
  typ_debug (lazy ("Existential constraints: " ^ string_of_list ", " string_of_n_constraint ex_constraints));

  let universals = KBindings.bindings universals |> List.map fst |> KidSet.of_list in
  let typ_ret =
    if
      KidSet.is_empty (KidSet.of_list (List.map kopt_kid existentials))
      || KidSet.is_empty (KidSet.diff (tyvars_of_typ !typ_ret) universals)
    then !typ_ret
    else mk_typ (Typ_exist (existentials, List.fold_left nc_and nc_true ex_constraints, !typ_ret))
  in
  let typ_ret = simp_typ typ_ret in
  let exp = annot_exp (E_app (f, xs)) typ_ret !all_unifiers in
  typ_debug (lazy ("Returning: " ^ string_of_exp exp));
  exp

and bind_mpat allow_unknown other_env env (MP_aux (mpat_aux, (l, uannot)) as mpat) typ =
  let typ, env = bind_existential l None typ env in
  typ_print (lazy (Util.("Binding " |> yellow |> clear) ^ string_of_mpat mpat ^ " to " ^ string_of_typ typ));
  let annot_mpat mpat typ' = MP_aux (mpat, (l, mk_expected_tannot env typ' (Some typ))) in
  let switch_typ mpat typ =
    match mpat with
    | MP_aux (pat_aux, (l, (Some tannot, uannot))) -> MP_aux (pat_aux, (l, (Some { tannot with typ }, uannot)))
    | _ -> typ_error l "Cannot switch type for unannotated mapping-pattern"
  in
  let bind_tuple_mpat (tpats, env, guards) mpat typ =
    let tpat, env, guards' = bind_mpat allow_unknown other_env env mpat typ in
    (tpat :: tpats, env, guards' @ guards)
  in
  match mpat_aux with
  | MP_id v -> begin
      (* If the identifier we're matching on is also a constructor of
         a union, that's probably a mistake, so warn about it. *)
      if Env.is_union_constructor v env then
        Reporting.warn
          (Printf.sprintf "Identifier %s found in mapping-pattern is also a union constructor at" (string_of_id v))
          l ""
      else ();
      match Env.lookup_id v env with
      | Local (Immutable, _) | Unbound _ -> (annot_mpat (MP_id v) typ, Env.add_local v (Immutable, typ) env, [])
      | Local (Mutable, _) | Register _ ->
          typ_error l
            ("Cannot shadow mutable local or register in switch statement mapping-pattern " ^ string_of_mpat mpat)
      | Enum enum ->
          subtyp l env enum typ;
          (annot_mpat (MP_id v) typ, env, [])
    end
  | MP_cons (hd_mpat, tl_mpat) -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let hd_mpat, env, hd_guards = bind_mpat allow_unknown other_env env hd_mpat ltyp in
          let tl_mpat, env, tl_guards = bind_mpat allow_unknown other_env env tl_mpat typ in
          (annot_mpat (MP_cons (hd_mpat, tl_mpat)) typ, env, hd_guards @ tl_guards)
      | _ -> typ_error l "Cannot match cons mapping-pattern against non-list type"
    end
  | MP_string_append mpats -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_id id, _) when Id.compare id (mk_id "string") = 0 ->
          let rec process_mpats env = function
            | [] -> ([], env, [])
            | pat :: pats ->
                let pat', env, guards = bind_mpat allow_unknown other_env env pat typ in
                let pats', env, guards' = process_mpats env pats in
                (pat' :: pats', env, guards @ guards')
          in
          let pats, env, guards = process_mpats env mpats in
          (annot_mpat (MP_string_append pats) typ, env, guards)
      | _ -> typ_error l "Cannot match string-append pattern against non-string type"
    end
  | MP_list mpats -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let rec process_mpats env = function
            | [] -> ([], env, [])
            | _ :: mpats ->
                let mpat', env, guards = bind_mpat allow_unknown other_env env mpat ltyp in
                let mpats', env, guards' = process_mpats env mpats in
                (mpat' :: mpats', env, guards @ guards')
          in
          let mpats, env, guards = process_mpats env mpats in
          (annot_mpat (MP_list mpats) typ, env, guards)
      | _ ->
          typ_error l
            ("Cannot match list mapping-pattern " ^ string_of_mpat mpat ^ "  against non-list type " ^ string_of_typ typ)
    end
  | MP_tuple [] -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_id typ_id, _) when string_of_id typ_id = "unit" -> (annot_mpat (MP_tuple []) typ, env, [])
      | _ -> typ_error l "Cannot match unit mapping-pattern against non-unit type"
    end
  | MP_tuple mpats -> begin
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_tuple typs, _) ->
          let tpats, env, guards =
            try List.fold_left2 bind_tuple_mpat ([], env, []) mpats typs
            with Invalid_argument _ -> typ_error l "Tuple mapping-pattern and tuple type have different length"
          in
          (annot_mpat (MP_tuple (List.rev tpats)) typ, env, guards)
      | _ -> typ_error l "Cannot bind tuple mapping-pattern against non tuple type"
    end
  | MP_app (f, mpats) when Env.is_union_constructor f env -> begin
      let typq, ctor_typ = Env.get_val_spec f env in
      let quants = quant_items typq in
      let untuple (Typ_aux (typ_aux, _) as typ) = match typ_aux with Typ_tuple typs -> typs | _ -> [typ] in
      match Env.expand_synonyms env ctor_typ with
      | Typ_aux (Typ_fn ([arg_typ], ret_typ), _) -> begin
          try
            typ_debug
              (lazy ("Unifying " ^ string_of_bind (typq, ctor_typ) ^ " for mapping-pattern " ^ string_of_typ typ));
            let unifiers = unify l env (tyvars_of_typ ret_typ) ret_typ typ in
            let arg_typ' = subst_unifiers unifiers arg_typ in
            let quants' = List.fold_left instantiate_quants quants (KBindings.bindings unifiers) in
            if not (List.for_all (solve_quant env) quants') then
              typ_raise l
                (Err_unresolved_quants
                   (f, quants', Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
                );
            let _ret_typ' = subst_unifiers unifiers ret_typ in
            let tpats, env, guards =
              try List.fold_left2 bind_tuple_mpat ([], env, []) mpats (untuple arg_typ')
              with Invalid_argument _ ->
                typ_error l "Union constructor mapping-pattern arguments have incorrect length"
            in
            (annot_mpat (MP_app (f, List.rev tpats)) typ, env, guards)
          with Unification_error (l, m) ->
            typ_error l ("Unification error when mapping-pattern matching against union constructor: " ^ m)
        end
      | _ -> typ_error l ("Mal-formed constructor " ^ string_of_id f ^ " with type " ^ string_of_typ ctor_typ)
    end
  | MP_app (other, [mpat]) when Env.is_mapping other env -> begin
      let typq, mapping_typ = Env.get_val_spec other env in
      let quants = quant_items typq in
      match Env.expand_synonyms env mapping_typ with
      | Typ_aux (Typ_bidir (typ1, typ2), _) -> begin
          try
            typ_debug
              (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for mapping-pattern " ^ string_of_typ typ));
            let unifiers = unify l env (tyvars_of_typ typ2) typ2 typ in
            let arg_typ' = subst_unifiers unifiers typ1 in
            let quants' = List.fold_left instantiate_quants quants (KBindings.bindings unifiers) in
            if not (List.for_all (solve_quant env) quants') then
              typ_raise l
                (Err_unresolved_quants
                   (other, quants', Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
                );
            let _ret_typ' = subst_unifiers unifiers typ2 in
            let tpat, env, guards = bind_mpat allow_unknown other_env env mpat arg_typ' in
            (annot_mpat (MP_app (other, [tpat])) typ, env, guards)
          with Unification_error (l, _) -> (
            try
              typ_debug (lazy "Unifying mapping forwards failed, trying backwards.");
              typ_debug
                (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for mapping-pattern " ^ string_of_typ typ));
              let unifiers = unify l env (tyvars_of_typ typ1) typ1 typ in
              let arg_typ' = subst_unifiers unifiers typ2 in
              let quants' = List.fold_left instantiate_quants quants (KBindings.bindings unifiers) in
              if not (List.for_all (solve_quant env) quants') then
                typ_raise l
                  (Err_unresolved_quants
                     (other, quants', Env.get_locals env, Env.get_typ_vars_info env, Env.get_constraints env)
                  );
              let _ret_typ' = subst_unifiers unifiers typ1 in
              let tpat, env, guards = bind_mpat allow_unknown other_env env mpat arg_typ' in
              (annot_mpat (MP_app (other, [tpat])) typ, env, guards)
            with Unification_error (l, m) ->
              typ_error l ("Unification error when pattern matching against mapping constructor: " ^ m)
          )
        end
      | _ -> Reporting.unreachable l __POS__ "unifying mapping type, expanded synonyms to non-mapping type!"
    end
  | MP_app (other, mpats) when Env.is_mapping other env ->
      bind_mpat allow_unknown other_env env (MP_aux (MP_app (other, [mk_mpat (MP_tuple mpats)]), (l, uannot))) typ
  | MP_app (f, _) when not (Env.is_union_constructor f env || Env.is_mapping f env) ->
      typ_error l (string_of_id f ^ " is not a union constructor or mapping in mapping-pattern " ^ string_of_mpat mpat)
  | MP_as (mpat, id) ->
      let typed_mpat, env, guards = bind_mpat allow_unknown other_env env mpat typ in
      ( annot_mpat (MP_as (typed_mpat, id)) (typ_of_mpat typed_mpat),
        Env.add_local id (Immutable, typ_of_mpat typed_mpat) env,
        guards
      )
  (* This is a special case for flow typing when we match a constant numeric literal. *)
  | MP_lit (L_aux (L_num n, _) as lit) when is_atom typ ->
      let nexp = match destruct_atom_nexp env typ with Some n -> n | None -> assert false in
      (annot_mpat (MP_lit lit) (atom_typ (nconstant n)), Env.add_constraint (nc_eq nexp (nconstant n)) env, [])
  (* Similarly, for boolean literals *)
  | MP_lit (L_aux (L_true, _) as lit) when is_atom_bool typ ->
      let nc = match destruct_atom_bool env typ with Some n -> n | None -> assert false in
      (annot_mpat (MP_lit lit) (atom_bool_typ nc_true), Env.add_constraint nc env, [])
  | MP_lit (L_aux (L_false, _) as lit) when is_atom_bool typ ->
      let nc = match destruct_atom_bool env typ with Some n -> n | None -> assert false in
      (annot_mpat (MP_lit lit) (atom_bool_typ nc_false), Env.add_constraint (nc_not nc) env, [])
  | MP_struct fmpats ->
      let rectyp_id =
        match Env.expand_synonyms env typ with
        | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
            rectyp_id
        | _ -> typ_error l ("The type " ^ string_of_typ typ ^ " is not a record")
      in
      let record_fields = ref (Env.get_record rectyp_id env |> snd |> List.map snd |> IdSet.of_list) in
      let bind_fmpat (fmpats, env, guards) (field, mpat) =
        record_fields := IdSet.remove field !record_fields;
        let _, rectyp_q, field_typ = Env.get_accessor rectyp_id field env in
        let unifiers =
          try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ
          with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m)
        in
        let field_typ' = subst_unifiers unifiers field_typ in
        let typed_mpat, env, new_guards = bind_mpat allow_unknown other_env env mpat field_typ' in
        ((field, typed_mpat) :: fmpats, env, guards @ new_guards)
      in
      let fmpats, env, guards = List.fold_left bind_fmpat ([], env, []) fmpats in
      if IdSet.is_empty !record_fields then (annot_mpat (MP_struct (List.rev fmpats)) typ, env, guards)
      else
        typ_error l
          ("struct pattern missing fields: " ^ string_of_list ", " string_of_id (IdSet.elements !record_fields))
  | MP_vector_concat (mpat :: mpats) ->
      bind_vector_concat_mpat l allow_unknown other_env env uannot mpat mpats (Some typ)
  | _ -> (
      let inferred_mpat, env, guards = infer_mpat allow_unknown other_env env mpat in
      match subtyp l env typ (typ_of_mpat inferred_mpat) with
      | () -> (switch_typ inferred_mpat (typ_of_mpat inferred_mpat), env, guards)
      | exception (Type_error _ as typ_exn) -> (
          match mpat_aux with
          | MP_lit lit ->
              let var = fresh_var () in
              let guard = mk_exp ~loc:l (E_app_infix (mk_exp (E_id var), mk_id "==", mk_exp (E_lit lit))) in
              let typed_mpat, env, guards = bind_mpat allow_unknown other_env env (mk_mpat (MP_id var)) typ in
              (typed_mpat, env, guard :: guards)
          | _ -> raise typ_exn
        )
    )

and infer_mpat allow_unknown other_env env (MP_aux (mpat_aux, (l, uannot)) as mpat) =
  let annot_mpat mpat typ = MP_aux (mpat, (l, mk_tannot env typ)) in
  match mpat_aux with
  | MP_id v -> begin
      match Env.lookup_id v env with
      | Local (Immutable, _) | Unbound _ -> begin
          match Env.lookup_id v other_env with
          | Local (Immutable, typ) ->
              bind_mpat allow_unknown other_env env (mk_mpat (MP_typ (mk_mpat (MP_id v), typ))) typ
          | Unbound _ ->
              if allow_unknown then (annot_mpat (MP_id v) unknown_typ, env, [])
              else
                typ_error l
                  ("Cannot infer identifier in mapping-pattern " ^ string_of_mpat mpat
                 ^ " - try adding a type annotation"
                  )
          | _ -> assert false
        end
      | Local (Mutable, _) | Register _ ->
          typ_error l ("Cannot shadow mutable local or register in mapping-pattern " ^ string_of_mpat mpat)
      | Enum enum -> (annot_mpat (MP_id v) enum, env, [])
    end
  | MP_vector_subrange (id, n, m) ->
      let len =
        match Env.get_default_order env with
        | Ord_aux (Ord_dec, _) ->
            if Big_int.greater_equal n m then Big_int.sub (Big_int.succ n) m
            else
              typ_error l
                (Printf.sprintf "%s must be greater than or equal to %s" (Big_int.to_string n) (Big_int.to_string m))
        | Ord_aux (Ord_inc, _) ->
            if Big_int.less_equal n m then Big_int.sub (Big_int.succ m) n
            else
              typ_error l
                (Printf.sprintf "%s must be less than or equal to %s" (Big_int.to_string n) (Big_int.to_string m))
      in
      begin
        match Env.lookup_id id env with
        | Local (Immutable, _) | Unbound _ -> begin
            match Env.lookup_id id other_env with
            | Unbound _ ->
                if allow_unknown then
                  (annot_mpat (MP_vector_subrange (id, n, m)) (bitvector_typ (nconstant len)), env, [])
                else typ_error l "Cannot infer identifier type in vector subrange pattern"
            | Local (Immutable, other_typ) ->
                let id_len = destruct_bitvector_typ l env other_typ in
                begin
                  match id_len with
                  | Nexp_aux (Nexp_constant id_len, _) when Big_int.greater_equal id_len len ->
                      (annot_mpat (MP_vector_subrange (id, n, m)) (bitvector_typ (nconstant len)), env, [])
                  | _ ->
                      typ_error l
                        (Printf.sprintf "%s must have a constant length greater than or equal to %s" (string_of_id id)
                           (Big_int.to_string len)
                        )
                end
            | _ -> typ_error l "Invalid identifier in vector subrange pattern"
          end
        | Local _ | Register _ -> typ_error l "Invalid identifier in vector subrange pattern"
        | Enum e ->
            typ_error l
              (Printf.sprintf "Identifier %s is a member of enumeration %s in vector subrange pattern" (string_of_id id)
                 (string_of_typ e)
              )
      end
  | MP_app (f, _) when Env.is_union_constructor f env -> begin
      let _, ctor_typ = Env.get_val_spec f env in
      match Env.expand_synonyms env ctor_typ with
      | Typ_aux (Typ_fn (_, ret_typ), _) -> bind_mpat allow_unknown other_env env mpat ret_typ
      | _ -> typ_error l ("Mal-formed constructor " ^ string_of_id f)
    end
  | MP_app (f, _) when Env.is_mapping f env -> begin
      let _, mapping_typ = Env.get_val_spec f env in
      match Env.expand_synonyms env mapping_typ with
      | Typ_aux (Typ_bidir (typ1, typ2), _) -> begin
          try bind_mpat allow_unknown other_env env mpat typ2
          with Type_error _ -> bind_mpat allow_unknown other_env env mpat typ1
        end
      | _ -> typ_error l ("Malformed mapping type " ^ string_of_id f)
    end
  | MP_lit lit -> (annot_mpat (MP_lit lit) (infer_lit env lit), env, [])
  | MP_typ (mpat, typ_annot) ->
      Env.wf_typ env typ_annot;
      let typed_mpat, env, guards = bind_mpat allow_unknown other_env env mpat typ_annot in
      (annot_mpat (MP_typ (typed_mpat, typ_annot)) typ_annot, env, guards)
  | MP_vector (mpat :: mpats) ->
      let fold_mpats (mpats, env, guards) mpat =
        let typed_mpat, env, guards' = bind_mpat allow_unknown other_env env mpat bit_typ in
        (mpats @ [typed_mpat], env, guards' @ guards)
      in
      let mpats, env, guards = List.fold_left fold_mpats ([], env, []) (mpat :: mpats) in
      let len = nexp_simp (nint (List.length mpats)) in
      let etyp = typ_of_mpat (List.hd mpats) in
      List.iter (fun mpat -> typ_equality l env etyp (typ_of_mpat mpat)) mpats;
      (annot_mpat (MP_vector mpats) (dvector_typ env len etyp), env, guards)
  | MP_vector_concat (mpat :: mpats) -> bind_vector_concat_mpat l allow_unknown other_env env uannot mpat mpats None
  | MP_string_append mpats ->
      let fold_pats (pats, env, guards) pat =
        let inferred_pat, env, guards' = infer_mpat allow_unknown other_env env pat in
        typ_equality l env (typ_of_mpat inferred_pat) string_typ;
        (pats @ [inferred_pat], env, guards' @ guards)
      in
      let typed_mpats, env, guards = List.fold_left fold_pats ([], env, []) mpats in
      (annot_mpat (MP_string_append typed_mpats) string_typ, env, guards)
  | MP_as (mpat, id) ->
      let typed_mpat, env, guards = infer_mpat allow_unknown other_env env mpat in
      ( annot_mpat (MP_as (typed_mpat, id)) (typ_of_mpat typed_mpat),
        Env.add_local id (Immutable, typ_of_mpat typed_mpat) env,
        guards
      )
  | _ -> typ_error l ("Couldn't infer type of mapping-pattern " ^ string_of_mpat mpat)

(**************************************************************************)
(* 6. Effect system                                                       *)
(**************************************************************************)

let effect_of_annot = function Some t, _ -> t.monadic | None, _ -> no_effect

let effect_of (E_aux (_, (_, annot))) = effect_of_annot annot

let add_effect_annot annot eff =
  match annot with Some tannot, uannot -> (Some { tannot with monadic = eff }, uannot) | None, uannot -> (None, uannot)

let effect_of_pat (P_aux (_, (_, annot))) = effect_of_annot annot

(**************************************************************************)
(* 7. Checking toplevel definitions                                       *)
(**************************************************************************)

let check_duplicate_letbinding l pat env =
  match IdSet.choose_opt (IdSet.inter (pat_ids pat) (Env.get_toplevel_lets env)) with
  | Some id -> typ_error l ("Duplicate toplevel let binding " ^ string_of_id id)
  | None -> ()

let check_letdef orig_env def_annot (LB_aux (letbind, (l, _))) =
  typ_print (lazy ("\nChecking top-level let" |> cyan |> clear));
  match letbind with
  | LB_val ((P_aux (P_typ (typ_annot, _), _) as pat), bind) ->
      check_duplicate_letbinding l pat orig_env;
      Env.wf_typ orig_env typ_annot;
      let checked_bind = crule check_exp orig_env bind typ_annot in
      let tpat, env = bind_pat_no_guard orig_env pat typ_annot in
      ( [DEF_aux (DEF_let (LB_aux (LB_val (tpat, checked_bind), (l, empty_tannot))), def_annot)],
        Env.add_toplevel_lets (pat_ids tpat) env
      )
  | LB_val (pat, bind) ->
      check_duplicate_letbinding l pat orig_env;
      let inferred_bind = irule infer_exp orig_env bind in
      let tpat, env = bind_pat_no_guard orig_env pat (typ_of inferred_bind) in
      ( [DEF_aux (DEF_let (LB_aux (LB_val (tpat, inferred_bind), (l, empty_tannot))), def_annot)],
        Env.add_toplevel_lets (pat_ids tpat) env
      )

let bind_funcl_arg_typ l env typ =
  match typ with
  | Typ_aux (Typ_fn (typ_args, typ_ret), _) -> begin
      let env = Env.add_ret_typ typ_ret env in
      match List.map implicit_to_int typ_args with
      | [typ_arg] -> (typ_arg, typ_ret, env)
      | typ_args ->
          (* This is one of the cases where we are allowed to treat
             function arguments as like a tuple, normally we can't. *)
          (Typ_aux (Typ_tuple typ_args, l), typ_ret, env)
    end
  | _ -> typ_error l ("Function clause must have function type: " ^ string_of_typ typ ^ " is not a function type")

let check_funcl env (FCL_aux (FCL_funcl (id, pexp), (def_annot, _))) typ =
  let l = def_annot.loc in
  let typ_arg, typ_ret, env = bind_funcl_arg_typ l env typ in
  (* We want to forbid polymorphic undefined values in all cases,
     except when type checking the specific undefined_(type) functions
     created by the -undefined_gen functions in initial_check.ml. Only
     in these functions will the rewriter be able to correctly
     re-write the polymorphic undefineds (due to the specific form the
     functions have *)
  let env =
    if Str.string_match (Str.regexp_string "undefined_") (string_of_id id) 0 then Env.allow_polymorphic_undefineds env
    else env
  in
  let typed_pexp = check_case env typ_arg pexp typ_ret in
  FCL_aux (FCL_funcl (id, typed_pexp), (def_annot, mk_expected_tannot env typ (Some typ)))

let check_mapcl env (MCL_aux (cl, (def_annot, _))) typ =
  let ignore_errors ~default f = try f () with Type_error _ -> default in
  let find_types env mpat typ =
    ignore_errors ~default:env (fun () ->
        let _, output_env, _ = bind_mpat true Env.empty (Env.set_allow_unknowns true env) mpat typ in
        output_env
    )
  in
  match typ with
  | Typ_aux (Typ_bidir (typ1, typ2), _) -> begin
      match cl with
      | MCL_bidir (left_mpexp, right_mpexp) -> begin
          let left_mpat, _, _ = destruct_mpexp left_mpexp in
          let left_dups = check_pattern_duplicates env (pat_of_mpat left_mpat) in
          let left_id_env = find_types env left_mpat typ1 in
          let right_mpat, _, _ = destruct_mpexp right_mpexp in
          let right_dups = check_pattern_duplicates env (pat_of_mpat right_mpat) in
          same_bindings env left_dups right_dups;
          let right_id_env = find_types env right_mpat typ2 in

          let typed_left_mpexp = check_mpexp right_id_env env left_mpexp typ1 in
          let typed_right_mpexp = check_mpexp left_id_env env right_mpexp typ2 in
          MCL_aux (MCL_bidir (typed_left_mpexp, typed_right_mpexp), (def_annot, mk_expected_tannot env typ (Some typ)))
        end
      | MCL_forwards (mpexp, exp) -> begin
          let mpat, _, _ = destruct_mpexp mpexp in
          ignore (check_pattern_duplicates env (pat_of_mpat mpat));
          let _, mpat_env, _ = bind_mpat false Env.empty env mpat typ1 in
          let typed_mpexp = check_mpexp Env.empty env mpexp typ1 in
          let typed_exp = check_exp mpat_env exp typ2 in
          MCL_aux (MCL_forwards (typed_mpexp, typed_exp), (def_annot, mk_expected_tannot env typ (Some typ)))
        end
      | MCL_backwards (mpexp, exp) -> begin
          let mpat, _, _ = destruct_mpexp mpexp in
          ignore (check_pattern_duplicates env (pat_of_mpat mpat));
          let _, mpat_env, _ = bind_mpat false Env.empty env mpat typ2 in
          let typed_mpexp = check_mpexp Env.empty env mpexp typ2 in
          let typed_exp = check_exp mpat_env exp typ1 in
          MCL_aux (MCL_backwards (typed_mpexp, typed_exp), (def_annot, mk_expected_tannot env typ (Some typ)))
        end
    end
  | _ ->
      typ_error def_annot.loc ("Mapping clause must have mapping type: " ^ string_of_typ typ ^ " is not a mapping type")

let infer_funtyp l env tannotopt funcls =
  match tannotopt with
  | Typ_annot_opt_aux (Typ_annot_opt_some (quant, ret_typ), _) -> begin
      let rec typ_from_pat (P_aux (pat_aux, (l, _)) as pat) =
        match pat_aux with
        | P_lit lit -> infer_lit env lit
        | P_typ (typ, _) -> typ
        | P_tuple pats -> mk_typ (Typ_tuple (List.map typ_from_pat pats))
        | _ -> typ_error l ("Cannot infer type from pattern " ^ string_of_pat pat)
      in
      match funcls with
      | [FCL_aux (FCL_funcl (_, Pat_aux (pexp, _)), _)] ->
          let pat = match pexp with Pat_exp (pat, _) | Pat_when (pat, _, _) -> pat in
          (* The function syntax lets us bind multiple function
             arguments with a single pattern, hence why we need to do
             this. But perhaps we don't want to allow this? *)
          let arg_typs =
            match typ_from_pat pat with Typ_aux (Typ_tuple arg_typs, _) -> arg_typs | arg_typ -> [arg_typ]
          in
          let fn_typ = mk_typ (Typ_fn (arg_typs, ret_typ)) in
          wf_binding l env (quant, fn_typ);
          (quant, fn_typ)
      | _ -> typ_error l "Cannot infer function type for function with multiple clauses"
    end
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> typ_error l "Cannot infer function type for unannotated function"

(* This is used for functions and mappings that do not have an explicit type signature using val *)
let synthesize_val_spec env typq typ id =
  mk_def
    (DEF_val
       (VS_aux
          ( VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), Parse_ast.Unknown), id, None),
            (Parse_ast.Unknown, mk_tannot env typ)
          )
       )
    )

let check_tannotopt env typq ret_typ = function
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> ()
  | Typ_annot_opt_aux (Typ_annot_opt_some (annot_typq, annot_ret_typ), l) ->
      if expanded_typ_identical env ret_typ annot_ret_typ then ()
      else
        typ_error l
          (string_of_bind (typq, ret_typ)
          ^ " and "
          ^ string_of_bind (annot_typq, annot_ret_typ)
          ^ " do not match between function and val spec"
          )

let check_termination_measure env arg_typs pat exp =
  let typ = match arg_typs with [x] -> x | _ -> Typ_aux (Typ_tuple arg_typs, Unknown) in
  let tpat, env = bind_pat_no_guard env pat typ in
  let texp = check_exp env exp int_typ in
  (tpat, texp)

let check_termination_measure_decl env def_annot (id, pat, exp) =
  let quant, typ = Env.get_val_spec id env in
  let arg_typs, l =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, _), l) -> (arg_typs, l)
    | _ -> typ_error (id_loc id) "Function val spec is not a function type"
  in
  let env = Env.add_typquant l quant env in
  let tpat, texp = check_termination_measure env arg_typs pat exp in
  DEF_aux (DEF_measure (id, tpat, texp), def_annot)

let check_funcls_complete l env funcls typ =
  let typ_arg, _, env = bind_funcl_arg_typ l env typ in
  let ctx = pattern_completeness_ctx env in
  match PC.is_complete_funcls_wildcarded ~keyword:"function" l ctx funcls typ_arg with
  | Some funcls -> (funcls, add_def_attribute (gen_loc l) "complete" "")
  | None -> (funcls, add_def_attribute (gen_loc l) "incomplete" "")

let check_fundef env def_annot (FD_aux (FD_function (recopt, tannotopt, funcls), (l, _))) =
  let id =
    match
      List.fold_right
        (fun (FCL_aux (FCL_funcl (id, _), _)) id' ->
          match id' with
          | Some id' ->
              if string_of_id id' = string_of_id id then Some id'
              else
                typ_error l
                  ("Function declaration expects all definitions to have the same name, " ^ string_of_id id
                 ^ " differs from other definitions of " ^ string_of_id id'
                  )
          | None -> Some id
        )
        funcls None
    with
    | Some id -> id
    | None -> typ_error l "funcl list is empty"
  in
  typ_print (lazy ("\n" ^ Util.("Check function " |> cyan |> clear) ^ string_of_id id));
  let have_val_spec, (quant, typ), env =
    try (true, Env.get_val_spec id env, env)
    with Type_error (l, _) ->
      let quant, typ = infer_funtyp l env tannotopt funcls in
      (false, (quant, typ), env)
  in
  let vtyp_args, vtyp_ret, vl =
    match typ with
    | Typ_aux (Typ_fn (vtyp_args, vtyp_ret), vl) -> (vtyp_args, vtyp_ret, vl)
    | _ -> typ_error l "Function val spec is not a function type"
  in
  check_tannotopt env quant vtyp_ret tannotopt;
  typ_debug (lazy ("Checking fundef " ^ string_of_id id ^ " has type " ^ string_of_bind (quant, typ)));
  let funcl_env = Env.add_typquant l quant env in
  let recopt =
    match recopt with
    | Rec_aux (Rec_nonrec, l) -> Rec_aux (Rec_nonrec, l)
    | Rec_aux (Rec_rec, l) -> Rec_aux (Rec_rec, l)
    | Rec_aux (Rec_measure (measure_p, measure_e), l) ->
        let tpat, texp = check_termination_measure funcl_env vtyp_args measure_p measure_e in
        Rec_aux (Rec_measure (tpat, texp), l)
  in
  let vs_def, env =
    if not have_val_spec then (
      let typ = Typ_aux (Typ_fn (vtyp_args, vtyp_ret), vl) in
      ([synthesize_val_spec env quant typ id], Env.add_val_spec id (quant, typ) env)
    )
    else ([], env)
  in
  let funcls = List.map (fun funcl -> check_funcl funcl_env funcl typ) funcls in
  let funcls, update_attr =
    if
      Option.is_some (get_def_attribute "complete" def_annot)
      || Option.is_some (get_def_attribute "incomplete" def_annot)
    then (funcls, fun attrs -> attrs)
    else check_funcls_complete l funcl_env funcls typ
  in
  let env = Env.define_val_spec id env in
  ( vs_def
    @ [
        DEF_aux (DEF_fundef (FD_aux (FD_function (recopt, tannotopt, funcls), (l, empty_tannot))), update_attr def_annot);
      ],
    env
  )

let check_mapdef env def_annot (MD_aux (MD_mapping (id, tannot_opt, mapcls), (l, _))) =
  typ_print (lazy ("\nChecking mapping " ^ string_of_id id));
  let have_val_spec, (quant, typ), env =
    try (true, Env.get_val_spec id env, env)
    with Type_error (_, _) as err -> (
      match tannot_opt with
      | Typ_annot_opt_aux (Typ_annot_opt_some (quant, typ), _) -> (false, (quant, typ), env)
      | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> raise err
    )
  in
  begin
    match typ with Typ_aux (Typ_bidir (_, _), _) -> () | _ -> typ_error l "Mapping val spec was not a mapping type"
  end;
  begin
    match tannot_opt with
    | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> ()
    | Typ_annot_opt_aux (Typ_annot_opt_some (annot_typq, annot_typ), l) ->
        if expanded_typ_identical env typ annot_typ then ()
        else
          typ_error l
            (string_of_bind (quant, typ)
            ^ " and "
            ^ string_of_bind (annot_typq, annot_typ)
            ^ " do not match between mapping and val spec"
            )
  end;
  typ_debug (lazy ("Checking mapdef " ^ string_of_id id ^ " has type " ^ string_of_bind (quant, typ)));
  let vs_def, env =
    if not have_val_spec then
      ([synthesize_val_spec env quant (Env.expand_synonyms env typ) id], Env.add_val_spec id (quant, typ) env)
    else ([], env)
  in
  let mapcl_env = Env.add_typquant l quant env in
  let mapcls = List.map (fun mapcl -> check_mapcl mapcl_env mapcl typ) mapcls in
  let env = Env.define_val_spec id env in
  (vs_def @ [DEF_aux (DEF_mapdef (MD_aux (MD_mapping (id, tannot_opt, mapcls), (l, empty_tannot))), def_annot)], env)

(* Checking a val spec simply adds the type as a binding in the context. *)
let check_val_spec env def_annot (VS_aux (vs, (l, _))) =
  let annotate vs typq typ =
    DEF_aux (DEF_val (VS_aux (vs, (l, mk_tannot (Env.add_typquant l typq env) typ))), def_annot)
  in
  let vs, id, typq, typ, env =
    match vs with
    | VS_val_spec ((TypSchm_aux (TypSchm_ts (typq, typ), ts_l) as typschm), id, exts) ->
        typ_print
          (lazy (Util.("Check val spec " |> cyan |> clear) ^ string_of_id id ^ " : " ^ string_of_typschm typschm));
        wf_typschm env typschm;
        let env = match exts with Some exts -> Env.add_extern id exts env | None -> env in
        let typq', typ' = expand_bind_synonyms ts_l env (typq, typ) in
        (* !opt_expand_valspec controls whether the actual valspec in
           the AST is expanded, the val_spec type stored in the
           environment is always expanded and uses typq' and typ' *)
        let typq, typ = if !opt_expand_valspec then (typq', typ') else (typq, typ) in
        let vs = VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), ts_l), id, exts) in
        (vs, id, typq', typ', env)
  in
  ([annotate vs typq typ], Env.add_val_spec id (typq, typ) env)

let check_default env def_annot (DT_aux (DT_order order, l)) =
  ([DEF_aux (DEF_default (DT_aux (DT_order order, l)), def_annot)], Env.set_default_order order env)

let kinded_id_arg kind_id =
  let typ_arg l arg = A_aux (arg, l) in
  match kind_id with
  | KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _) -> typ_arg (kid_loc kid) (A_nexp (nvar kid))
  | KOpt_aux (KOpt_kind (K_aux (K_type, _), kid), _) -> typ_arg (kid_loc kid) (A_typ (mk_typ (Typ_var kid)))
  | KOpt_aux (KOpt_kind (K_aux (K_bool, _), kid), _) -> typ_arg (kid_loc kid) (A_bool (nc_var kid))

let fold_union_quant quants (QI_aux (qi, _)) =
  match qi with QI_id kind_id -> quants @ [kinded_id_arg kind_id] | _ -> quants

(* We wrap this around wf_binding checks that aim to forbid recursive
   types to explain any error messages raised if the well-formedness
   check fails. *)
let forbid_recursive_types type_l f =
  try f ()
  with Type_error (l, err) ->
    let msg = "Types are not well-formed within this type definition. Note that recursive types are forbidden." in
    raise (Type_error (type_l, err_because (Err_other msg, l, err)))

let check_type_union u_l non_rec_env env variant typq (Tu_aux (Tu_ty_id (arg_typ, v), def_annot)) =
  let ret_typ = app_typ variant (List.fold_left fold_union_quant [] (quant_items typq)) in
  let typ = mk_typ (Typ_fn ([arg_typ], ret_typ)) in
  forbid_recursive_types u_l (fun () -> wf_binding def_annot.loc non_rec_env (typq, arg_typ));
  wf_binding def_annot.loc env (typq, typ);
  env |> Env.add_union_id v (typq, typ) |> Env.add_val_spec v (typq, typ)

let check_record l env def_annot id typq fields =
  forbid_recursive_types l (fun () ->
      List.iter (fun ((Typ_aux (_, l) as field), _) -> wf_binding l env (typq, field)) fields
  );
  let env =
    try
      match get_def_attribute "bitfield" def_annot with
      | Some (_, size) when not (Env.is_bitfield id env) ->
          Env.add_bitfield id (bits_typ env (nconstant (Big_int.of_string size))) Bindings.empty env
      | _ -> env
    with _ -> env
  in
  Env.add_record id typq fields env

let rec check_typedef : Env.t -> def_annot -> uannot type_def -> tannot def list * Env.t =
 fun env def_annot (TD_aux (tdef, (l, _))) ->
  match tdef with
  | TD_abbrev (id, typq, typ_arg) ->
      begin
        match typ_arg with
        | A_aux (A_typ typ, a_l) -> forbid_recursive_types l (fun () -> wf_binding a_l env (typq, typ))
        | _ -> ()
      end;
      ([DEF_aux (DEF_type (TD_aux (tdef, (l, empty_tannot))), def_annot)], Env.add_typ_synonym id typq typ_arg env)
  | TD_record (id, typq, fields, _) ->
      let env = check_record l env def_annot id typq fields in
      ([DEF_aux (DEF_type (TD_aux (tdef, (l, empty_tannot))), def_annot)], env)
  | TD_variant (id, typq, arms, _) ->
      let rec_env = Env.add_variant id (typq, arms) env in
      (* register_value is a special type used by theorem prover
         backends that we allow to be recursive. *)
      let non_rec_env = if string_of_id id = "register_value" then rec_env else env in
      let env =
        rec_env |> fun env -> List.fold_left (fun env tu -> check_type_union l non_rec_env env id typq tu) env arms
      in
      ([DEF_aux (DEF_type (TD_aux (tdef, (l, empty_tannot))), def_annot)], env)
  | TD_enum (id, ids, _) -> ([DEF_aux (DEF_type (TD_aux (tdef, (l, empty_tannot))), def_annot)], Env.add_enum id ids env)
  | TD_bitfield (id, typ, ranges) as unexpanded ->
      let typ = Env.expand_synonyms env typ in
      begin
        match typ with
        (* The type of a bitfield must be a constant-width bitvector *)
        | Typ_aux (Typ_app (v, [A_aux (A_nexp (Nexp_aux (Nexp_constant size, _)), _)]), _)
          when string_of_id v = "bitvector" ->
            let rec expand_range_synonyms = function
              | BF_aux (BF_single nexp, l) -> BF_aux (BF_single (Env.expand_nexp_synonyms env nexp), l)
              | BF_aux (BF_range (nexp1, nexp2), l) ->
                  let nexp1 = Env.expand_nexp_synonyms env nexp1 in
                  let nexp2 = Env.expand_nexp_synonyms env nexp2 in
                  BF_aux (BF_range (nexp1, nexp2), l)
              | BF_aux (BF_concat (r1, r2), l) ->
                  BF_aux (BF_concat (expand_range_synonyms r1, expand_range_synonyms r2), l)
            in
            let record_tdef = TD_record (id, mk_typquant [], [(typ, mk_id "bits")], false) in
            let ranges =
              List.map (fun (f, r) -> (f, expand_range_synonyms r)) ranges |> List.to_seq |> Bindings.of_seq
            in
            let def_annot = add_def_attribute l "bitfield" (Big_int.to_string size) def_annot in
            let defs =
              DEF_aux (DEF_type (TD_aux (record_tdef, (l, empty_uannot))), def_annot)
              :: Bitfield.macro id size (Env.get_default_order env) ranges
            in
            let defs =
              if !Initial_check.opt_undefined_gen then Initial_check.generate_undefineds IdSet.empty defs else defs
            in
            let defs, env = check_defs env defs in
            let env = Env.add_bitfield id typ ranges env in
            if !opt_no_bitfield_expansion then
              ([DEF_aux (DEF_type (TD_aux (unexpanded, (l, empty_tannot))), def_annot)], env)
            else (defs, env)
        | _ -> typ_error l "Underlying bitfield type must be a constant-width bitvector"
      end

and check_scattered : Env.t -> def_annot -> uannot scattered_def -> tannot def list * Env.t =
 fun env def_annot (SD_aux (sdef, (l, uannot))) ->
  match sdef with
  | SD_function _ | SD_end _ | SD_mapping _ -> ([], env)
  | SD_enum id ->
      ([DEF_aux (DEF_scattered (SD_aux (SD_enum id, (l, empty_tannot))), def_annot)], Env.add_scattered_enum id env)
  | SD_enumcl (id, member) ->
      ( [DEF_aux (DEF_scattered (SD_aux (SD_enumcl (id, member), (l, empty_tannot))), def_annot)],
        Env.add_enum_clause id member env
      )
  | SD_variant (id, typq) ->
      ( [DEF_aux (DEF_scattered (SD_aux (SD_variant (id, typq), (l, empty_tannot))), def_annot)],
        Env.add_scattered_variant id typq env
      )
  | SD_unioncl (id, tu) ->
      ( [DEF_aux (DEF_scattered (SD_aux (SD_unioncl (id, tu), (l, empty_tannot))), def_annot)],
        let env = Env.add_variant_clause id tu env in
        let typq, _ = Env.get_variant id env in
        let definition_env = Env.get_scattered_variant_env id env in
        try check_type_union l definition_env env id typq tu
        with Type_error (l', err) ->
          let msg =
            "As this is a scattered union clause, this could also be caused by using a type defined after the \
             'scattered union' declaration"
          in
          raise (Type_error (l', err_because (err, id_loc id, Err_other msg)))
      )
  | SD_internal_unioncl_record (id, record_id, typq, fields) ->
      let definition_env = Env.get_scattered_variant_env id env in
      let definition_env = check_record l definition_env def_annot record_id typq fields in
      let env = Env.set_scattered_variant_env ~variant_env:definition_env id env in
      let env = Env.add_record record_id typq fields env in
      ( [
          DEF_aux
            ( DEF_scattered (SD_aux (SD_internal_unioncl_record (id, record_id, typq, fields), (l, empty_tannot))),
              def_annot
            );
        ],
        env
      )
  | SD_funcl (FCL_aux (FCL_funcl (id, _), (fcl_def_annot, _)) as funcl) ->
      let typq, typ = Env.get_val_spec id env in
      let funcl_env = Env.add_typquant fcl_def_annot.loc typq env in
      let funcl = check_funcl funcl_env funcl typ in
      ([DEF_aux (DEF_scattered (SD_aux (SD_funcl funcl, (l, mk_tannot ~uannot funcl_env typ))), def_annot)], env)
  | SD_mapcl (id, mapcl) ->
      let typq, typ = Env.get_val_spec id env in
      let mapcl_env = Env.add_typquant l typq env in
      let mapcl = check_mapcl mapcl_env mapcl typ in
      ([DEF_aux (DEF_scattered (SD_aux (SD_mapcl (id, mapcl), (l, empty_tannot))), def_annot)], env)

and check_outcome : Env.t -> outcome_spec -> uannot def list -> outcome_spec * tannot def list * Env.t =
 fun env (OV_aux (OV_outcome (id, typschm, params), l)) defs ->
  let valid_outcome_def = function
    | DEF_aux ((DEF_impl _ | DEF_val _), _) -> ()
    | def -> typ_error (def_loc def) "Forbidden definition in outcome block"
  in
  typ_print (lazy (Util.("Check outcome " |> cyan |> clear) ^ string_of_id id ^ " : " ^ string_of_typschm typschm));
  match Env.is_toplevel env with
  | None -> begin
      incr depth;
      try
        let local_env = add_typ_vars l params env in
        wf_typschm local_env typschm;
        let quant, typ = match typschm with TypSchm_aux (TypSchm_ts (typq, typ), _) -> (typq, typ) in
        let local_env = Env.set_outcome_typschm ~outcome_loc:l (quant, typ) local_env in
        List.iter valid_outcome_def defs;
        let defs, local_env = check_defs local_env defs in
        let vals =
          List.filter_map
            (function DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, _), _)), _) -> Some id | _ -> None)
            defs
        in
        decr depth;
        ( OV_aux (OV_outcome (id, typschm, params), l),
          defs,
          Env.add_outcome id (quant, typ, params, vals, local_env) env
        )
      with Type_error (err_l, err) ->
        decr depth;
        typ_raise err_l err
    end
  | Some outer_l ->
      let msg = "Outcome must be declared within top-level scope" in
      typ_raise l (err_because (Err_other msg, outer_l, Err_other "Containing scope declared here"))

and check_impldef : Env.t -> def_annot -> uannot funcl -> tannot def list * Env.t =
 fun env def_annot (FCL_aux (FCL_funcl (id, _), (fcl_def_annot, _)) as funcl) ->
  typ_print (lazy (Util.("Check impl " |> cyan |> clear) ^ string_of_id id));
  match Env.get_outcome_typschm_opt env with
  | Some (quant, typ) ->
      let funcl_env = Env.add_typquant fcl_def_annot.loc quant env in
      ([DEF_aux (DEF_impl (check_funcl funcl_env funcl typ), def_annot)], env)
  | None -> typ_error fcl_def_annot.loc "Cannot declare an implementation outside of an outcome"

and check_outcome_instantiation :
      'a. Env.t -> def_annot -> 'a instantiation_spec -> subst list -> tannot def list * Env.t =
 fun env def_annot (IN_aux (IN_id id, (l, _))) substs ->
  typ_print (lazy (Util.("Check instantiation " |> cyan |> clear) ^ string_of_id id));
  let typq, typ, params, vals, outcome_env = Env.get_outcome l id env in
  (* Find the outcome parameters that were already instantiated by previous instantiation commands *)
  let instantiated, uninstantiated =
    Util.map_split
      (fun kopt ->
        match KBindings.find_opt (kopt_kid kopt) (Env.get_outcome_instantiation env) with
        | Some (prev_l, existing_typ) -> Ok (kopt_kid kopt, (prev_l, kopt_kind kopt, existing_typ))
        | None -> Error kopt
      )
      params
  in
  let instantiated = List.fold_left (fun m (kid, inst) -> KBindings.add kid inst m) KBindings.empty instantiated in

  (* Instantiate the outcome type with these existing parameters *)
  let typ =
    List.fold_left
      (fun typ (kid, (_, _, existing_typ)) -> typ_subst kid (mk_typ_arg (A_typ existing_typ)) typ)
      typ (KBindings.bindings instantiated)
  in

  let instantiate_typ substs typ =
    List.fold_left
      (fun (typ, new_instantiated, fns, env) -> function
        | IS_aux (IS_typ (kid, subst_typ), decl_l) -> begin
            match KBindings.find_opt kid instantiated with
            | Some (_, _, existing_typ) when alpha_equivalent env subst_typ existing_typ ->
                (typ, new_instantiated, fns, env)
            | Some (prev_l, _, existing_typ) ->
                let msg =
                  Printf.sprintf "Cannot instantiate %s with %s, already instantiated as %s" (string_of_kid kid)
                    (string_of_typ subst_typ) (string_of_typ existing_typ)
                in
                typ_raise decl_l (err_because (Err_other msg, prev_l, Err_other "Previously instantiated here"))
            | None ->
                Env.wf_typ env subst_typ;
                ( typ_subst kid (mk_typ_arg (A_typ subst_typ)) typ,
                  (kid, subst_typ) :: new_instantiated,
                  fns,
                  Env.add_outcome_variable decl_l kid subst_typ env
                )
          end
        | IS_aux (IS_id (id_from, id_to), decl_l) -> (typ, new_instantiated, (id_from, id_to, decl_l) :: fns, env)
      )
      (typ, [], [], env) substs
  in
  let typ, new_instantiated, fns, env = instantiate_typ substs typ in

  (* Make sure every required outcome parameter has been instantiated *)
  List.iter
    (fun kopt ->
      if not (List.exists (fun (v, _) -> Kid.compare (kopt_kid kopt) v = 0) new_instantiated) then
        typ_error l ("Type variable " ^ string_of_kinded_id kopt ^ " must be instantiated")
    )
    uninstantiated;

  begin
    match List.find_opt (fun id -> not (List.exists (fun (id_from, _, _) -> Id.compare id id_from = 0) fns)) vals with
    | Some val_id -> typ_error l ("Function " ^ string_of_id val_id ^ " must be instantiated for " ^ string_of_id id)
    | None -> ()
  end;

  List.iter
    (fun (id_from, id_to, decl_l) ->
      let to_typq, to_typ = Env.get_val_spec id_to env in
      let from_typq, from_typ = Env.get_val_spec_orig id_from outcome_env in
      typ_debug (lazy (string_of_bind (to_typq, to_typ)));

      let from_typ =
        List.fold_left
          (fun typ (v, subst_typ) -> typ_subst v (mk_typ_arg (A_typ subst_typ)) typ)
          from_typ new_instantiated
      in
      let from_typ =
        List.fold_left
          (fun typ (v, (_, _, subst_typ)) -> typ_subst v (mk_typ_arg (A_typ subst_typ)) typ)
          from_typ (KBindings.bindings instantiated)
      in

      check_function_instantiation decl_l id_from env (to_typq, to_typ) (from_typq, from_typ)
    )
    fns;

  ( [DEF_aux (DEF_instantiation (IN_aux (IN_id id, (l, mk_tannot env unit_typ)), substs), def_annot)],
    Env.add_val_spec id (typq, typ) env
  )

and check_def : Env.t -> uannot def -> tannot def list * Env.t =
 fun env (DEF_aux (aux, def_annot)) ->
  match aux with
  | DEF_fixity (prec, n, op) -> ([DEF_aux (DEF_fixity (prec, n, op), def_annot)], env)
  | DEF_type tdef -> check_typedef env def_annot tdef
  | DEF_fundef fdef -> check_fundef env def_annot fdef
  | DEF_mapdef mdef -> check_mapdef env def_annot mdef
  | DEF_impl funcl -> check_impldef env def_annot funcl
  | DEF_internal_mutrec fdefs ->
      let defs = List.concat (List.map (fun fdef -> fst (check_fundef env def_annot fdef)) fdefs) in
      let split_fundef (defs, fdefs) def =
        match def with DEF_aux (DEF_fundef fdef, _) -> (defs, fdefs @ [fdef]) | _ -> (defs @ [def], fdefs)
      in
      let defs, fdefs = List.fold_left split_fundef ([], []) defs in
      (defs @ [DEF_aux (DEF_internal_mutrec fdefs, def_annot)], env)
  | DEF_let letdef -> check_letdef env def_annot letdef
  | DEF_val vs -> check_val_spec env def_annot vs
  | DEF_outcome (outcome, defs) ->
      let outcome, defs, env = check_outcome env outcome defs in
      ([DEF_aux (DEF_outcome (outcome, defs), def_annot)], env)
  | DEF_instantiation (ispec, substs) -> check_outcome_instantiation env def_annot ispec substs
  | DEF_default default -> check_default env def_annot default
  | DEF_overload (id, ids) -> ([DEF_aux (DEF_overload (id, ids), def_annot)], Env.add_overloads def_annot.loc id ids env)
  | DEF_register (DEC_aux (DEC_reg (typ, id, None), (l, _))) ->
      let env = Env.add_register id typ env in
      ( [
          DEF_aux
            (DEF_register (DEC_aux (DEC_reg (typ, id, None), (l, mk_expected_tannot env typ (Some typ)))), def_annot);
        ],
        env
      )
  | DEF_register (DEC_aux (DEC_reg (typ, id, Some exp), (l, _))) ->
      let checked_exp = crule check_exp env exp typ in
      let env = Env.add_register id typ env in
      ( [
          DEF_aux
            ( DEF_register (DEC_aux (DEC_reg (typ, id, Some checked_exp), (l, mk_expected_tannot env typ (Some typ)))),
              def_annot
            );
        ],
        env
      )
  | DEF_pragma (pragma, arg, l) -> ([DEF_aux (DEF_pragma (pragma, arg, l), def_annot)], env)
  | DEF_scattered sdef -> check_scattered env def_annot sdef
  | DEF_measure (id, pat, exp) -> ([check_termination_measure_decl env def_annot (id, pat, exp)], env)
  | DEF_loop_measures (id, _) ->
      Reporting.unreachable (id_loc id) __POS__
        "Loop termination measures should have been rewritten before type checking"

and check_defs_progress : int -> int -> Env.t -> uannot def list -> tannot def list * Env.t =
 fun n total env defs ->
  let rec aux n total acc env defs =
    match defs with
    | [] -> (List.rev acc, env)
    | def :: defs ->
        Util.progress "Type check " (string_of_int n ^ "/" ^ string_of_int total) n total;
        let def, env = check_def env def in
        aux (n + 1) total (List.rev def @ acc) env defs
  in
  aux n total [] env defs

and check_defs : Env.t -> uannot def list -> tannot def list * Env.t =
 fun env defs ->
  let total = List.length defs in
  check_defs_progress 1 total env defs

let check : Env.t -> uannot ast -> tannot ast * Env.t =
 fun env ast ->
  let total = List.length ast.defs in
  let defs, env = check_defs_progress 1 total env ast.defs in
  ({ ast with defs }, env)

let rec check_with_envs : Env.t -> uannot def list -> (tannot def list * Env.t) list =
 fun env defs ->
  match defs with
  | [] -> []
  | def :: defs ->
      let def, env = check_def env def in
      (def, env) :: check_with_envs env defs

let initial_env =
  Env.empty
  |> Env.set_prover (Some (prove __POS__))
  |> Env.add_extern (mk_id "size_itself_int") { pure = true; bindings = [("_", "size_itself_int")] }
  |> Env.add_val_spec (mk_id "size_itself_int")
       ( TypQ_aux (TypQ_tq [QI_aux (QI_id (mk_kopt K_int (mk_kid "n")), Parse_ast.Unknown)], Parse_ast.Unknown),
         function_typ [app_typ (mk_id "itself") [mk_typ_arg (A_nexp (nvar (mk_kid "n")))]] (atom_typ (nvar (mk_kid "n")))
       )
  |> Env.add_extern (mk_id "make_the_value") { pure = true; bindings = [("_", "make_the_value")] }
  |> Env.add_val_spec (mk_id "make_the_value")
       ( TypQ_aux (TypQ_tq [QI_aux (QI_id (mk_kopt K_int (mk_kid "n")), Parse_ast.Unknown)], Parse_ast.Unknown),
         function_typ [atom_typ (nvar (mk_kid "n"))] (app_typ (mk_id "itself") [mk_typ_arg (A_nexp (nvar (mk_kid "n")))])
       )
  (* __assume is used by property.ml to add guards for SMT generation,
     but which don't affect flow-typing. *)
  |> Env.add_val_spec (mk_id "sail_assume")
       (TypQ_aux (TypQ_no_forall, Parse_ast.Unknown), function_typ [bool_typ] unit_typ)
