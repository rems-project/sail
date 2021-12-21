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

open Type_check
open Ast
open Ast_defs
open Ast_util
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

module StringSet = Set.Make(String)

let rec list_contains cmp l1 = function
  | [] -> Some l1
  | h::t ->
     let rec remove = function
       | [] -> None
       | h'::t' -> if cmp h h' = 0 then Some t'
                   else Util.option_map (List.cons h') (remove t')
     in Util.option_bind (fun l1' -> list_contains cmp l1' t) (remove l1)

let opt_undef_axioms = ref false
let opt_debug_on : string list ref = ref []

(****************************************************************************
 * PPrint-based sail-to-coq pprinter
****************************************************************************)

(* Data representation:
 *
 * In pure computations we keep values with top level existential types
 * (including ranges and nats) separate from the proofs of the accompanying
 * constraints, which keeps the terms shorter and more manageable.
 * Existentials embedded in types (e.g., in tuples or datatypes) are dependent
 * pairs.
 *
 * Monadic values always includes the proof in a dependent pair because the
 * constraint solving tactic won't see the term that defined the value, and
 * must rely entirely on the type (like the Sail type checker).
 *)


type context = {
  types_mod : string; (* Name of the types module for disambiguation *)
  early_ret : bool;
  kid_renames : kid KBindings.t; (* Plain tyvar -> tyvar renames,
                                    used to avoid variable/type variable name clashes *)
  (* Note that as well as these kid renames, we also attempt to replace entire
     n_constraints with equivalent variables in doc_nc_exp. *)
  kid_id_renames : (id option) KBindings.t; (* tyvar -> argument renames *)
  kid_id_renames_rev : kid Bindings.t; (* reverse of kid_id_renames *)
  bound_nvars : KidSet.t;
  build_at_return : string option;
  recursive_fns : (int * int) Bindings.t; (* Number of implicit arguments and constraints for (mutually) recursive definitions *)
  debug : bool;
  ret_typ_pp : PPrint.document; (* Return type formatted for use with returnR *)
}
let empty_ctxt = {
  types_mod = "";
  early_ret = false;
  kid_renames = KBindings.empty;
  kid_id_renames = KBindings.empty;
  kid_id_renames_rev = Bindings.empty;
  bound_nvars = KidSet.empty;
  build_at_return = None;
  recursive_fns = Bindings.empty;
  debug = false;
  ret_typ_pp = PPrint.empty;
}

let add_single_kid_id_rename ctxt id kid =
  let kir =
    match Bindings.find_opt id ctxt.kid_id_renames_rev with
    | Some kid -> KBindings.add kid None ctxt.kid_id_renames
    | None -> ctxt.kid_id_renames
  in
  { ctxt with
      kid_id_renames = KBindings.add kid (Some id) kir;
      kid_id_renames_rev = Bindings.add id kid ctxt.kid_id_renames_rev
    }

let debug_depth = ref 0

let rec indent n = match n with
  | 0 -> ""
  | n -> "|   " ^ indent (n - 1)

let debug ctxt m =
  if ctxt.debug
  then print_endline (indent !debug_depth ^ Lazy.force m)
  else ()

let langlebar = string "<|"
let ranglebar = string "|>"
let anglebars = enclose langlebar ranglebar
let enclose_record = enclose (string "{| ") (string " |}")
let enclose_record_update = enclose (string "{[ ") (string " ]}")
let bigarrow = string "=>"

let separate_opt s f l = separate s (Util.map_filter f l)

let is_number_char c =
  c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5' ||
  c = '6' || c = '7' || c = '8' || c = '9'

let is_enum env id =
  match Env.lookup_id id env with
  | Enum _ -> true
  | _ -> false

let rec fix_id remove_tick name = match name with
  | "assert"
  | "lsl"
  | "lsr"
  | "asr"
  | "type"
  | "fun"
  | "function"
  | "raise"
  | "try"
  | "match"
  | "with"
  | "check"
  | "field"
  | "LT"
  | "GT"
  | "EQ"
  | "Z"
  | "O"
  | "R"
  | "S"
  | "mod"
  | "M"
  | "tt"
    -> name ^ "'"
  | _ ->
     if String.contains name '#' then
       fix_id remove_tick (String.concat "_" (Util.split_on_char '#' name))
     else if String.contains name '?' then
       fix_id remove_tick (String.concat "_pat_" (Util.split_on_char '?' name))
     else if String.contains name '^' then
       fix_id remove_tick (String.concat "__" (Util.split_on_char '^' name))
     else if name.[0] = '\'' then
       let var = String.sub name 1 (String.length name - 1) in
       if remove_tick then fix_id remove_tick var else (var ^ "'")
     else if is_number_char(name.[0]) then
       ("v" ^ name ^ "'")
     else name

let string_id (Id_aux(i,_)) =
  match i with
  | Id i -> fix_id false i
  | Operator x -> Util.zencode_string ("op " ^ x)

let doc_id id = string (string_id id)

let doc_id_type types_mod env (Id_aux(i,_) as id) =
  let is_shadowed () =
    match env with
    | None -> false
    | Some env ->
       IdSet.mem id (Env.get_defined_val_specs env) ||
       Env.lookup_id id env <> Unbound
  in
  match i with
  | Id("int") -> string "Z"
  | Id("real") -> string "R"
  | Id i when is_shadowed () ->
     string types_mod ^^ dot ^^ string (fix_id false i)
  | Id i -> string (fix_id false i)
  | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_id_ctor (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_var ctx kid =
  match KBindings.find kid ctx.kid_id_renames with
  | Some id -> doc_id id
  | None -> underscore (* The original id has been shadowed, hope Coq can work it out...  TODO: warn? *)
  | exception Not_found ->
     string (fix_id true (string_of_kid (try KBindings.find kid ctx.kid_renames with Not_found -> kid)))

let doc_docstring (l, _) = match l with
  | Parse_ast.Documented (str, _) -> string ("(*" ^ str ^ "*)") ^^ hardline
  | _ -> empty

let simple_annot l typ = (Parse_ast.Generated l, Some (Env.empty, typ, no_effect))
let simple_num l n = E_aux (
  E_lit (L_aux (L_num n, Parse_ast.Generated l)),
  simple_annot (Parse_ast.Generated l)
    (atom_typ (Nexp_aux (Nexp_constant n, Parse_ast.Generated l))))

let effectful_set = function
  | [] -> false
  | _ -> true
  (*List.exists
    (fun (BE_aux (eff,_)) ->
      match eff with
      | BE_rreg | BE_wreg | BE_rmem | BE_rmemt | BE_wmem | BE_eamem
      | BE_exmem | BE_wmv | BE_wmvt | BE_barr | BE_depend | BE_nondet
      | BE_escape -> true
      | _ -> false)*)

let effectful (Effect_aux (Effect_set effs, _)) = effectful_set effs

let is_regtyp (Typ_aux (typ, _)) env = match typ with
  | Typ_app(id, _) when string_of_id id = "register" -> true
  | _ -> false

let doc_nexp ctx ?(skip_vars=KidSet.empty) nexp =
  (* Print according to Coq's precedence rules *)
  let rec plussub (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_sum (n1, n2) -> separate space [plussub n1; plus; mul n2]
    | Nexp_minus (n1, n2) -> separate space [plussub n1; minus; mul n2]
    | _ -> mul nexp
  and mul (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_times (n1, n2) -> separate space [mul n1; star; uneg n2]
    | _ -> uneg nexp
  and uneg (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_neg n -> separate space [minus; uneg n]
    | _ -> exp nexp
  and exp (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_exp n -> separate space [string "2"; caret; exp n]
    | _ -> app nexp
  and app (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_app (Id_aux (Id "div",_), [n1;n2])
        -> separate space [string "ZEuclid.div"; atomic n1; atomic n2]
    | Nexp_app (Id_aux (Id "mod",_), [n1;n2])
        -> separate space [string "ZEuclid.modulo"; atomic n1; atomic n2]
    | Nexp_app (Id_aux (Id "abs_atom",_), [n1])
        -> separate space [string "Z.abs"; atomic n1]
    | _ -> atomic nexp
  and atomic (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_constant i -> string (Big_int.to_string i)
    | Nexp_var v when KidSet.mem v skip_vars -> string "_"
    | Nexp_var v -> doc_var ctx v
    | Nexp_id id -> doc_id id
    | Nexp_sum _ | Nexp_minus _ | Nexp_times _ | Nexp_neg _ | Nexp_exp _
    | Nexp_app (Id_aux (Id ("div"|"mod"),_), [_;_])
    | Nexp_app (Id_aux (Id "abs_atom",_), [_])
        -> parens (plussub nexp)
    | _ ->
       raise (Reporting.err_unreachable l __POS__
                ("cannot pretty-print nexp \"" ^ string_of_nexp nexp ^ "\""))
  in atomic nexp

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

let rec orig_nc (NC_aux (nc, l) as full_nc) =
  let rewrap nc = NC_aux (nc, l) in
  match nc with
  | NC_equal (nexp1, nexp2) -> rewrap (NC_equal (orig_nexp nexp1, orig_nexp nexp2))
  | NC_bounded_ge (nexp1, nexp2) -> rewrap (NC_bounded_ge (orig_nexp nexp1, orig_nexp nexp2))
  | NC_bounded_gt (nexp1, nexp2) -> rewrap (NC_bounded_gt (orig_nexp nexp1, orig_nexp nexp2))
  | NC_bounded_le (nexp1, nexp2) -> rewrap (NC_bounded_le (orig_nexp nexp1, orig_nexp nexp2))
  | NC_bounded_lt (nexp1, nexp2) -> rewrap (NC_bounded_lt (orig_nexp nexp1, orig_nexp nexp2))
  | NC_not_equal (nexp1, nexp2) -> rewrap (NC_not_equal (orig_nexp nexp1, orig_nexp nexp2))
  | NC_set (kid,s) -> rewrap (NC_set (orig_kid kid, s))
  | NC_or (nc1, nc2) -> rewrap (NC_or (orig_nc nc1, orig_nc nc2))
  | NC_and (nc1, nc2) -> rewrap (NC_and (orig_nc nc1, orig_nc nc2))
  | NC_app (f,args) -> rewrap (NC_app (f,List.map orig_typ_arg args))
  | NC_var kid -> rewrap (NC_var (orig_kid kid))
  | NC_true | NC_false -> full_nc
and orig_typ_arg (A_aux (arg,l)) =
  let rewrap a = (A_aux (a,l)) in
  match arg with
  | A_nexp nexp -> rewrap (A_nexp (orig_nexp nexp))
  | A_bool nc -> rewrap (A_bool (orig_nc nc))
  | A_order _ | A_typ _ ->
       raise (Reporting.err_unreachable l __POS__ "Tried to pass Type or Order kind to SMT function")

(* Returns the set of type variables that will appear in the Coq output,
   which may be smaller than those in the Sail type.  May need to be
   updated with do *)
let rec coq_nvars_of_typ (Typ_aux (t,l)) =
  let trec = coq_nvars_of_typ in
  match t with
  | Typ_id _ -> KidSet.empty
  | Typ_var kid -> tyvars_of_nexp (orig_nexp (nvar kid))
  | Typ_fn (t1,t2,_) -> List.fold_left KidSet.union (trec t2) (List.map trec t1)
  | Typ_tup ts ->
     List.fold_left (fun s t -> KidSet.union s (trec t))
       KidSet.empty ts
  | Typ_app(Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) ->
     trec etyp
  | Typ_app(Id_aux (Id "implicit", _),_)
  (* TODO: update when complex atom types are sorted out *)
  | Typ_app(Id_aux (Id "atom", _), _) -> KidSet.empty
  | Typ_app(Id_aux (Id "atom_bool", _), _) -> KidSet.empty
  | Typ_app (_,tas) ->
     List.fold_left (fun s ta -> KidSet.union s (coq_nvars_of_typ_arg ta))
       KidSet.empty tas
  (* TODO: remove appropriate bound variables *)
  | Typ_exist (_,_,t) -> trec t
  | Typ_bidir _ -> unreachable l __POS__ "Coq doesn't support bidir types"
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
and coq_nvars_of_typ_arg (A_aux (ta,_)) =
  match ta with
  | A_nexp nexp -> tyvars_of_nexp (orig_nexp nexp)
  | A_typ typ -> coq_nvars_of_typ typ
  | A_order _ -> KidSet.empty
  | A_bool nc -> tyvars_of_constraint (orig_nc nc)

let maybe_expand_range_type (Typ_aux (typ,l) as full_typ) =
  match typ with
  | Typ_app(Id_aux (Id "range", _), [A_aux(A_nexp low,_);
                                     A_aux(A_nexp high,_)]) ->
         (* TODO: avoid name clashes *)
     let kid = mk_kid "rangevar" in
     let var = nvar kid in
     let nc = nc_and (nc_lteq low var) (nc_lteq var high) in
     Some (Typ_aux (Typ_exist ([mk_kopt K_int kid], nc, atom_typ var),Parse_ast.Generated l))
  | Typ_id (Id_aux (Id "nat",_)) ->
     let kid = mk_kid "n" in
     let var = nvar kid in
     Some (Typ_aux (Typ_exist ([mk_kopt K_int kid], nc_gteq var (nconstant Nat_big_num.zero), atom_typ var),
                    Parse_ast.Generated l))
  | _ -> None

let expand_range_type typ = Util.option_default typ (maybe_expand_range_type typ)


let nice_and nc1 nc2 =
match nc1, nc2 with
| NC_aux (NC_true,_), _ -> nc2
| _, NC_aux (NC_true,_) -> nc1
| _,_ -> nc_and nc1 nc2

let nice_iff nc1 nc2 =
match nc1, nc2 with
| NC_aux (NC_true,_), _ -> nc2
| _, NC_aux (NC_true,_) -> nc1
| NC_aux (NC_false,_), _ -> nc_not nc2
| _, NC_aux (NC_false,_) -> nc_not nc1
 (* TODO: replace this hacky iff with a proper NC_ constructor *)
| _,_ -> mk_nc (NC_app (mk_id "iff",[arg_bool nc1; arg_bool nc2]))

(* n_constraint functions are currently just Z3 functions *)
let doc_nc_fn (Id_aux (id,_) as full_id) =
  match id with
  | Id "not" -> string "negb"
  | Operator "-->" -> string "implb"
  | Id "iff" -> string "Bool.eqb"
  | _ -> doc_id full_id

let merge_kid_count = KBindings.union (fun _ m n -> Some (m+n))

let rec count_nexp_vars (Nexp_aux (nexp,_)) =
  match nexp with
  | Nexp_id _
  | Nexp_constant _
    -> KBindings.empty
  | Nexp_var kid -> KBindings.singleton kid 1
  | Nexp_app (_,nes) ->
     List.fold_left merge_kid_count KBindings.empty (List.map count_nexp_vars nes)
  | Nexp_times (n1,n2)
  | Nexp_sum (n1,n2)
  | Nexp_minus (n1,n2)
    -> merge_kid_count (count_nexp_vars n1) (count_nexp_vars n2)
  | Nexp_exp n
  | Nexp_neg n
    -> count_nexp_vars n

let rec count_nc_vars (NC_aux (nc,_)) =
  let count_arg (A_aux (arg,_)) =
    match arg with
    | A_bool nc -> count_nc_vars nc
    | A_nexp nexp -> count_nexp_vars nexp
    | A_typ _ | A_order _ -> KBindings.empty
  in
  match nc with
  | NC_or (nc1,nc2)
  | NC_and (nc1,nc2)
    -> merge_kid_count (count_nc_vars nc1) (count_nc_vars nc2)
  | NC_var kid
  | NC_set (kid,_)
    -> KBindings.singleton kid 1
  | NC_equal (n1,n2)
  | NC_bounded_ge (n1,n2)
  | NC_bounded_gt (n1,n2)
  | NC_bounded_le (n1,n2)
  | NC_bounded_lt (n1,n2)
  | NC_not_equal  (n1,n2)
    -> merge_kid_count (count_nexp_vars n1) (count_nexp_vars n2)
  | NC_true | NC_false
    -> KBindings.empty
  | NC_app (_,args) ->
     List.fold_left merge_kid_count KBindings.empty (List.map count_arg args)

(* Simplify some of the complex boolean types created by the Sail type checker,
   whereever an existentially bound variable is used once in a trivial way,
   for example exists b, b and exists n, n = 32. *)

type atom_bool_prop =
  Bool_boring
| Bool_complex of kinded_id list * n_constraint * n_constraint

let simplify_atom_bool l kopts nc atom_nc =
(*prerr_endline ("simplify " ^ string_of_n_constraint nc ^ " for bool " ^ string_of_n_constraint atom_nc);*)
  let counter = ref 0 in
  let is_bound kid = List.exists (fun kopt -> Kid.compare kid (kopt_kid kopt) == 0) kopts in
  let ty_vars = merge_kid_count (count_nc_vars nc) (count_nc_vars atom_nc) in
  let lin_ty_vars = KBindings.filter (fun kid n -> is_bound kid && n = 1) ty_vars in
  let rec simplify (NC_aux (nc,l) as nc_full) =
    let is_ex_var news (NC_aux (nc,_)) =
      match nc with
      | NC_var kid when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_var kid when KidSet.mem kid news -> Some kid
      | NC_equal (Nexp_aux (Nexp_var kid,_), _) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_equal (_, Nexp_aux (Nexp_var kid,_)) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_ge (Nexp_aux (Nexp_var kid,_), _) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_ge (_, Nexp_aux (Nexp_var kid,_)) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_gt (Nexp_aux (Nexp_var kid,_), _) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_gt (_, Nexp_aux (Nexp_var kid,_)) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_le (Nexp_aux (Nexp_var kid,_), _) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_le (_, Nexp_aux (Nexp_var kid,_)) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_lt (Nexp_aux (Nexp_var kid,_), _) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_bounded_lt (_, Nexp_aux (Nexp_var kid,_)) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_not_equal (Nexp_aux (Nexp_var kid,_), _) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_not_equal (_, Nexp_aux (Nexp_var kid,_)) when KBindings.mem kid lin_ty_vars -> Some kid
      | NC_set (kid, _::_) when KBindings.mem kid lin_ty_vars -> Some kid
      | _ -> None
    in
    let replace kills vars =
      let v = mk_kid ("simp#" ^ string_of_int !counter) in
      let kills = KidSet.union kills (KidSet.of_list vars) in
      counter := !counter + 1;
      KidSet.singleton v, kills, NC_aux (NC_var v,l)
    in
    match nc with
    | NC_or (nc1,nc2) -> begin
       let new1, kill1, nc1 = simplify nc1 in
       let new2, kill2, nc2 = simplify nc2 in
       let news, kills = KidSet.union new1 new2, KidSet.union kill1 kill2 in
       match is_ex_var news nc1, is_ex_var news nc2 with
       | Some kid1, Some kid2 -> replace kills [kid1;kid2]
       | _ -> news, kills, NC_aux (NC_or (nc1,nc2),l)
      end
    | NC_and (nc1,nc2) -> begin
       let new1, kill1, nc1 = simplify nc1 in
       let new2, kill2, nc2 = simplify nc2 in
       let news, kills = KidSet.union new1 new2, KidSet.union kill1 kill2 in
       match is_ex_var news nc1, is_ex_var news nc2 with
       | Some kid1, Some kid2 -> replace kills [kid1;kid2]
       | _ -> news, kills, NC_aux (NC_and (nc1,nc2),l)
      end
    | NC_app (Id_aux (Id "not",_) as id,[A_aux (A_bool nc1,al)]) -> begin
       let new1, kill1, nc1 = simplify nc1 in
       match is_ex_var new1 nc1 with
       | Some kid -> replace kill1 [kid]
       | None -> new1, kill1, NC_aux (NC_app (id,[A_aux (A_bool nc1,al)]),l)
      end
    (* We don't currently recurse into general uses of NC_app, but the
       "boring" cases we really want to get rid of won't contain
       those. *)
    | _ ->
       match is_ex_var KidSet.empty nc_full with
       | Some kid -> replace KidSet.empty [kid]
       | None -> KidSet.empty, KidSet.empty, nc_full
  in
  let new_nc, kill_nc, nc = simplify nc in
  let new_atom, kill_atom, atom_nc = simplify atom_nc in
  let new_kids = KidSet.union new_nc new_atom in
  let kill_kids = KidSet.union kill_nc kill_atom in
  let kopts =
    List.map (fun kid -> mk_kopt K_bool kid) (KidSet.elements new_kids) @
      List.filter (fun kopt -> not (KidSet.mem (kopt_kid kopt) kill_kids)) kopts
  in
(*prerr_endline ("now have " ^ string_of_n_constraint nc ^ " for bool " ^ string_of_n_constraint atom_nc);*)
  match atom_nc with
  | NC_aux (NC_var kid,_) when KBindings.mem kid lin_ty_vars -> Bool_boring
  | NC_aux (NC_var kid,_) when KidSet.mem kid new_kids -> Bool_boring
  | _ -> Bool_complex (kopts, nc, atom_nc)


type ex_kind = ExNone | ExGeneral

let string_of_ex_kind = function
  | ExNone -> "none"
  | ExGeneral -> "general"

(* Should a Sail type be turned into a dependent pair in Coq?
   Optionally takes a variable that we're binding (to avoid trivial cases where
   the type is exactly the boolean we're binding), and whether to turn bools
   with interesting type-expressions into dependent pairs. *)
let classify_ex_type ctxt env ?binding ?(rawbools=false) (Typ_aux (t,l) as t0) =
  let is_binding kid =
    match binding, KBindings.find_opt kid ctxt.kid_id_renames with
    | Some id, Some (Some id') when Id.compare id id' == 0 -> true
    | _ -> false
  in
  let simplify_atom_bool l kopts nc atom_nc =
    match simplify_atom_bool l kopts nc atom_nc with
    | Bool_boring -> Bool_boring
    | Bool_complex (_,_,NC_aux (NC_var kid,_)) when is_binding kid -> Bool_boring
    | Bool_complex (x,y,z) -> Bool_complex (x,y,z)
  in
  match t with
  | Typ_exist (kopts,nc,Typ_aux (Typ_app (Id_aux (Id "atom_bool",_), [A_aux (A_bool atom_nc,_)]),_)) -> begin
      match simplify_atom_bool l kopts nc atom_nc with
      | Bool_boring -> ExNone, [], bool_typ
      | Bool_complex _ -> ExGeneral, [], bool_typ
    end
  | Typ_app (Id_aux (Id "atom_bool",_), [A_aux (A_bool atom_nc,_)]) -> begin
      match rawbools, simplify_atom_bool l [] nc_true atom_nc with
      | false, _ -> ExNone, [], bool_typ
      | _,Bool_boring -> ExNone, [], bool_typ
      | _,Bool_complex _ -> ExGeneral, [], bool_typ
    end
  | Typ_exist (kopts,_,t1) -> ExGeneral,kopts,t1
  | _ -> ExNone,[],t0

let rec flatten_nc (NC_aux (nc,l) as nc_full) =
  match nc with
  | NC_and (nc1,nc2) -> flatten_nc nc1 @ flatten_nc nc2
  | _ -> [nc_full]

(* When making changes here, check whether they affect coq_nvars_of_typ *)
let rec doc_typ_fns ctx env =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ true ty
    and typ' ty = fn_typ false ty
    and fn_typ atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_fn(args,ret,efct) ->
         let ret_typ =
           if effectful efct
           then separate space [string "M"; fn_typ true ret]
           else separate space [fn_typ false ret] in
         let arg_typs = List.map (app_typ false) args in
         let tpp = separate (space ^^ arrow ^^ space) (arg_typs @ [ret_typ]) in
         (* once we have proper excetions we need to know what the exceptions type is *)
         if atyp_needed then parens tpp else tpp
      | _ -> tup_typ atyp_needed ty
    and tup_typ atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_tup typs ->
         parens (separate_map (space ^^ star ^^ space) (app_typ false) typs)
      | _ -> app_typ atyp_needed ty
    and app_typ atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_app(Id_aux (Id "bitvector", _), [
          A_aux (A_nexp m, _);
          A_aux (A_order ord, _)]) ->
         (* TODO: remove duplication with exists, below *)
         let tpp = string "mword " ^^ doc_nexp ctx m in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "vector", _), [
          A_aux (A_nexp m, _);
          A_aux (A_order ord, _);
          A_aux (A_typ elem_typ, _)]) ->
         (* TODO: remove duplication with exists, below *)
         let tpp = string "vec" ^^ space ^^ typ elem_typ ^^ space ^^ doc_nexp ctx m in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) ->
         let tpp = string "register_ref regstate register_value " ^^ typ etyp in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _), _)
      | Typ_id (Id_aux (Id "nat", _)) ->
         (match maybe_expand_range_type ty with
         | Some typ -> atomic_typ atyp_needed typ
         | None -> raise (Reporting.err_unreachable l __POS__ "Bad range type"))
      | Typ_app(Id_aux (Id "implicit", _),_) ->
         (string "Z")
      | Typ_app(Id_aux (Id "atom", _), [A_aux(A_nexp n,_)]) ->
         (string "Z")
      | Typ_app(Id_aux (Id "atom_bool", _), [A_aux (A_bool atom_nc,_)]) ->
         begin match simplify_atom_bool l [] nc_true atom_nc with
         | Bool_boring -> string "bool"
         | Bool_complex (_,_,atom_nc) -> (* simplify won't introduce new kopts *)
            let var = mk_kid "_bool" in (* TODO collision avoid *)
            let nc = nice_iff atom_nc (nc_var var) in
            braces (separate space
                      [doc_var ctx var; colon; string "bool";
                       ampersand;
                       doc_arithfact ctx env nc])
         end
      | Typ_app(id,args) ->
         let tpp = (doc_id_type ctx.types_mod (Some env) id) ^^ space ^^ (separate_map space doc_typ_arg args) in
         if atyp_needed then parens tpp else tpp
      | _ -> atomic_typ atyp_needed ty
    and atomic_typ atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_id (Id_aux (Id "bool",_)) -> string "bool"
      | Typ_id (Id_aux (Id "bit",_)) -> string "bitU"
      | Typ_id (id) ->
         (*if List.exists ((=) (string_of_id id)) regtypes
         then string "register"
         else*) doc_id_type ctx.types_mod (Some env) id
      | Typ_var v -> doc_var ctx v
      | Typ_app _ | Typ_tup _ | Typ_fn _ ->
         (* exhaustiveness matters here to avoid infinite loops
          * if we add a new Typ constructor *)
         let tpp = typ ty in
         if atyp_needed then parens tpp else tpp
      (* TODO: handle non-integer kopts *)
      | Typ_exist (kopts,nc,ty') -> begin
          let kopts,nc,ty' = match maybe_expand_range_type ty' with
            | Some (Typ_aux (Typ_exist (kopts',nc',ty'),_)) ->
               kopts'@kopts,nc_and nc nc',ty'
            | _ -> kopts,nc,ty'
          in
          match ty' with
          | Typ_aux (Typ_app (Id_aux (Id "atom",_),
                              [A_aux (A_nexp nexp,_)]),_) ->
             begin match nexp, kopts with
             | (Nexp_aux (Nexp_var kid,_)), [kopt] when Kid.compare kid (kopt_kid kopt) == 0 ->
                braces (separate space [doc_var ctx kid; colon; string "Z";
                                        ampersand; doc_arithfact ctx env nc])
             | _ ->
                let var = mk_kid "_atom" in (* TODO collision avoid *)
                let nc = nice_and (nc_eq (nvar var) nexp) nc in
                braces (separate space [doc_var ctx var; colon; string "Z";
                                        ampersand; doc_arithfact ctx env ~exists:(List.map kopt_kid kopts) nc])
             end
          | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),
                              [A_aux (A_nexp m, _);
                               A_aux (A_order ord, _)]), _) ->
             (* TODO: proper handling of m, complex elem type, dedup with above *)
             let var = mk_kid "_vec" in (* TODO collision avoid *)
             let kid_set = KidSet.of_list (List.map kopt_kid kopts) in
             let m_pp = doc_nexp ctx ~skip_vars:kid_set m in
             let tpp, len_pp = string "mword " ^^ m_pp, string "length_mword" in
             let length_constraint_pp =
               if KidSet.is_empty (KidSet.inter kid_set (nexp_frees m))
               then None
               else Some (separate space [len_pp; doc_var ctx var; string "=?"; doc_nexp ctx m])
             in
             braces (separate space
                       [doc_var ctx var; colon; tpp;
                        ampersand;
                        doc_arithfact ctx env ~exists:(List.map kopt_kid kopts) ?extra:length_constraint_pp nc])
          | Typ_aux (Typ_app (Id_aux (Id "vector",_),
                              [A_aux (A_nexp m, _);
                               A_aux (A_order ord, _);
                               A_aux (A_typ elem_typ, _)]),_) ->
             (* TODO: proper handling of m, complex elem type, dedup with above *)
             let var = mk_kid "_vec" in (* TODO collision avoid *)
             let kid_set = KidSet.of_list (List.map kopt_kid kopts) in
             let m_pp = doc_nexp ctx ~skip_vars:kid_set m in
             let tpp, len_pp = string "vec" ^^ space ^^ typ elem_typ ^^ space ^^ m_pp, string "vec_length" in
             let length_constraint_pp =
               if KidSet.is_empty (KidSet.inter kid_set (nexp_frees m))
               then None
               else Some (separate space [len_pp; doc_var ctx var; string "=?"; doc_nexp ctx m])
             in
             braces (separate space
                       [doc_var ctx var; colon; tpp;
                        ampersand;
                        doc_arithfact ctx env ~exists:(List.map kopt_kid kopts) ?extra:length_constraint_pp nc])
          | Typ_aux (Typ_app (Id_aux (Id "atom_bool",_), [A_aux (A_bool atom_nc,_)]),_) -> begin
             match simplify_atom_bool l kopts nc atom_nc with
             | Bool_boring -> string "bool"
             | Bool_complex (kopts,nc,atom_nc) ->
                let var = mk_kid "_bool" in (* TODO collision avoid *)
                let nc = nice_and (nice_iff atom_nc (nc_var var)) nc in
                braces (separate space
                          [doc_var ctx var; colon; string "bool";
                           ampersand;
                           doc_arithfact ctx env ~exists:(List.map kopt_kid kopts) nc])
            end
          | Typ_aux (Typ_tup tys,l) -> begin
              (* TODO: boolean existentials *)
              let kid_set = KidSet.of_list (List.map kopt_kid kopts) in
              let should_keep (Typ_aux (ty,_)) =
                match ty with
                | Typ_app (Id_aux (Id "atom",_), [A_aux (A_nexp (Nexp_aux (Nexp_var var,_)),_)]) ->
                   not (KidSet.mem var kid_set)
                | _ -> true
              in
              let out_tys = List.filter should_keep tys in
              let binding_of_tyvar (KOpt_aux (KOpt_kind (K_aux (kind,_) as kaux,kid),_)) =
                let kind_pp = match kind with
                  | K_int -> string "Z"
                  | _ ->
                     raise (Reporting.err_todo l
                              ("Non-atom existential type over " ^ string_of_kind kaux ^ " not yet supported in Coq: " ^
                                 string_of_typ ty))
                in doc_var ctx kid, kind_pp
              in
              let exvars_pp = List.map binding_of_tyvar kopts in
              let pat = match exvars_pp with
                | [v,k] -> v ^^ space ^^ colon ^^ space ^^ k
                | _ ->
                   let vars, types = List.split exvars_pp in
                   squote ^^ parens (separate (string ", ") vars) ^/^
                     colon ^/^ parens (separate (string " * ") types)
              in
              group (braces (group (pat ^^ space ^^ ampersand) ^/^
                               group (tup_typ true (Typ_aux (Typ_tup out_tys,l)) ^^
                                        string "%type ") ^^
                                 ampersand ^/^
                                   doc_arithfact ctx env nc))
            end
          | _ ->
             raise (Reporting.err_todo l
                  ("Non-atom existential type not yet supported in Coq: " ^
                     string_of_typ ty))
        end

(*

        let add_tyvar tpp kid =
          braces (separate space [doc_var ctx kid; colon; string "Z"; ampersand; tpp])
        in
        match drop_duplicate_atoms kids ty with
        | Some ty ->
           let tpp = typ ty in
           let tpp = match nc with NC_aux (NC_true,_) -> tpp | _ ->
             braces (separate space [underscore; colon; parens (doc_arithfact ctx nc); ampersand; tpp])
           in
           List.fold_left add_tyvar tpp kids
        | None ->
           match nc with
(*           | NC_aux (NC_true,_) -> List.fold_left add_tyvar (string "Z") (List.tl kids)*)
           | _ -> List.fold_left add_tyvar (doc_arithfact ctx nc) kids
        end*)
      | Typ_bidir _ -> unreachable l __POS__ "Coq doesn't support bidir types"
      | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
    and doc_typ_arg ?(prop_vars = false) (A_aux(t,_)) = match t with
      | A_typ t -> app_typ true t
      | A_nexp n -> doc_nexp ctx n
      | A_order o -> empty
      | A_bool nc -> parens (doc_nc_exp ctx env nc)
  in typ', atomic_typ, doc_typ_arg
and doc_typ ctx env = let f,_,_ = doc_typ_fns ctx env in f
and doc_atomic_typ ctx env = let _,f,_ = doc_typ_fns ctx env in f
and doc_typ_arg ctx env = let _,_,f = doc_typ_fns ctx env in f

and doc_arithfact ctxt env ?(exists = []) ?extra nc =
  let prop = doc_nc_exp ctxt env nc in
  let prop = match extra with
    | None -> prop
    | Some pp -> separate space [parens pp; string "&&"; parens prop]
  in
  let prop = prop in
  match exists with
  | [] -> string "ArithFact" ^^ space ^^ parens prop
  | _ -> string "ArithFactP" ^^ space ^^
           parens (separate space ([string "exists"]@(List.map (doc_var ctxt) exists)@[comma; prop; equals; string "true"]))

(* Follows Coq precedence levels *)
and doc_nc_exp ctx env nc =
  let locals = Env.get_locals env |> Bindings.bindings in
  let nc = Env.expand_constraint_synonyms env nc in
  let nc_id_map =
    List.fold_left
      (fun m (v,(_,Typ_aux (typ,_))) ->
        match typ with
        | Typ_app (id, [A_aux (A_bool nc,_)]) when string_of_id id = "atom_bool" ->
           (flatten_nc nc, v)::m
        | _ -> m) [] locals
  in
  (* Look for variables in the environment which exactly express the nc, and use
     them instead.  As well as often being shorter, this avoids unbound type
     variables added by Sail's type checker. *)
  let rec newnc f nc =
    let ncs = flatten_nc nc in
    let candidates =
      Util.map_filter (fun (ncs',id) -> Util.option_map (fun x -> x,id) (list_contains NC.compare ncs ncs')) nc_id_map
    in
    match List.sort (fun (l,_) (l',_) -> compare l l') candidates with
    | ([],id)::_ -> doc_id id
    | ((h::t),id)::_ -> parens (doc_op (string "&&") (doc_id id) (l10 (List.fold_left nc_and h t)))
    | [] -> f nc
  and l70 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_equal (ne1, ne2) -> doc_op (string "=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | NC_bounded_ge (ne1, ne2) -> doc_op (string ">=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | NC_bounded_gt (ne1, ne2) -> doc_op (string ">?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | NC_bounded_le (ne1, ne2) -> doc_op (string "<=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | NC_bounded_lt (ne1, ne2) -> doc_op (string "<?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | _ -> l50 nc_full
  and l50 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_or (nc1, nc2) -> doc_op (string "||") (newnc l50 nc1) (newnc l40 nc2)
    | _ -> l40 nc_full
  and l40 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_and (nc1, nc2) -> doc_op (string "&&") (newnc l40 nc1) (newnc l10 nc2)
    | _ -> l10 nc_full
  and l10 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_not_equal (ne1, ne2) -> string "negb" ^^ space ^^ parens (doc_op (string "=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2))
    | NC_set (kid, is) ->
       separate space [string "member_Z_list"; doc_var ctx kid;
                       brackets (separate (string "; ")
                                   (List.map (fun i -> string (Nat_big_num.to_string i)) is))]
    | NC_app (f,args) -> separate space (doc_nc_fn f::List.map doc_typ_arg_exp args)
    | _ -> l0 nc_full
  and l0 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_true -> string "true"
    | NC_false -> string "false"
    | NC_var kid -> doc_nexp ctx (nvar kid)
    | NC_not_equal _
    | NC_set _
    | NC_app _
    | NC_equal _
    | NC_bounded_ge _
    | NC_bounded_gt _
    | NC_bounded_le _
    | NC_bounded_lt _
    | NC_or _
    | NC_and _ -> parens (l70 nc_full)
  and doc_typ_arg_exp (A_aux (arg,l)) =
    match arg with
    | A_nexp nexp -> doc_nexp ctx nexp
    | A_bool nc -> newnc l0 nc
    | A_order _ | A_typ _ ->
       raise (Reporting.err_unreachable l __POS__ "Tried to pass Type or Order kind to SMT function")
  in newnc l70 nc

(* Check for variables in types that would be pretty-printed and are not
   bound in the val spec of the function. *)
let contains_t_pp_var ctxt (Typ_aux (t,a) as typ) =
  KidSet.subset (coq_nvars_of_typ typ) ctxt.bound_nvars

(* TODO: should we resurrect this?
let replace_typ_size ctxt env (Typ_aux (t,a)) =
  match t with
  | Typ_app (Id_aux (Id "vector",_) as id, [A_aux (A_nexp size,_);ord;typ']) ->
     begin
       let mk_typ nexp =
         Some (Typ_aux (Typ_app (id, [A_aux (A_nexp nexp,Parse_ast.Unknown);ord;typ']),a))
       in
       match Type_check.solve env size with
       | Some n -> mk_typ (nconstant n)
       | None ->
          let is_equal nexp =
            prove __POS__ env (NC_aux (NC_equal (size,nexp),Parse_ast.Unknown))
          in match List.find is_equal (NexpSet.elements ctxt.bound_nexps) with
          | nexp -> mk_typ nexp
          | exception Not_found -> None
     end
  | _ -> None*)

let doc_tannot ctxt env eff typ =
  let of_typ typ =
    let ta = doc_typ ctxt env typ in
    if eff then
      if ctxt.early_ret
      then string " : MR " ^^ parens ta ^^ string " _"
      else string " : M " ^^ parens ta
    else string " : " ^^ ta
  in of_typ typ

(* Only double-quotes need escaped - by doubling them. *)
let coq_escape_string s =
  Str.global_replace (Str.regexp "\"") "\"\"" s
   
let doc_lit (L_aux(lit,l)) =
  match lit with
  | L_unit  -> utf8string "tt"
  | L_zero  -> utf8string "B0"
  | L_one   -> utf8string "B1"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i ->
     let s = Big_int.to_string i in
     let ipp = utf8string s in
     if Big_int.less i Big_int.zero then parens ipp else ipp
  (* Not a typo, the bbv hex notation uses the letter O *)
  | L_hex n -> utf8string ("Ox\"" ^ n ^ "\"")
  | L_bin n -> utf8string ("'b\"" ^ n ^ "\"")
  | L_undef ->
     utf8string "(Fail \"undefined value of unsupported type\")"
  | L_string s -> utf8string ("\"" ^ (coq_escape_string s) ^ "\"")
  | L_real s ->
    (* Lem does not support decimal syntax, so we translate a string
       of the form "x.y" into the ratio (x * 10^len(y) + y) / 10^len(y).
       The OCaml library has a conversion function from strings to floats, but
       not from floats to ratios. ZArith's Q library does have the latter, but
       using this would require adding a dependency on ZArith to Sail. *)
    let parts = Util.split_on_char '.' s in
    let (num, denom) = match parts with
    | [i] -> (Big_int.of_string i, Big_int.of_int 1)
    | [i;f] ->
      let denom = Big_int.pow_int_positive 10 (String.length f) in
      (Big_int.add (Big_int.mul (Big_int.of_string i) denom) (Big_int.of_string f), denom)
    | _ ->
      raise (Reporting.err_syntax_loc l "could not parse real literal") in
    parens (separate space (List.map string [
      "realFromFrac"; Big_int.to_string num; Big_int.to_string denom]))

let doc_quant_item_id ?(prop_vars=false) ctx delimit (QI_aux (qi,_)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (K_aux (kind,_),kid),_)) -> begin
    if KBindings.mem kid ctx.kid_id_renames then None else
    match kind with
    | K_type -> Some (delimit (separate space [doc_var ctx kid; colon; string "Type"]))
    | K_int -> Some (delimit (separate space [doc_var ctx kid; colon; string "Z"]))
    | K_order -> None
    | K_bool -> Some (delimit (separate space [doc_var ctx kid; colon;
                                               string (if prop_vars then "Prop" else "bool")]))
  end
  | QI_constraint nc -> None
  | QI_constant _ -> None

let quant_item_id_name ctx (QI_aux (qi,_)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (K_aux (kind,_),kid),_)) -> begin
    if KBindings.mem kid ctx.kid_id_renames then None else
    match kind with
    | K_type -> Some (doc_var ctx kid)
    | K_int -> Some (doc_var ctx kid)
    | K_order -> None
    | K_bool -> Some (doc_var ctx kid)
  end
  | QI_constraint nc -> None
  | QI_constant _ -> None

let doc_quant_item_constr ?(prop_vars=false) ctx env delimit (QI_aux (qi,_)) =
  match qi with
  | QI_id  _ -> None
  | QI_constant _ -> None
  | QI_constraint nc -> Some (bquote ^^ braces (doc_arithfact ctx env nc))

(* At the moment these are all anonymous - when used we rely on Coq to fill
   them in. *)
let quant_item_constr_name ctx (QI_aux (qi,_)) =
  match qi with
  | QI_id  _ -> None
  | QI_constant _ -> None
  | QI_constraint nc -> Some underscore

let doc_typquant_items ?(prop_vars=false) ctx env delimit (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     separate_opt space (doc_quant_item_id ~prop_vars ctx delimit) qis ^^
     separate_opt space (doc_quant_item_constr ~prop_vars ctx env delimit) qis
  | TypQ_no_forall -> empty

let doc_typquant_items_separate ctx env delimit (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     Util.map_filter (doc_quant_item_id ctx delimit) qis,
     Util.map_filter (doc_quant_item_constr ctx env delimit) qis
  | TypQ_no_forall -> [], []

let typquant_names_separate ctx (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     Util.map_filter (quant_item_id_name ctx) qis,
     Util.map_filter (quant_item_constr_name ctx) qis
  | TypQ_no_forall -> [], []


let doc_typquant ctx env (TypQ_aux(tq,_)) typ = match tq with
| TypQ_tq ((_ :: _) as qs) ->
   string "forall " ^^ separate_opt space (doc_quant_item_id ctx braces) qs ^/^
     separate_opt space (doc_quant_item_constr ctx env parens) qs ^^ string ", " ^^ typ
| _ -> typ

(* Produce Size type constraints for bitvector sizes when using
   machine words.  Often these will be unnecessary, but this simple
   approach will do for now. *)

let rec typeclass_nexps (Typ_aux(t,l)) =
  match t with
  | Typ_id _
  | Typ_var _
    -> NexpSet.empty
  | Typ_fn (t1,t2,_) -> List.fold_left NexpSet.union (typeclass_nexps t2) (List.map typeclass_nexps t1)
  | Typ_tup ts -> List.fold_left NexpSet.union NexpSet.empty (List.map typeclass_nexps ts)
  | Typ_app (Id_aux (Id "bitvector",_),
             [A_aux (A_nexp size_nexp,_); _])
  | Typ_app (Id_aux (Id "itself",_),
             [A_aux (A_nexp size_nexp,_)]) ->
     let size_nexp = nexp_simp size_nexp in
     if is_nexp_constant size_nexp then NexpSet.empty else
       NexpSet.singleton (orig_nexp size_nexp)
  | Typ_app _ -> NexpSet.empty
  | Typ_exist (kids,_,t) -> NexpSet.empty (* todo *)
  | Typ_bidir _ -> unreachable l __POS__ "Coq doesn't support bidir types"
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"

let doc_typschm ctx env quants (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  let pt = doc_typ ctx env t in
  if quants then doc_typquant ctx env tq pt else pt

let is_ctor env id = match Env.lookup_id id env with
| Enum _ -> true
| _ -> false

let is_auto_decomposed_exist ctxt env ?(rawbools=false) typ =
  let typ = expand_range_type typ in
  match classify_ex_type ctxt env ~rawbools (Env.expand_synonyms env typ) with
  | ExGeneral, kopts, typ' -> Some (kopts, typ')
  | ExNone, _, _ -> None

(* Partition a list of 'a-type pairs according to whether the types match one of
   the type variables in kopts.  Used for removing redundant parts of tuples
   with existentially bound type variables.  The first part of the returned pair
   has an 'a-type option for each tyvar in kopts, in order, and the second is the
   remaining 'a-type pairs. *)
let filter_dep_tuple kopts vals_typs =
  let kid_set = KidSet.of_list (List.map kopt_kid kopts) in
  let should_keep (_,Typ_aux (ty,_)) =
    match ty with
    | Typ_app (Id_aux (Id "atom",_), [A_aux (A_nexp (Nexp_aux (Nexp_var var,_)),_)]) ->
       not (KidSet.mem var kid_set)
    | _ -> true
  in
  let tup_val_typs, ex_val_typs = List.partition should_keep vals_typs in
  let is_kid kid (Typ_aux (t,_)) =
    match t with
    | Typ_app (Id_aux (Id "atom",_), [A_aux (A_nexp (Nexp_aux (Nexp_var var,_)),_)]) -> Kid.compare kid var == 0
    | _ -> false
  in
  let find_val kopt = List.find_opt (fun (_,ty) -> is_kid (kopt_kid kopt) ty) ex_val_typs in
  List.map find_val kopts, tup_val_typs

let filter_dep_pattern_tuple kopts (P_aux (p,ann) as pat) typ =
  match p, typ with
  | P_tup ps, Typ_aux (Typ_tup ts,l) ->
     let ex_pat_typs, tup_pat_typs = filter_dep_tuple kopts (List.combine ps ts) in
     let map_ex_pat x =
       match x with
       | Some (P_aux (P_wild,_),_) -> string "_"
       | Some (P_aux (P_id id,_),_) -> doc_id id
       | Some (p,t) -> raise (Reporting.err_unreachable l __POS__ ("inconsistent type " ^ string_of_typ t ^ " and pattern " ^ string_of_pat p))
       | None -> string "_"
     in
     let coq_typats = List.map map_ex_pat ex_pat_typs in
     let coq_typat =
       match coq_typats with
       | [p] -> p
       | _ -> parens (separate (string ", ") coq_typats)
     in
     let coq_pat = P_tup (List.map fst tup_pat_typs) in
     let coq_typ = Typ_aux (Typ_tup (List.map snd tup_pat_typs), l) in
     Some coq_typat, P_aux (coq_pat,ann), coq_typ
  | _ -> None, pat, typ

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat ctxt apat_needed exists_as_pairs (P_aux (p,(l,annot)) as pat, typ) =
  let env = env_of_annot (l,annot) in
  let typ = Env.expand_synonyms env typ in
  match exists_as_pairs, is_auto_decomposed_exist ctxt env typ with
  | true, Some (kopts,typ') ->
     debug ctxt (lazy ("decomposing for pattern " ^ string_of_pat pat ^ " at type " ^ string_of_typ typ ^ " with internal type " ^ string_of_typ typ'));
     let ctxt' = { ctxt with bound_nvars = List.fold_left (fun s kopt -> KidSet.add (kopt_kid kopt) s) ctxt.bound_nvars kopts } in
     let typat, pat, typ' = filter_dep_pattern_tuple kopts pat typ' in
     let pat_pp = doc_pat ctxt' true true (pat, typ') in
     let pat_pp =
       match typat with
       | None -> separate space [string "existT"; underscore; pat_pp; underscore]
       | Some typat -> separate space [string "existT2"; underscore; underscore; typat; pat_pp; underscore]
     in
     if apat_needed then parens pat_pp else pat_pp
  | _ ->
     match p with
     (* Special case translation of the None constructor to remove the unit arg *)
     | P_app(id, _) when string_of_id id = "None" -> string "None"
     | P_app(id, ((_ :: _) as pats)) -> begin
        (* Following the type checker to get the subpattern types, TODO perhaps ought
           to persuade the type checker to output these somehow. *)
       let (typq, ctor_typ) = Env.get_union_id id env in
       let arg_typs =
         match Env.expand_synonyms env ctor_typ with
         | Typ_aux (Typ_fn (arg_typs, ret_typ, _), _) ->
            let unifiers = unify l env (tyvars_of_typ ret_typ) ret_typ typ in
            List.map (subst_unifiers unifiers) arg_typs
         | _ -> assert false
       in
       debug ctxt (lazy ("constructor " ^ string_of_id id ^ " with type " ^
                           string_of_typ ctor_typ ^
                             " gives types for subpatterns of " ^
                               String.concat ", " (List.map string_of_typ arg_typs)));
       (* Constructors that were specified without a return type might get
          an extra tuple in their type; expand that here if necessary.
          TODO: this should go away if we enforce proper arities. *)
       let arg_typs = match pats, arg_typs with
         | _::_::_, [Typ_aux (Typ_tup typs,_)] -> typs
         | _,_ -> arg_typs
       in
       let pats_pp = separate_map comma (doc_pat ctxt true true) (List.combine pats arg_typs) in
       let pats_pp = match pats with [_] -> pats_pp | _ -> parens pats_pp in
       let ppp = doc_unop (doc_id_ctor id) pats_pp in
       if apat_needed then parens ppp else ppp
     end
     | P_app(id, []) -> doc_id_ctor id
     | P_lit lit  -> doc_lit lit
     | P_wild -> underscore
     | P_id id -> doc_id id
     | P_var(p,_) -> doc_pat ctxt true exists_as_pairs (p, typ)
     | P_as(p,id) -> parens (separate space [doc_pat ctxt true exists_as_pairs (p, typ); string "as"; doc_id id])
     | P_typ(ptyp,p) ->
        let doc_p = doc_pat ctxt true exists_as_pairs (p, typ) in
        doc_p
     (* Type annotations aren't allowed everywhere in patterns in Coq *)
     (*parens (doc_op colon doc_p (doc_typ typ))*)
     | P_vector pats ->
        let el_typ =
          match destruct_vector env typ with
          | Some (_,_,t) -> t
          | None -> raise (Reporting.err_unreachable l __POS__ "vector pattern doesn't have vector type")
        in
        let ppp = brackets (separate_map semi (fun p -> doc_pat ctxt true exists_as_pairs (p,el_typ)) pats) in
        if apat_needed then parens ppp else ppp
     | P_vector_concat pats ->
        raise (Reporting.err_unreachable l __POS__
                 "vector concatenation patterns should have been removed before pretty-printing")
     | P_tup pats  ->
        let typs = match typ with
          | Typ_aux (Typ_tup typs, _) -> typs
          | Typ_aux (Typ_exist _,_) ->
             raise (Reporting.err_todo l "existential types not yet supported here")
          | _ -> raise (Reporting.err_unreachable l __POS__ "tuple pattern doesn't have tuple type")
        in
        (match pats, typs with
        | [p], [typ'] -> doc_pat ctxt apat_needed true (p, typ')
        | [_], _ -> raise (Reporting.err_unreachable l __POS__ "tuple pattern length does not match tuple type length")
        | _ -> parens (separate_map comma_sp (doc_pat ctxt false true) (List.combine pats typs)))
     | P_list pats ->
        let el_typ = match typ with
          | Typ_aux (Typ_app (f, [A_aux (A_typ el_typ,_)]),_)
              when Id.compare f (mk_id "list") = 0 -> el_typ
          | _ -> raise (Reporting.err_unreachable l __POS__ "list pattern not a list")
        in
        brackets (separate_map semi (fun p -> doc_pat ctxt false true (p, el_typ)) pats)
     | P_cons (p,p') ->
        let el_typ = match typ with
          | Typ_aux (Typ_app (f, [A_aux (A_typ el_typ,_)]),_)
              when Id.compare f (mk_id "list") = 0 -> el_typ
          | _ -> raise (Reporting.err_unreachable l __POS__ "list pattern not a list")
        in
        doc_op (string "::") (doc_pat ctxt true true (p, el_typ)) (doc_pat ctxt true true (p', typ))
     | P_string_append _ -> unreachable l __POS__
        "string append pattern found in Coq backend, should have been rewritten"
     | P_not _ -> unreachable l __POS__ "Coq backend doesn't support not patterns"
     | P_or _ -> unreachable l __POS__ "Coq backend doesn't support or patterns yet"

let contains_early_return exp =
  let e_app (f, args) =
    let rets, args = List.split args in
    (List.fold_left (||) (string_of_id f = "early_return") rets,
    E_app (f, args)) in
  fst (fold_exp
  { (Rewriter.compute_exp_alg false (||))
    with e_return = (fun (_, r) -> (true, E_return r)); e_app = e_app } exp)

let find_e_ids exp =
  let e_id id = IdSet.singleton id, E_id id in
  fst (fold_exp
    { (compute_exp_alg IdSet.empty IdSet.union) with e_id = e_id } exp)

let typ_id_of (Typ_aux (typ, l)) = match typ with
  | Typ_id id -> id
  | Typ_app (register, [A_aux (A_typ (Typ_aux (Typ_id id, _)), _)])
    when string_of_id register = "register" -> id
  | Typ_app (id, _) -> id
  | _ -> raise (Reporting.err_unreachable l __POS__ "failed to get type id")

(* TODO: maybe Nexp_exp, division? *)
(* Evaluation of constant nexp subexpressions, because Coq will be able to do those itself *)
let rec nexp_const_eval (Nexp_aux (n,l) as nexp) =
  let binop f re l n1 n2 =
  match nexp_const_eval n1, nexp_const_eval n2 with
  | Nexp_aux (Nexp_constant c1,_), Nexp_aux (Nexp_constant c2,_) ->
     Nexp_aux (Nexp_constant (f c1 c2),l)
  | n1', n2' -> Nexp_aux (re n1' n2',l)
  in
  let unop f re l n1 =
  match nexp_const_eval n1 with
  | Nexp_aux (Nexp_constant c1,_) -> Nexp_aux (Nexp_constant (f c1),l)
  | n1' -> Nexp_aux (re n1',l)
  in
  match n with
  | Nexp_times (n1,n2) -> binop Big_int.mul (fun n1 n2 -> Nexp_times (n1,n2)) l n1 n2
  | Nexp_sum (n1,n2) -> binop Big_int.add (fun n1 n2 -> Nexp_sum (n1,n2)) l n1 n2
  | Nexp_minus (n1,n2) -> binop Big_int.sub (fun n1 n2 -> Nexp_minus (n1,n2)) l n1 n2
  | Nexp_neg n1 -> unop Big_int.negate (fun n -> Nexp_neg n) l n1
  | _ -> nexp

(* Decide whether two nexps used in a vector size are similar; if not
   a cast will be inserted *)
let similar_nexps ctxt env n1 n2 =
  let rec same_nexp_shape (Nexp_aux (n1,_)) (Nexp_aux (n2,_)) =
    match n1, n2 with
    | Nexp_id _, Nexp_id _ -> true
    (* TODO: this is really just an approximation to what we really want:
       will the Coq types have the same names?  We could probably do better
       by tracking which existential kids are equal to bound kids. *)
    | Nexp_var k1, Nexp_var k2 ->
       Kid.compare k1 k2 == 0 ||
         (prove __POS__ env (nc_eq (nvar k1) (nvar k2)) && (
            not (KidSet.mem k1 ctxt.bound_nvars) ||
              not (KidSet.mem k2 ctxt.bound_nvars)))
    | Nexp_constant c1, Nexp_constant c2 -> Nat_big_num.equal c1 c2
    | Nexp_app (f1,args1), Nexp_app (f2,args2) ->
       Id.compare f1 f2 == 0 && List.for_all2 same_nexp_shape args1 args2
    | Nexp_times (n1,n2), Nexp_times (n3,n4)
    | Nexp_sum (n1,n2), Nexp_sum (n3,n4)
    | Nexp_minus (n1,n2), Nexp_minus (n3,n4)
      -> same_nexp_shape n1 n3 && same_nexp_shape n2 n4
    | Nexp_exp n1, Nexp_exp n2
    | Nexp_neg n1, Nexp_neg n2
      -> same_nexp_shape n1 n2
    | _ -> false
  in if same_nexp_shape (nexp_const_eval n1) (nexp_const_eval n2) then true else false

let constraint_fns = ["Z.leb"; "Z.geb"; "Z.ltb"; "Z.gtb"; "Z.eqb"; "neq_int"]

let condition_produces_constraint ctxt exp =
  let env = env_of exp in
  match classify_ex_type ctxt env ~rawbools:true (typ_of exp) with
  | ExNone, _, _ -> false
  | ExGeneral, _, _ -> true

(* For most functions whose return types are non-trivial atoms we return a
   dependent pair with a proof that the result is the expected integer.  This
   is redundant for basic arithmetic functions and functions which we unfold
   in the constraint solver. *)
let no_proof_fns = ["Z.add"; "Z.sub"; "Z.opp"; "Z.mul"; "Z.rem";
                    "length_mword"; "length"; "vec_length";
                    "negb"; "andb"; "orb";
                    "Z.leb"; "Z.geb"; "Z.ltb"; "Z.gtb"; "Z.eqb"]

let is_no_proof_fn env id =
  if Env.is_extern id env "coq"
  then
    let s = Env.get_extern id env "coq" in
    List.exists (fun x -> String.compare x s == 0) no_proof_fns
  else false

let replace_atom_return_type ret_typ =
  (* TODO: more complex uses of atom *)
  match ret_typ with
  | Typ_aux (Typ_app (Id_aux (Id "atom",_), [A_aux (A_nexp nexp,_)]),l) ->
     let kid = mk_kid "_retval" in (* TODO: collision avoidance *)
     Some "build_ex", Typ_aux (Typ_exist ([mk_kopt K_int kid], nc_eq (nvar kid) nexp, atom_typ (nvar kid)),Parse_ast.Generated l)
  | Typ_aux (Typ_app (Id_aux (Id "atom_bool",il), ([A_aux (A_bool _,_)] as args)),l) ->
     Some "build_ex", ret_typ
  | _ -> None, ret_typ

let is_range_from_atom env (Typ_aux (argty,_)) (Typ_aux (fnty,_)) =
  match argty, fnty with
  | Typ_app(Id_aux (Id "atom", _), [A_aux (A_nexp nexp,_)]),
    Typ_app(Id_aux (Id "range", _), [A_aux(A_nexp low,_);
                                     A_aux(A_nexp high,_)]) ->
     Type_check.prove __POS__ env (nc_and (nc_eq nexp low) (nc_eq nexp high))
  | _ -> false

(* Get a more general type for an annotation/expression - i.e.,
   like typ_of but using the expected type if there was one *)
let general_typ_of_annot annot =
  match expected_typ_of annot with
  | None -> typ_of_annot annot
  | Some typ -> typ

let general_typ_of (E_aux (_,annot)) = general_typ_of_annot annot

let is_prefix s s' =
  let l = String.length s in
  String.length s' >= l &&
  String.sub s' 0 l = s

let merge_new_tyvars ctxt old_env pat new_env =
  let remove_binding id (m,r) =
    match Bindings.find_opt id r with
    | Some kid ->
       debug ctxt (lazy ("Removing " ^ string_of_kid kid ^ " to " ^ string_of_id id));
       KBindings.add kid None m, Bindings.remove id r
    | None -> m,r
  in
  let check_kid id kid (m,r) =
    try
      let _ = Env.get_typ_var kid old_env in
      debug ctxt (lazy (" tyvar " ^ string_of_kid kid ^ " already in env"));
      m,r
    with _ ->
      debug ctxt (lazy (" adding tyvar mapping " ^ string_of_kid kid ^ " to " ^ string_of_id id));
      KBindings.add kid (Some id) m, Bindings.add id kid r
  in
  let merge_new_kids id m =
    let typ = lvar_typ (Env.lookup_id ~raw:true id new_env) in
    debug ctxt (lazy (" considering tyvar mapping for " ^ string_of_id id ^ " at type " ^ string_of_typ typ ));
    match destruct_numeric typ, destruct_atom_bool new_env typ with
    | Some ([],_,Nexp_aux (Nexp_var kid,_)), _
    | _, Some (NC_aux (NC_var kid,_))
      -> check_kid id kid m
    | _ ->
       debug ctxt (lazy (" not suitable type"));
       m
  in
  let rec merge_pat m (P_aux (p,(l,_))) =
    match p with
    | P_lit _ | P_wild
      -> m
    | P_not _ -> unreachable l __POS__ "Coq backend doesn't support not patterns"
    | P_or _ -> unreachable l __POS__ "Coq backend doesn't support or patterns yet"
    | P_typ (_,p) -> merge_pat m p
    | P_as (p,id) -> merge_new_kids id (merge_pat m p)
    | P_id id -> merge_new_kids id m
    | P_var (p,ty_p) ->
       begin match p, ty_p with
       | _, TP_aux (TP_wild,_) -> merge_pat m p
       | P_aux (P_id id,_), TP_aux (TP_var kid,_) -> check_kid id kid (merge_pat m p)
       | _ -> merge_pat m p
       end
    (* Some of these don't make it through to the backend, but it's obvious what
       they'd do *)
    | P_app (_,ps)
    | P_vector ps
    | P_vector_concat ps
    | P_tup ps
    | P_list ps
    | P_string_append ps
      -> List.fold_left merge_pat m ps
    | P_cons (p1,p2) -> merge_pat (merge_pat m p1) p2
  in
  let m,r = IdSet.fold remove_binding (pat_ids pat) (ctxt.kid_id_renames, ctxt.kid_id_renames_rev) in
  let m,r = merge_pat (m, r) pat in
  { ctxt with kid_id_renames = m; kid_id_renames_rev = r }

let maybe_parens_comma_list f ls =
  match ls with
  | [x] -> f true x
  | xs -> parens (separate (string ", ") (List.map (f false) xs))

let prefix_recordtype = true
let report = Reporting.err_unreachable
let doc_exp, doc_let =
  let rec top_exp (ctxt : context) (aexp_needed : bool)
    (E_aux (e, (l,annot)) as full_exp) =
    let top_exp c a e = 
      let () = debug_depth := !debug_depth + 1 in
      let r = top_exp c a e in
      let () = debug_depth := !debug_depth - 1 in
      r
    in
    let expY = top_exp ctxt true in
    let expN = top_exp ctxt false in
    let expV = top_exp ctxt in
    let wrap_parens doc = if aexp_needed then parens (doc) else doc in
    let maybe_add_exist epp =
      let env = env_of full_exp in
      let typ = Env.expand_synonyms env (general_typ_of full_exp) in
      let () =
        debug ctxt (lazy ("Considering build_ex for " ^ string_of_exp full_exp));
        debug ctxt (lazy (" at type " ^ string_of_typ typ))
      in
      let typ = expand_range_type typ in
      match destruct_exist_plain typ with
      | None -> epp
      | Some (kopts,nc,Typ_aux (Typ_app (Id_aux (Id "atom_bool",_), [A_aux (A_bool atom_nc,_)]),l)) -> begin
          match simplify_atom_bool l kopts nc atom_nc with
          | Bool_boring -> epp
          | Bool_complex _ -> wrap_parens (string "build_ex" ^/^ epp)
        end
      | Some _ ->
         wrap_parens (string "build_ex" ^/^ epp)
    in
    let construct_dep_pairs ?(rawbools=false) env =
      let rec aux want_parens (E_aux (e,_) as exp) typ =
        match e with
        | E_tuple exps
        | E_cast (_, E_aux (E_tuple exps,_))
          -> begin
            match typ with
            | Typ_aux (Typ_exist (kopts,nc,Typ_aux (Typ_tup typs,_)),_) ->
               debug ctxt (lazy ("Constructing dependent tuple " ^
                                   String.concat ", " (List.map string_of_exp exps) ^
                                     " of type " ^ string_of_typ typ));
               let ex_exp_typs, tup_exp_typs = filter_dep_tuple kopts (List.combine exps typs) in
               let ex_exps = Util.map_filter (function Some x -> Some x | None -> None) ex_exp_typs in
               let ex_pp = maybe_parens_comma_list (fun want_parens (exp,typ) -> aux want_parens exp typ) ex_exps in
               let tup_pp = maybe_parens_comma_list (fun want_parens (exp,typ) -> aux want_parens exp typ) tup_exp_typs in
               let pp = group (string "build_ex2" ^/^ ex_pp ^/^ tup_pp) in
               if want_parens then parens pp else pp
            | _ ->
               let typs = List.map general_typ_of exps in
               parens (separate (string ", ") (List.map2 (aux false) exps typs))
          end
        | _ ->
           let typ' = expand_range_type (Env.expand_synonyms (env_of exp) typ) in
           debug ctxt (lazy ("Constructing " ^ string_of_exp exp ^ " at type " ^ string_of_typ typ));
           let build_ex, out_typ =
             match classify_ex_type ctxt (env_of exp) ~rawbools typ' with
             | ExNone, _, _ -> None, typ'
             | ExGeneral, _, typ' -> Some "build_ex", typ'
           in
           let in_typ = expand_range_type (Env.expand_synonyms (env_of exp) (typ_of exp)) in
           let in_typ = match destruct_exist_plain in_typ with Some (_,_,t) -> t | None -> in_typ in
           let autocast =
             (* Avoid using helper functions which simplify the nexps *)
             match in_typ, out_typ with
             | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n1,_);_]),_),
               Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n2,_);_]),_) ->
                not (similar_nexps ctxt (env_of exp) n1 n2)
             | _ -> false
           in
           let exp_pp = expV (want_parens || autocast || Util.is_some build_ex) exp in
           let exp_pp =
             if autocast then
               let exp_pp = string "autocast" ^^ space ^^ exp_pp in
               if want_parens || Util.is_some build_ex then parens exp_pp else exp_pp
             else exp_pp
           in match build_ex with
              | Some s ->
                let exp_pp = string s ^/^ exp_pp in
                if want_parens then parens exp_pp else exp_pp
              | None -> exp_pp
      in aux
    in
    let liftR doc =
      if ctxt.early_ret && effectful (effect_of full_exp)
      then separate space [string "liftR"; parens (doc)]
      else doc in
    match e with
    | E_assign(_, _) when has_effect (effect_of full_exp) BE_config ->
       string "returnm tt" (* TODO *)
    | E_assign((LEXP_aux(le_act,tannot) as le), e) ->
       (* can only be register writes *)
       (match le_act (*, t, tag*) with
        | LEXP_vector_range (le,e2,e3) ->
           (match le with
            | LEXP_aux (LEXP_field ((LEXP_aux (_, lannot) as le),id), fannot) ->
               if is_bit_typ (typ_of_annot fannot) then
                 raise (report l __POS__ "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id id in
                 liftR ((prefix 2 1)
                   (string "write_reg_field_range")
                   (align (doc_lexp_deref ctxt le ^/^
                      field_ref ^/^ expY e2 ^/^ expY e3 ^/^ expY e)))
            | _ ->
               let deref = doc_lexp_deref ctxt le in
               liftR ((prefix 2 1)
                 (string "write_reg_range")
                 (align (deref ^/^ expY e2 ^/^ expY e3) ^/^ expY e)))
        | LEXP_vector (le,e2) ->
           (match le with
            | LEXP_aux (LEXP_field ((LEXP_aux (_, lannot) as le),id), fannot) ->
               if is_bit_typ (typ_of_annot fannot) then
                 raise (report l __POS__ "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id id in
                 let call = if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot fannot)) then "write_reg_field_bit" else "write_reg_field_pos" in
                 liftR ((prefix 2 1)
                   (string call)
                   (align (doc_lexp_deref ctxt le ^/^
                     field_ref ^/^ expY e2 ^/^ expY e)))
            | LEXP_aux (_, lannot) ->
               let deref = doc_lexp_deref ctxt le in
               let call = if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot lannot)) then "write_reg_bit" else "write_reg_pos" in
               liftR ((prefix 2 1) (string call)
               (deref ^/^ expY e2 ^/^ expY e))
           )
        | LEXP_field ((LEXP_aux (_, lannot) as le),id) ->
          let field_ref =
            doc_id (typ_id_of (typ_of_annot lannot)) ^^
            underscore ^^
            doc_id id (*^^
            dot ^^
            string "set_field"*) in
           liftR ((prefix 2 1)
             (string "write_reg_field")
             (doc_lexp_deref ctxt le ^^ space ^^
                field_ref ^/^ expY e))
        | LEXP_deref re ->
           liftR ((prefix 2 1) (string "write_reg") (expY re ^/^ expY e))
        | _ ->
           liftR ((prefix 2 1) (string "write_reg") (doc_lexp_deref ctxt le ^/^ expY e)))
    | E_vector_append(le,re) ->
      raise (Reporting.err_unreachable l __POS__
        "E_vector_append should have been rewritten before pretty-printing")
    | E_cons(le,re) -> doc_op (group (colon^^colon)) (expY le) (expY re)
    | E_if(c,t,e) ->
       let epp = if_exp ctxt false c t e in
       if aexp_needed then parens (align epp) else epp
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
       raise (report l __POS__ "E_for should have been rewritten before pretty-printing")
    | E_loop _ ->
       raise (report l __POS__ "E_loop should have been rewritten before pretty-printing")
    | E_let(leb,e) ->
       let pat = match leb with LB_aux (LB_val (p,_),_) -> p in
       let () = debug ctxt (lazy ("Let with pattern " ^ string_of_pat pat)) in
       let new_ctxt = merge_new_tyvars ctxt (env_of_annot (l,annot)) pat (env_of e) in
       let epp = let_exp ctxt leb ^^ space ^^ string "in" ^^ hardline ^^ top_exp new_ctxt false e in
       if aexp_needed then parens epp else epp
    | E_app(f,args) ->
       let env = env_of full_exp in
       let doc_loop_var (E_aux (e,(l,_)) as exp) =
         match e with
         | E_id id ->
            let id_pp = doc_id id in
            let typ = general_typ_of exp in
            if Util.is_some (is_auto_decomposed_exist ctxt env typ)
            then string "build_ex" ^^ space ^^ id_pp ^/^
                   colon ^^ space ^^ doc_typ ctxt env typ,
                 separate space [string "existT"; underscore; id_pp; underscore],
                 true
            else id_pp, id_pp, false
         | E_lit (L_aux (L_unit,_)) -> string "tt", underscore, false
         | _ -> raise (Reporting.err_unreachable l __POS__
                         ("Bad expression for variable in loop: " ^ string_of_exp exp))
       in
       let make_loop_vars extra_binders varstuple =
         match varstuple with
         | E_aux (E_tuple vs, _) ->
            let vs = List.map doc_loop_var vs in
            let mkpp f vs = separate (string ", ") (List.map f vs) in
            let tup_pp = mkpp (fun (pp,_,_) -> pp) vs in
            let match_pp = mkpp (fun (_,pp,_) -> pp) vs in
            parens tup_pp,
            separate space (string "fun" :: extra_binders @
                              [squote ^^ parens match_pp; bigarrow])
         | _ ->
            let exp_pp,match_pp,decompose = doc_loop_var varstuple in
            let vpp = if decompose
                      then squote ^^ parens match_pp
                      else match_pp
            in
            let exp_pp = if decompose then parens exp_pp else exp_pp in
            exp_pp,
            separate space (string "fun" :: extra_binders @ [vpp; bigarrow])
       in
       begin match f with
       | Id_aux (Id "and_bool", _) | Id_aux (Id "or_bool", _)
         when effectful (effect_of full_exp) ->
          let informative = Util.is_some (is_auto_decomposed_exist ctxt (env_of full_exp) (general_typ_of full_exp)) in
          let suffix = if informative then "MP" else "M" in
          let call = doc_id (append_id f suffix) in
          let doc_arg exp =
            let epp = expY exp in
            match is_auto_decomposed_exist ctxt (env_of exp) ~rawbools:true (general_typ_of exp) with
            | Some _ ->
               if informative
               then parens (epp ^^ doc_tannot ctxt (env_of exp) true (general_typ_of exp))
               else parens (string "projT1_m" ^/^ epp)
            | None ->
               if informative then parens (string "build_trivial_ex" ^/^ epp)
               else epp
          in
          let epp = hang 2 (flow (break 1) (call :: List.map doc_arg args)) in
          let epp = if informative then epp ^^ doc_tannot ctxt (env_of full_exp) true (general_typ_of full_exp) else epp in
          wrap_parens epp
       (* temporary hack to make the loop body a function of the temporary variables *)
       | Id_aux (Id "None", _) as none -> doc_id_ctor none
       | Id_aux (Id "foreach#", _) ->
          begin
            match args with
            | [from_exp; to_exp; step_exp; ord_exp; vartuple; body] ->
               let loopvar, body = match body with
                 | E_aux (E_if (_,
                   E_aux (E_let (LB_aux (LB_val (
                     ((P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _))
                     | (P_aux (P_var (P_aux (P_id id, _), _), _))
                     | (P_aux (P_id id, _))), _), _),
                     body), _), _), _) -> id, body
                 | _ -> raise (Reporting.err_unreachable l __POS__ ("Unable to find loop variable in " ^ string_of_exp body)) in
               let dir = match ord_exp with
                 | E_aux (E_lit (L_aux (L_false, _)), _) -> "_down"
                 | E_aux (E_lit (L_aux (L_true, _)), _) -> "_up"
                 | _ -> raise (Reporting.err_unreachable l __POS__ ("Unexpected loop direction " ^ string_of_exp ord_exp))
               in
               let effects = effectful (effect_of body) in
               let combinator = if effects then "foreach_ZM" else "foreach_Z" in
               let combinator = combinator ^ dir in
               let body_ctxt = add_single_kid_id_rename ctxt loopvar (mk_kid ("loop_" ^ string_of_id loopvar)) in
               let from_exp_pp, to_exp_pp, step_exp_pp =
                 expY from_exp, expY to_exp, expY step_exp
               in
               (* The body has the right type for deciding whether a proof is necessary *)
               let vartuple_retyped = check_exp env (strip_exp vartuple) (general_typ_of body) in
               let vartuple_pp, body_lambda =
                 make_loop_vars [doc_id loopvar; underscore] vartuple_retyped
               in
               parens (
                   (prefix 2 1)
                     ((separate space) [string combinator;
                                        from_exp_pp; to_exp_pp; step_exp_pp;
                                        vartuple_pp])
                     (parens
                        (prefix 2 1 (group body_lambda) (top_exp body_ctxt false body))
                     )
                 )
          | _ -> raise (Reporting.err_unreachable l __POS__
             "Unexpected number of arguments for loop combinator")
          end
       | Id_aux (Id (("while#" | "until#" | "while#t" | "until#t") as combinator), _) ->
          let combinator = String.sub combinator 0 (String.index combinator '#') in
          begin
            let cond, varstuple, body, measure =
              match args with
              | [cond; varstuple; body] -> cond, varstuple, body, None
              | [cond; varstuple; body; measure] -> cond, varstuple, body, Some measure
              | _ -> raise (Reporting.err_unreachable l __POS__
                              "Unexpected number of arguments for loop combinator")
            in
            let return (E_aux (e, (l,a))) =
              let a' = mk_tannot (env_of_annot (l,a)) bool_typ no_effect in
              E_aux (E_internal_return (E_aux (e, (l,a))), (l,a'))
            in
            let simple_bool (E_aux (_, (l,a)) as exp) =
              let a' = mk_tannot (env_of_annot (l,a)) bool_typ no_effect in
              E_aux (E_cast (bool_typ, exp), (l,a'))
            in
            let csuffix, cond, body =
              match effectful (effect_of cond), effectful (effect_of body) with
              | false, false -> "", cond, body
              | false, true  -> "M", return cond, body
              | true,  false -> "M", simple_bool cond, return body
              | true,  true  -> "M", simple_bool cond, body
            in
            (* If rewrite_loops_with_escape_effect added a dummy assertion to
               ensure that the loop can escape when it reaches the limit, omit
               the dummy assert here. *)
            let body = match body with
              | E_aux (E_internal_plet
                  (P_aux ((P_wild | P_typ (_,P_aux (P_wild, _))),_),
                   E_aux (E_assert
                            (E_aux (E_lit (L_aux (L_true,_)),_),
                             E_aux (E_lit (L_aux (L_string "loop dummy assert",_)),_))
                         ,_),body'),_) -> body'
              | _ -> body
            in
            (* The variable tuple (and the loop body) may have
               overspecific types, so use the loop's type for deciding
               whether a proof is necessary *)
            let body_pp = construct_dep_pairs (env_of body) false body (general_typ_of full_exp) in
            let varstuple_retyped = check_exp env (strip_exp varstuple) (general_typ_of full_exp) in
            let varstuple_pp, lambda =
              make_loop_vars [] varstuple_retyped
            in
            let msuffix, measure_pp =
              match measure with
              | None -> "", []
              | Some exp -> "T", [parens (prefix 2 1 (group lambda) (expN exp))]
            in
            let proj = match classify_ex_type ctxt env (general_typ_of full_exp) with
              | ExGeneral, _, _ -> fun pp -> string "projT1 " ^^ parens pp
              | ExNone, _, _ -> fun pp -> pp
            in
            parens (proj (
                (prefix 2 1)
                  (string (combinator ^ csuffix ^ msuffix))
                  (separate (break 1)
                     (varstuple_pp::measure_pp@
                        [parens (prefix 2 1 (group lambda) (expN cond));
                         parens (prefix 2 1 (group lambda) body_pp)]))
              ))
          end
       | Id_aux (Id "early_return", _) ->
          begin
            match args with
            | [exp] ->
               let exp_pp =
                 match ctxt.build_at_return with
                 | Some s -> parens (string s ^/^ expY exp)
                 | None -> expY exp
               in
               let epp = separate space [string "early_return"; exp_pp] in
               let tannot = separate space [string "MR";
                 doc_atomic_typ ctxt (env_of full_exp) false (typ_of full_exp);
                 doc_atomic_typ ctxt (env_of exp) false (typ_of exp)]
               in
               parens (doc_op colon epp tannot)
            | _ -> raise (Reporting.err_unreachable l __POS__
               "Unexpected number of arguments for early_return builtin")
          end
       | _ ->
          let env = env_of_annot (l,annot) in
          let () = debug ctxt (lazy ("Function application " ^ string_of_id f)) in
          let call, is_extern, is_ctor, is_rec =
            if Env.is_union_constructor f env then doc_id_ctor f, false, true, None else
            if Env.is_extern f env "coq"
            then string (Env.get_extern f env "coq"), true, false, None
            else doc_id f, false, false, Bindings.find_opt f ctxt.recursive_fns
          in
          let (tqs,fn_ty) =
            if is_ctor then Env.get_union_id f env else Env.get_val_spec f env
          in
          (* Calculate the renaming *)
          let tqs_map = List.fold_left
                          (fun m k ->
                            let kid = kopt_kid k in
                            KBindings.add (orig_kid kid) kid m)
                          KBindings.empty (quant_kopts tqs) in
          let arg_typs, ret_typ, eff = match fn_ty with
            | Typ_aux (Typ_fn (arg_typs,ret_typ,eff),_) -> arg_typs, ret_typ, eff
            | _ -> raise (Reporting.err_unreachable l __POS__ "Function not a function type")
          in
          let inst, inst_env =
            (* We attempt to get an instantiation of the function signature's
               type variables which agrees with Coq by
               1. using dummy variables with the expected type of each argument
                  (avoiding the inferred type, which might have (e.g.) stripped
                  out an existential quantifier)
               2. calculating the instantiation without using the expected
                  return type, so that we can work out if we need a cast around
                  the function call. *)
            let dummy_args =
              Util.list_mapi (fun i exp -> mk_id ("#coq#arg" ^ string_of_int i),
                                           general_typ_of exp) args
            in
            let () = debug ctxt (lazy (" arg types: " ^ String.concat ", " (List.map (fun (_,ty) -> string_of_typ ty) dummy_args))) in
            let dummy_exp = mk_exp (E_app (f, List.map (fun (id,_) -> mk_exp (E_id id)) dummy_args)) in
            let dummy_env = List.fold_left (fun env (id,typ) -> Env.add_local id (Immutable,typ) env) env dummy_args in
            let (E_aux (_, (_, inst_tannot))) as inst_exp =
              try infer_exp dummy_env dummy_exp
              with ex ->
                debug ctxt (lazy (" cannot infer dummy application " ^ Printexc.to_string ex));
                full_exp
            in
            (* We may have inherited existentials from the arguments,
               so add any to the environment. *)
            let inst_env =
              match typ_of inst_exp with
              | Typ_aux (Typ_exist (kopts, _, _), l) ->
                 List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) env kopts
              | _ -> env
            in
            match get_instantiations inst_tannot with
            | Some x -> x, inst_env
            (* Not all function applications can be inferred, so try falling back to the
               type inferred when we know the target type.
               TODO: there are probably some edge cases where this won't pick up a need
               to cast. *)
            | None ->
               (debug ctxt (lazy (" unable to infer function instantiation without return type " ^ string_of_typ (typ_of full_exp)));
                instantiation_of full_exp, env)
          in
          let () = debug ctxt (lazy (" instantiations pre-rename: " ^ String.concat ", " (List.map (fun (kid,tyarg) -> string_of_kid kid ^ " => " ^ string_of_typ_arg tyarg) (KBindings.bindings inst)))) in
          let inst = KBindings.fold (fun k u m ->
                         match KBindings.find_opt (orig_kid k) tqs_map with
                         | Some k' -> KBindings.add k' u m
                         | None -> m (* must have been an existential *) ) inst KBindings.empty in
          let () = debug ctxt (lazy (" instantiations: " ^ String.concat ", " (List.map (fun (kid,tyarg) -> string_of_kid kid ^ " => " ^ string_of_typ_arg tyarg) (KBindings.bindings inst)))) in

          (* Insert existential packing of arguments where necessary *)
          let doc_arg want_parens arg typ_from_fn =
            let env = env_of arg in
            let typ_from_fn = subst_unifiers inst typ_from_fn in
            let typ_from_fn = Env.expand_synonyms inst_env typ_from_fn in
            (* TODO: more sophisticated check *)
            let () =
              debug ctxt (lazy (" arg type found    " ^ string_of_typ (typ_of arg)));
              debug ctxt (lazy (" arg type expected " ^ string_of_typ typ_from_fn))
            in
            let typ_of_arg = Env.expand_synonyms env (typ_of arg) in
            let typ_of_arg = expand_range_type typ_of_arg in
            let typ_of_arg' = match typ_of_arg with Typ_aux (Typ_exist (_,_,t),_) -> t  | t -> t in
            let typ_from_fn' = match typ_from_fn with Typ_aux (Typ_exist (_,_,t),_) -> t  | t -> t in
            let autocast =
              (* Avoid using helper functions which simplify the nexps *)
              match typ_of_arg', typ_from_fn' with
              | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n1,_);_]),_),
                Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n2,_);_]),_) ->
                 not (similar_nexps ctxt env n1 n2)
              | _ -> false
            in
            (* If the argument is an integer that can be inferred from the
               context in a different form, let Coq fill it in.  E.g.,
               when "64" is really "8 * width".  Avoid cases where the
               type checker has introduced a phantom type variable while
               calculating the instantiations. *)
            let vars_in_env n =
              let ekids = Env.get_typ_vars env in
              KidSet.for_all (fun kid -> KBindings.mem kid ekids) (nexp_frees n)
            in
            match destruct_atom_nexp env typ_of_arg, destruct_atom_nexp env typ_from_fn with
            | Some n1, Some n2
                 when vars_in_env n2 && not (similar_nexps ctxt env n1 n2) ->
               underscore
            | _ ->
               let want_parens1 = want_parens || autocast in
               let arg_pp =
                 construct_dep_pairs inst_env want_parens1 arg typ_from_fn
               in
               if autocast && false
               then let arg_pp = string "autocast" ^^ space ^^ arg_pp in
                    if want_parens then parens arg_pp else arg_pp
               else arg_pp
          in
          let epp =
            if is_ctor
            then
              let argspp = match args, arg_typs with
                | [arg], [arg_typ] -> doc_arg true arg arg_typ
                | _, _ -> parens (flow (comma ^^ break 1) (List.map2 (doc_arg false) args arg_typs))
              in group (hang 2 (call ^^ break 1 ^^ argspp))
            else
              let argspp = List.map2 (doc_arg true) args arg_typs in
              let all =
                match is_rec with
                | Some (pre,post) -> call :: List.init pre (fun _ -> underscore) @ argspp @
                                       List.init post (fun _ -> underscore) @
                                         [parens (string "_limit_reduces _acc")]
                | None -> 
                   match f with
                   | Id_aux (Id x,_) when is_prefix "#rec#" x ->
                      call :: argspp @ [parens (string "Zwf_guarded _")]
                   | _ -> call :: argspp
              in hang 2 (flow (break 1) all) in

          (* Decide whether to unpack an existential result, pack one, or cast.
             To do this we compare the expected type stored in the checked expression
             with the inferred type. *)
          let ret_typ_inst =
               subst_unifiers inst ret_typ
          in
          let packeff,unpack,autocast =
            let ann_typ = Env.expand_synonyms env (general_typ_of_annot (l,annot)) in
            let ann_typ = expand_range_type ann_typ in
            let ret_typ_inst = expand_range_type (Env.expand_synonyms inst_env ret_typ_inst) in
            let ret_typ_inst =
              if is_no_proof_fn env f then ret_typ_inst
              else snd (replace_atom_return_type ret_typ_inst) in
            let () =
              debug ctxt (lazy (" type returned " ^ string_of_typ ret_typ_inst));
              debug ctxt (lazy (" type expected " ^ string_of_typ ann_typ))
            in
            let unpack, in_typ =
              if is_no_proof_fn env f then false, ret_typ_inst else
                match classify_ex_type ctxt inst_env ~rawbools:true ret_typ_inst with
                | ExGeneral, _, t1 -> true,t1
                | ExNone, _, t1 -> false,t1
            in
            let pack,out_typ = 
              match ann_typ with
              | Typ_aux (Typ_exist (_,_,t1),_) -> true,t1
              | t1 -> false,t1
            in
            let autocast =
              (* Avoid using helper functions which simplify the nexps *)
              match in_typ, out_typ with
              | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n1,_);_]),_),
                Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n2,_);_]),_) ->
                 not (similar_nexps ctxt env n1 n2)
              | _ -> false
            in pack,unpack,autocast
          in
          let () =
            debug ctxt (lazy (" packeff: " ^ string_of_bool packeff ^
                              " unpack: " ^ string_of_bool unpack ^
                              " autocast: " ^ string_of_bool autocast))
          in
          let autocast_id, proj_id =
            if effectful eff
            then "autocast_m", "projT1_m"
            else "autocast",   "projT1" in
          (* We need to unpack an existential if it's generated by a pure
             computation, or if the monadic binding isn't expecting one. *)
          let epp = if unpack && not (effectful eff && packeff)
                    then string proj_id ^/^ parens epp
                    else epp in
          let epp = if autocast then string autocast_id ^^ space ^^ parens epp else epp in
          let epp =
            if effectful eff && packeff && not unpack
            then string "build_ex_m" ^^ break 1 ^^ parens epp
            else epp
          in
          liftR (if aexp_needed then parens (align epp) else epp)
       end
    | E_vector_access (v,e) ->
      raise (Reporting.err_unreachable l __POS__
        "E_vector_access should have been rewritten before pretty-printing")
    | E_vector_subrange (v,e1,e2) ->
      raise (Reporting.err_unreachable l __POS__
        "E_vector_subrange should have been rewritten before pretty-printing")
    | E_field((E_aux(_,(l,fannot)) as fexp),id) ->
       (match destruct_tannot fannot with
        | Some(env, (Typ_aux (Typ_id tid, _)), _)
        | Some(env, (Typ_aux (Typ_app (tid, _), _)), _)
          when Env.is_record tid env ->
           let fname =
             if prefix_recordtype && string_of_id tid <> "regstate"
             then (string (string_of_id tid ^ "_")) ^^ doc_id id
             else doc_id id in
           expY fexp ^^ dot ^^ parens fname
        | _ ->
           raise (report l __POS__ "E_field expression with no register or record type"))
    | E_block [] -> string "tt"
    | E_block exps -> raise (report l __POS__ "Blocks should have been removed till now.")
    | E_id id | E_ref id ->
       let env = env_of full_exp in
       let typ = typ_of full_exp in
       let eff = effect_of full_exp in
       let base_typ = Env.base_typ_of env typ in
       if has_effect eff BE_rreg then
         let epp = separate space [string "read_reg"; doc_id id ^^ string "_ref"] in
         if is_bitvector_typ base_typ
         then wrap_parens (align (group (prefix 0 1 (parens (liftR epp)) (doc_tannot ctxt env true base_typ))))
         else liftR epp
       else if Env.is_register id env && is_regtyp typ env then doc_id id ^^ string "_ref"
       else if is_ctor env id then doc_id_ctor id
       else begin
         match Env.lookup_id id env with
         | Local (_,typ) ->
            let exp_typ = expand_range_type (Env.expand_synonyms env typ) in
            let ann_typ = general_typ_of full_exp in
            let ann_typ = expand_range_type (Env.expand_synonyms env ann_typ) in
            let autocast =
              (* Avoid using helper functions which simplify the nexps *)
              match exp_typ, ann_typ with
              | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n1,_);_]),_),
                Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n2,_);_]),_) ->
                 not (similar_nexps ctxt env n1 n2)
              | _ -> false
            in
            let () =
              debug ctxt (lazy ("Variable " ^ string_of_id id ^ " with type " ^ string_of_typ typ));
              debug ctxt (lazy (" expected type " ^ string_of_typ ann_typ));
              debug ctxt (lazy (" autocast " ^ string_of_bool autocast))
            in
            if autocast then
              wrap_parens (string "autocast" ^/^ doc_id id)
            else
              doc_id id
         | _ -> doc_id id
       end
    | E_lit lit -> doc_lit lit
    | E_cast(typ,e) ->
       let env = env_of_annot (l,annot) in
       let outer_typ = Env.expand_synonyms env (general_typ_of_annot (l,annot)) in
       let outer_typ = expand_range_type outer_typ in
       let cast_typ = expand_range_type (Env.expand_synonyms env typ) in
       let inner_typ = Env.expand_synonyms env (typ_of e) in
       let inner_typ = expand_range_type inner_typ in
       let () =
         debug ctxt (lazy ("Cast of type " ^ string_of_typ cast_typ));
         debug ctxt (lazy (" on expr of type " ^ string_of_typ inner_typ));
         debug ctxt (lazy (" where type expected is " ^ string_of_typ outer_typ))
       in
       let epp = expV true e in
       let outer_ex,_,outer_typ' = classify_ex_type ctxt env outer_typ in
       let cast_ex,_,cast_typ' = classify_ex_type ctxt env ~rawbools:true cast_typ in
       let inner_ex,_,inner_typ' = classify_ex_type ctxt env inner_typ in
       let autocast_out =
         (* Avoid using helper functions which simplify the nexps *)
         match outer_typ', cast_typ' with
         | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n1,_);_]),_),
           Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n2,_);_]),_) ->
              not (similar_nexps ctxt env n1 n2)
           | _ -> false
       in
       let autocast_in =
         (* Avoid using helper functions which simplify the nexps *)
         match inner_typ', cast_typ' with
         | Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n1,_);_]),_),
           Typ_aux (Typ_app (Id_aux (Id "bitvector",_),[A_aux (A_nexp n2,_);_]),_) ->
              not (similar_nexps ctxt env n1 n2)
           | _ -> false
       in
       let effects = effectful (effect_of e) in
       (* We don't currently have a version of autocast under existentials,
          but they're rare and may be unnecessary *)
       let autocast_out =
         if effects && outer_ex = ExGeneral then false else autocast_out
       in
       let autocast_in =
         if effects && inner_ex = ExGeneral then false else autocast_in
       in
       let () =
         debug ctxt (lazy (" effectful: " ^ string_of_bool effects ^
                           " outer_ex: " ^ string_of_ex_kind outer_ex ^
                           " cast_ex: " ^ string_of_ex_kind cast_ex ^
                           " inner_ex: " ^ string_of_ex_kind inner_ex ^
                           " autocast_in: " ^ string_of_bool autocast_in ^
                           " autocast_out: " ^ string_of_bool autocast_out))
       in
       let epp =
         if autocast_in then
           string "autocast" ^/^ parens epp
         else
           epp
       in
       let epp =
         if effects then
           match inner_ex, cast_ex with
           | ExGeneral, ExGeneral ->
              (* If the types are the same use the cast as a hint to Coq,
                 otherwise derive the new type from the old one. *)
              if alpha_equivalent env inner_typ cast_typ
              then epp
              else string "derive_m" ^/^ epp
           | ExGeneral, ExNone ->
              string "projT1_m" ^/^ epp
           | ExNone, ExGeneral ->
              string "build_ex_m" ^/^ epp
           | ExNone, ExNone -> epp
         else match cast_ex with
              | ExGeneral -> string "build_ex" ^/^ epp
              | ExNone -> epp
       in
       let epp = epp ^/^ doc_tannot ctxt (env_of e) effects typ in
       let epp =
         if effects then
           match cast_ex, outer_ex with
           | ExGeneral, ExNone -> string "projT1_m" ^/^ parens epp
           | ExGeneral, ExGeneral ->
              if alpha_equivalent env cast_typ outer_typ
              then epp
              else string "derive_m" ^/^ parens epp
           | _ -> epp
         else match cast_ex with
              | ExGeneral -> string "projT1" ^/^ parens epp
              | ExNone -> epp
       in
       let epp =
         if autocast_out then
           string (if effects then "autocast_m" else "autocast") ^^ space ^^ parens epp
         else epp
       in
       if aexp_needed then parens epp else epp
    | E_tuple exps ->
       construct_dep_pairs (env_of_annot (l,annot)) true full_exp (general_typ_of full_exp)
    | E_record fexps ->
       let recordtyp = match destruct_tannot annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _) ->
           (* when Env.is_record tid env -> *)
           tid
         | _ ->  raise (report l __POS__ ("cannot get record type from annot " ^ string_of_tannot annot ^ " of exp " ^ string_of_exp full_exp)) in
       let epp = enclose_record (align (separate_map
                                          (semi_sp ^^ break 1)
                                          (doc_fexp ctxt recordtyp) fexps)) in
       if aexp_needed then parens epp else epp
    | E_record_update(e, fexps) ->
       let recordtyp, env = match destruct_tannot annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _)
           when Env.is_record tid env ->
           tid, env
         | _ ->  raise (report l __POS__ ("cannot get record type from annot " ^ string_of_tannot annot ^ " of exp " ^ string_of_exp full_exp)) in
       if List.length fexps > 1 then
         let _,fields = Env.get_record recordtyp env in
         let var, let_pp =
           match e with
           | E_aux (E_id id,_) -> id, empty
           | _ -> let v = mk_id "_record" in (* TODO: collision avoid *)
                  v, separate space [string "let "; doc_id v; coloneq; top_exp ctxt true e; string "in"] ^^ break 1
         in
         let doc_field (_,id) =
           match List.find (fun (FE_aux (FE_Fexp (id',_),_)) -> Id.compare id id' == 0) fexps with
           | fexp -> doc_fexp ctxt recordtyp fexp
           | exception Not_found ->
               let fname =
                 if prefix_recordtype && string_of_id recordtyp <> "regstate"
                 then (string (string_of_id recordtyp ^ "_")) ^^ doc_id id
                 else doc_id id in
               doc_op coloneq fname (doc_id var ^^ dot ^^ parens fname)
         in let_pp ^^ enclose_record (align (separate_map (semi_sp ^^ break 1)
                                               doc_field fields))
       else
         enclose_record_update (doc_op (string "with") (expY e) (separate_map semi_sp (doc_fexp ctxt recordtyp) fexps))
    | E_vector exps ->
       let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
       let start, (len, order, etyp) =
         if is_vector_typ t || is_bitvector_typ t then vector_start_index t, vector_typ_args_of t
         else raise (Reporting.err_unreachable l __POS__
           "E_vector of non-vector type") in
       let dir,dir_out = if is_order_inc order then (true,"true") else (false, "false") in
       let expspp = align (group (flow_map (semi ^^ break 0) expN exps)) in
       let epp = brackets expspp in
       let (epp,aexp_needed) =
         if is_bitvector_typ t then
           let bepp = string "vec_of_bits" ^^ space ^^ align epp in
           (align (group (prefix 0 1 bepp (doc_tannot ctxt (env_of full_exp) false t))), true)
         else
           let vepp = string "vec_of_list_len" ^^ space ^^ align epp in
           (vepp,aexp_needed) in
       if aexp_needed then parens (align epp) else epp
    | E_vector_update(v,e1,e2) ->
       raise (Reporting.err_unreachable l __POS__
         "E_vector_update should have been rewritten before pretty-printing")
    | E_vector_update_subrange(v,e1,e2,e3) ->
       raise (Reporting.err_unreachable l __POS__
        "E_vector_update should have been rewritten before pretty-printing")
    | E_list exps ->
       brackets (separate_map (semi ^^ break 1) (expN) exps)
    | E_case(e,pexps) ->
       let only_integers e = expY e in
       let epp =
         group ((separate space [string "match"; only_integers e; string "with"]) ^/^
                  (separate_map (break 1) (doc_case ctxt (env_of_annot (l,annot)) (typ_of e)) pexps) ^/^
                    (string "end")) in
       if aexp_needed then parens (align epp) else align epp
    | E_try (e, pexps) ->
       if effectful (effect_of e) then
         let try_catch = if ctxt.early_ret then "try_catchR" else "try_catch" in
         let epp =
           (* TODO capture avoidance for __catch_val *)
           group ((separate space [string try_catch; expY e; string "(fun __catch_val => match __catch_val with "]) ^/^
                    (separate_map (break 1) (doc_case ctxt (env_of_annot (l,annot)) exc_typ) pexps) ^/^
                      (string "end)")) in
         if aexp_needed then parens (align epp) else align epp
       else
         raise (Reporting.err_todo l "Warning: try-block around pure expression")
    | E_throw e ->
       let epp = liftR (separate space [string "throw"; expY e]) in
       if aexp_needed then parens (align epp) else align epp
    | E_exit e -> liftR (separate space [string "exit"; expY e])
    | E_assert (e1,e2) ->
       let epp = liftR (separate space [string "assert_exp"; expY e1; expY e2]) in
       if aexp_needed then parens (align epp) else align epp
    | E_app_infix (e1,id,e2) ->
       raise (Reporting.err_unreachable l __POS__
         "E_app_infix should have been rewritten before pretty-printing")
    | E_var(lexp, eq_exp, in_exp) ->
       raise (report l __POS__ "E_vars should have been removed before pretty-printing")
    | E_internal_plet (pat,e1,e2) ->
       begin
         let () =
           debug ctxt (lazy ("Internal plet, pattern " ^ string_of_pat pat));
           debug ctxt (lazy (" type of e1 " ^ string_of_typ (typ_of e1)))
         in
         let outer_env = env_of_annot (l,annot) in
         let new_ctxt = merge_new_tyvars ctxt outer_env pat (env_of e2) in
         match pat, e1, e2 with
         | (P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _)),
           (E_aux (E_assert (assert_e1,assert_e2),_)), _ ->
             let assert_fn, mid = 
               match assert_constraint outer_env true assert_e1 with
               | Some _ -> "assert_exp'", ">>= fun _ =>"
               | None -> "assert_exp", ">>"
             in
             let epp = liftR (separate space [string assert_fn; expY assert_e1; expY assert_e2]) in
             let epp = infix 0 1 (string mid) epp (top_exp new_ctxt false e2) in
             if aexp_needed then parens (align epp) else align epp
         | _,
           (E_aux (E_if (if_cond,
                         (  E_aux (E_throw _,_)
                          | E_aux (E_block [E_aux (E_throw _,_)],_) as throw_exp),
                   else_exp),_)), _
              when condition_produces_constraint ctxt if_cond ->
            let cond_pp = expY if_cond in
            let throw_pp = expN throw_exp in
            (* Push non-trivial else branches below *)
            let e2 =
              match else_exp with
              | E_aux (E_internal_return (E_aux (E_lit (L_aux (L_unit,_)),_)),_)
              | E_aux (E_internal_return
                         (E_aux (E_cast (_, E_aux (E_lit (L_aux (L_unit,_)),_)),_)),_)
                -> e2
              | _ -> E_aux (E_internal_plet (pat,else_exp,e2),(l,annot))
            in
            (* TODO: capture avoid *)
            let hyp = string "_non_throw_hyp" in
            group (parens (string "match sumbool_of_bool " ^^ space ^^ cond_pp ^^ space ^^ string "with" ^/^
                      group (string "| left _ =>" ^/^ throw_pp) ^/^
                        group (string "| right " ^^ hyp ^^ string " =>" ^/^
                          string "returnm " ^^ hyp) ^/^ string "end")) ^/^
              string " >>= fun _ => " ^/^
                top_exp new_ctxt false e2
         | _ ->
            let epp =
              let middle =
                let env1 = env_of e1 in
                match pat with
                | P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _) ->
                   string ">>"
                | P_aux (P_id id,_)
                   when Util.is_none (is_auto_decomposed_exist ctxt (env_of e1) (typ_of e1)) &&
                        not (is_enum (env_of e1) id) ->
                   separate space [string ">>= fun"; doc_id id; bigarrow]
                | P_aux (P_typ (typ, P_aux (P_id id,_)),_)
                   when Util.is_none (is_auto_decomposed_exist ctxt (env_of e1) typ) &&
                        not (is_enum (env_of e1) id) ->
                   separate space [string ">>= fun"; doc_id id; colon; doc_typ ctxt outer_env typ; bigarrow]
                | P_aux (P_typ (typ, P_aux (P_id id,_)),_)
                | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id,_),_),_)),_)
                | P_aux (P_var (P_aux (P_typ (typ, P_aux (P_id id,_)),_),_),_)
                    when not (is_enum env1 id) ->
                      let full_typ = (expand_range_type typ) in
                      let binder = match classify_ex_type ctxt env1 (Env.expand_synonyms env1 full_typ) with
                        | ExGeneral, _, _ ->
                           squote ^^ parens (separate space [string "existT"; underscore; doc_id id; underscore; colon; doc_typ ctxt outer_env typ])
                        | ExNone, _, _ ->
                           parens (separate space [doc_id id; colon; doc_typ ctxt outer_env typ])
                      in separate space [string ">>= fun"; binder; bigarrow]
                | P_aux (P_id id,_) ->
                   let typ = typ_of e1 in
                   (* Ideally we'd drop the parens and the squote when possible, but it's
                      easier to keep both, and avoids clashes with 'b"..." bitvector literals. *)
                   let plain_binder = squote ^^ parens (doc_pat ctxt false true (pat, typ_of e1)) in
                   let binder = match classify_ex_type ctxt env1 ~binding:id (Env.expand_synonyms env1 typ) with
                     | ExGeneral, _, (Typ_aux (Typ_app (Id_aux (Id "atom_bool",_),_),_) as typ') ->
                         squote ^^ parens (separate space [string "existT"; underscore; doc_id id; underscore; colon; doc_typ ctxt outer_env typ])
                     | ExNone, _, typ' -> begin
                        match typ' with
                        | Typ_aux (Typ_app (Id_aux (Id "atom_bool",_),_),_) ->
                           squote ^^ parens (separate space [string "existT"; underscore; doc_id id; underscore; colon; doc_typ ctxt outer_env typ])
                        | _ -> plain_binder
                       end
                     | _ -> plain_binder
                   in separate space [string ">>= fun"; binder; bigarrow]
                | P_aux (P_typ (typ, pat'),_) ->
                   separate space [string ">>= fun"; squote ^^ parens (doc_pat ctxt true true (pat, typ_of e1) ^/^ colon ^^ space ^^ doc_typ ctxt outer_env typ); bigarrow]
                | _ ->
                   separate space [string ">>= fun"; squote ^^ parens (doc_pat ctxt false true (pat, typ_of e1)); bigarrow]
              in
              let e1_pp = expY e1 in
              let e2_pp = top_exp new_ctxt false e2 in
              infix 0 1 middle e1_pp e2_pp
            in
            if aexp_needed then parens (align epp) else epp
       end
    | E_internal_return (e1) ->
       let exp_typ = typ_of e1 in
       let ret_typ = general_typ_of full_exp in
       let () =
         debug ctxt (lazy ("Monad return of " ^ string_of_exp e1));
         debug ctxt (lazy (" with type " ^ string_of_typ exp_typ));
         debug ctxt (lazy (" at type " ^ string_of_typ ret_typ))
       in
       let valpp =
         let env = env_of e1 in
         construct_dep_pairs env true e1 ret_typ ~rawbools:true
       in
       if ctxt.early_ret then
         wrap_parens (group (align (separate space [string "returnR"; parens ctxt.ret_typ_pp; valpp])))
       else
         wrap_parens (group (align (separate space [string "returnM"; valpp])))
    | E_sizeof nexp ->
      (match nexp_simp nexp with
        | Nexp_aux (Nexp_constant i, _) -> doc_lit (L_aux (L_num i, l))
        | _ ->
          raise (Reporting.err_unreachable l __POS__
            "pretty-printing non-constant sizeof expressions to Lem not supported"))
    | E_return r ->
      let ret_monad = " : MR" in
      let exp_pp =
        match ctxt.build_at_return with
        | Some s -> parens (string s ^/^ expY r)
        | None -> expY r
      in
      let ta =
        if contains_t_pp_var ctxt (typ_of full_exp) || contains_t_pp_var ctxt (typ_of r)
        then empty
        else separate space
          [string ret_monad;
          parens (doc_typ ctxt (env_of full_exp) (typ_of full_exp));
          parens (doc_typ ctxt (env_of full_exp) (typ_of r))] in
      align (parens (string "early_return" ^//^ exp_pp ^//^ ta))
    | E_constraint nc -> wrap_parens (doc_nc_exp ctxt (env_of full_exp) nc)
    | E_internal_value _ ->
      raise (Reporting.err_unreachable l __POS__
        "unsupported internal expression encountered while pretty-printing")
  and if_exp ctxt (elseif : bool) c t e =
    let if_pp = string (if elseif then "else if" else "if") in
    let use_sumbool = condition_produces_constraint ctxt c in
    let c_pp = top_exp ctxt use_sumbool c in
    let t_pp = top_exp ctxt false t in
    let else_pp = match e with
      | E_aux (E_if (c', t', e'), _)
      | E_aux (E_cast (_, E_aux (E_if (c', t', e'), _)), _) ->
         if_exp ctxt true c' t' e'
      (* Special case to prevent current arm decoder becoming a staircase *)
      (* TODO: replace with smarter pretty printing *)
      | E_aux (E_internal_plet (pat,exp1,E_aux (E_cast (typ, (E_aux (E_if (_, _, _), _) as exp2)),_)),ann) when Typ.compare typ unit_typ == 0 ->
         string "else" ^/^ top_exp ctxt false (E_aux (E_internal_plet (pat,exp1,exp2),ann))
      | _ -> prefix 2 1 (string "else") (top_exp ctxt false e)
    in
    (prefix 2 1
      (soft_surround 2 1 if_pp
         (if use_sumbool then string "sumbool_of_bool" ^/^ c_pp else c_pp)
         (string "then"))
      t_pp) ^^
    break 1 ^^
    else_pp
  and let_exp ctxt (LB_aux(lb,_)) = match lb with
    (* Prefer simple lets over patterns, because I've found Coq can struggle to
       work out return types otherwise *)
    | LB_val(P_aux (P_id id,_),e)
      when not (is_enum (env_of e) id) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; coloneq])
              (top_exp ctxt false e)
    | LB_val(P_aux (P_typ (typ,P_aux (P_id id,_)),_),e)
      when Util.is_none (is_auto_decomposed_exist ctxt (env_of e) ~rawbools:true typ) &&
           not (is_enum (env_of e) id) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; colon; doc_typ ctxt (env_of e) typ; coloneq])
              (top_exp ctxt false e)
    | (LB_val(P_aux (P_typ (_,P_aux (P_id id,_)),_),e)
       | LB_val(P_aux (P_var (P_aux (P_id id,_),_),_), e)
       | LB_val(P_aux (P_typ (_,P_aux (P_var (P_aux (P_id id,_),_),_)),_), e))
      when (* is auto decomposed *)
           not (is_enum (env_of e) id) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; coloneq])
              (top_exp ctxt false e)
    | LB_val(P_aux (P_typ (typ,pat),_),(E_aux (_,e_ann) as e)) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true false (pat, typ); coloneq])
              (top_exp ctxt false (E_aux (E_cast (typ,e),e_ann)))
    | LB_val(pat,e) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true false (pat, typ_of e); coloneq])
              (top_exp ctxt false e)

  and doc_fexp ctxt recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype && string_of_id recordtyp <> "regstate"
      then (string (string_of_id recordtyp ^ "_")) ^^ doc_id id
      else doc_id id in
    group (doc_op coloneq fname (top_exp ctxt true e))

  and doc_case ctxt old_env typ = function
  | Pat_aux(Pat_exp(pat,e),_) ->
     let new_ctxt = merge_new_tyvars ctxt old_env pat (env_of e) in
     group (prefix 3 1 (separate space [pipe; doc_pat ctxt false false (pat,typ);bigarrow])
              (group (top_exp new_ctxt false e)))
  | Pat_aux(Pat_when(_,_,_),(l,_)) ->
    raise (Reporting.err_unreachable l __POS__
     "guarded pattern expression should have been rewritten before pretty-printing")

  and doc_lexp_deref ctxt ((LEXP_aux(lexp,(l,annot)))) = match lexp with
    | LEXP_field (le,id) ->
       parens (separate empty [doc_lexp_deref ctxt le;dot;doc_id id])
    | LEXP_id id -> doc_id id ^^ string "_ref"
    | LEXP_cast (typ,id) -> doc_id id ^^ string "_ref"
    | LEXP_tup lexps -> parens (separate_map comma_sp (doc_lexp_deref ctxt) lexps)
    | _ ->
       raise (Reporting.err_unreachable l __POS__ ("doc_lexp_deref: Unsupported lexp"))
             (* expose doc_exp and doc_let *)
  in top_exp, let_exp

(* FIXME: A temporary definition of List.init until 4.06 is more standard *)
let list_init n f = Array.to_list (Array.init n f)

let types_used_with_generic_eq defs =
  let rec add_typ idset (Typ_aux (typ,_)) =
    match typ with
    | Typ_id id -> IdSet.add id idset
    | Typ_app (id,args) ->
       List.fold_left add_typ_arg (IdSet.add id idset) args
    | Typ_tup ts -> List.fold_left add_typ idset ts
    | _ -> idset
  and add_typ_arg idset (A_aux (ta,_)) =
    match ta with
    | A_typ typ -> add_typ idset typ
    | _ -> idset
  in
  let alg =
    { (Rewriter.compute_exp_alg IdSet.empty IdSet.union) with
      Rewriter.e_aux = fun ((typs,exp),annot) ->
        let typs' =
          match exp with
          | E_app (f,[arg1;_]) ->
             if Env.is_extern f (env_of_annot annot) "coq" then
               let f' = Env.get_extern f (env_of_annot annot) "coq" in
               if f' = "generic_eq" || f' = "generic_neq" then
                 add_typ typs (Env.expand_synonyms (env_of arg1) (typ_of arg1))
               else typs
             else typs
          | _ -> typs
        in typs', E_aux (exp,annot) }
  in
  let typs_req_funcl (FCL_aux (FCL_Funcl (_,pexp), _)) =
    fst (Rewriter.fold_pexp alg pexp)
  in
  let typs_req_fundef (FD_aux (FD_function (_,_,_,fcls),_)) =
    List.fold_left IdSet.union IdSet.empty (List.map typs_req_funcl fcls)
  in
  let rec typs_req_def = function
    | DEF_type _
    | DEF_spec _
    | DEF_fixity _
    | DEF_overload _
    | DEF_default _
    | DEF_pragma _
    | DEF_reg_dec _
      -> IdSet.empty
    | DEF_fundef fd -> typs_req_fundef fd
    | DEF_mapdef (MD_aux (_,(l,_)))
    | DEF_scattered (SD_aux (_,(l,_)))
    | DEF_measure (Id_aux (_,l),_,_)
    | DEF_loop_measures (Id_aux (_,l),_)
      -> unreachable l __POS__
           "Definition found in the Coq back-end that should have been rewritten away"
    | DEF_internal_mutrec fds ->
       List.fold_left IdSet.union IdSet.empty (List.map typs_req_fundef fds)
    | DEF_val lb ->
       fst (Rewriter.fold_letbind alg lb)
  in
  List.fold_left IdSet.union IdSet.empty (List.map typs_req_def defs)

let doc_type_union ctxt typ_name (Tu_aux(Tu_ty_id(typ,id),_)) =
  separate space [doc_id_ctor id; colon;
                  doc_typ ctxt Env.empty typ; arrow; typ_name]

(* For records and variants we declare the type parameters as implicit
   so that they're implicit in the constructors.  Currently Coq also
   makes them implicit in the type, so undo that here. *)
let doc_reset_implicits id_pp typq =
  let (kopts,ncs) = quant_split typq in
  let resets = List.map (fun _ -> underscore) kopts in
  let implicits = List.map (fun _ -> string "{_}") ncs in
  let args = match implicits with
    | [] -> [colon; string "clear implicits"]
    | _ -> resets @ implicits
  in
  separate space ([string "Arguments"; id_pp] @ args) ^^ dot

(*
let rec doc_range ctxt (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_nexp ctxt i) (doc_nexp ctxt i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_nexp ctxt i1) (doc_nexp ctxt i2))
  | BF_concat(ir1,ir2) -> (doc_range ctxt ir1) ^^ comma ^^ (doc_range ctxt ir2)
 *)

(* TODO: check use of empty_ctxt below *)
let doc_typdef types_mod generic_eq_types (TD_aux(td, (l, annot))) =
  match td with
  | TD_abbrev(id,typq,A_aux (A_typ typ, _)) ->
     let typschm = TypSchm_aux (TypSchm_ts (typq, typ), l) in
     doc_op coloneq
       (separate space [string "Definition"; doc_id_type types_mod None id;
                        doc_typquant_items empty_ctxt Env.empty parens typq;
                        colon; string "Type"])
       (doc_typschm empty_ctxt Env.empty false typschm) ^^ dot ^^ twice hardline
  | TD_abbrev(id,typq,A_aux (A_nexp nexp,_)) ->
     let idpp = doc_id_type types_mod None id in
     doc_op coloneq
       (separate space [string "Definition"; idpp;
                        doc_typquant_items empty_ctxt Env.empty parens typq;
                        colon; string "Z"])
       (doc_nexp empty_ctxt nexp) ^^ dot ^^ hardline ^^
     separate space [string "Hint Unfold"; idpp; colon; string "sail."] ^^
     twice hardline
  | TD_abbrev(id,typq,A_aux (A_bool nc,_)) ->
     let idpp = doc_id_type types_mod None id in
     doc_op coloneq
       (separate space [string "Definition"; idpp;
                        doc_typquant_items empty_ctxt Env.empty parens typq;
                        colon; string "bool"])
       (doc_nc_exp empty_ctxt Env.empty nc) ^^ dot ^^ hardline ^^
     separate space [string "Hint Unfold"; idpp; colon; string "sail."] ^^
     twice hardline
  | TD_abbrev _ -> empty (* TODO? *)
  | TD_bitfield _ -> empty (* TODO? *)
  | TD_record(id,typq,fs,_) ->
    let fname fid = if prefix_recordtype && string_of_id id <> "regstate"
                    then concat [doc_id id;string "_";doc_id_type types_mod None fid;]
                    else doc_id_type types_mod None fid in
    let f_pp (typ,fid) =
      concat [fname fid;space;colon;space;doc_typ empty_ctxt Env.empty typ; semi] in
    let rectyp = match typq with
      | TypQ_aux (TypQ_tq qs, _) ->
        let quant_item = function
          | QI_aux (QI_id (KOpt_aux (KOpt_kind (_, kid), _)), l) ->
            [A_aux (A_nexp (Nexp_aux (Nexp_var kid, l)), l)]
          | _ -> [] in
        let targs = List.concat (List.map quant_item qs) in
        mk_typ (Typ_app (id, targs))
      | TypQ_aux (TypQ_no_forall, _) -> mk_id_typ id in
    let fs_doc = group (separate_map (break 1) f_pp fs) in
    let type_id_pp = doc_id_type types_mod None id in
    let match_parameters =
      let (kopts,_) = quant_split typq in
      match kopts with
      | [] -> empty
      | _ -> space ^^ separate_map space (fun _ -> underscore) kopts
    in
    let doc_update_field (_,fid) =
      let idpp = fname fid in
      let pp_field alt i (_,fid') =
        if Id.compare fid fid' == 0 then string alt else
          let id = "f" ^ string_of_int i in
          string id
      in
      match fs with
      | [_] ->
         string "Notation \"{[ r 'with' '" ^^ idpp ^^ string "' := e ]}\" :=" ^//^
           string "{| " ^^ idpp ^^ string " := e |} (only parsing)."
      | _   ->
         string "Notation \"{[ r 'with' '" ^^ idpp ^^ string "' := e ]}\" :=" ^//^
           string "match r with Build_" ^^ type_id_pp ^^ match_parameters ^^ space ^^ separate space (List.mapi (pp_field "_") fs) ^^ string " =>" ^//^
           string "Build_" ^^ type_id_pp ^^ match_parameters ^^ space ^^ separate space (List.mapi (pp_field "e") fs) ^//^
             string "end" ^^ dot
    in
    let updates_pp = separate hardline (List.map doc_update_field fs) in
    let numfields = List.length fs in
    let intros_pp s =
      string " intros [" ^^
      separate space (list_init numfields (fun n -> string (s ^ string_of_int n))) ^^
      string "]." ^^ hardline
    in
    let eq_pp =
      if IdSet.mem id generic_eq_types then
        string "Instance Decidable_eq_" ^^ type_id_pp ^^ space ^^ colon ^/^
        string "forall (x y : " ^^ type_id_pp ^^ string "), Decidable (x = y)." ^^
        hardline ^^ intros_pp "x" ^^ intros_pp "y" ^^
        separate hardline (list_init numfields
                             (fun n ->
                               let ns = string_of_int n in
                               string ("cmp_record_field x" ^ ns ^ " y" ^ ns ^ "."))) ^^
        hardline ^^
        string "refine (Build_Decidable _ true _). subst. split; reflexivity." ^^ hardline ^^
        string "Defined." ^^ twice hardline
      else empty
    in
    let reset_implicits_pp = doc_reset_implicits type_id_pp typq in
    doc_op coloneq
           (separate space [string "Record"; type_id_pp; doc_typquant_items empty_ctxt Env.empty braces typq])
           ((*doc_typquant typq*) (braces (space ^^ align fs_doc ^^ space))) ^^
      dot ^^ hardline ^^ reset_implicits_pp ^^ hardline ^^ eq_pp ^^ updates_pp ^^
        twice hardline
  | TD_variant(id,typq,ar,_) ->
     (match id with
      | Id_aux ((Id "read_kind"),_) -> empty
      | Id_aux ((Id "write_kind"),_) -> empty
      | Id_aux ((Id "barrier_kind"),_) -> empty
      | Id_aux ((Id "trans_kind"),_) -> empty
      | Id_aux ((Id "instruction_kind"),_) -> empty
      (* | Id_aux ((Id "regfp"),_) -> empty
      | Id_aux ((Id "niafp"),_) -> empty
      | Id_aux ((Id "diafp"),_) -> empty *)
      | Id_aux ((Id "option"),_) -> empty
      | _ ->
         let id_pp = doc_id_type types_mod None id in
         let typ_nm = separate space [id_pp; doc_typquant_items empty_ctxt Env.empty braces typq] in
         let ar_doc = group (separate_map (break 1) (fun x -> pipe ^^ space ^^ doc_type_union empty_ctxt id_pp x) ar) in
         let typ_pp =
           (doc_op coloneq)
             (concat [string "Inductive"; space; typ_nm])
             ((*doc_typquant typq*) ar_doc) in
         let reset_implicits_pp = doc_reset_implicits id_pp typq in
         let doc_dec_eq_req = function
           | QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_type,_),kid),_)),_) ->
              (* TODO: collision avoidance for x y *)
              Some (string "`{forall x y : " ^^ doc_var empty_ctxt kid ^^ string ", Decidable (x = y)}")
           | _ -> None
         in
         let eq_pp =
           if IdSet.mem id generic_eq_types then
             let typ_use_pp =
               separate space (id_pp::Util.map_filter (quant_item_id_name empty_ctxt) (quant_items typq))
             in
             let eq_reqs_pp =
               separate (break 1) (Util.map_filter doc_dec_eq_req (quant_items typq))
             in
             string "Instance Decidable_eq_" ^^ typ_nm ^^ space ^^ eq_reqs_pp ^^ colon ^/^
               string "forall (x y : " ^^ typ_use_pp ^^ string "), Decidable (x = y)." ^^ hardline ^^
                 string "refine (Decidable_eq_from_dec (fun x y => _))." ^^ hardline ^^
                   string "decide equality; refine (generic_dec _ _)." ^^ hardline ^^
                     string "Defined." ^^ hardline
           else empty
         in
         typ_pp ^^ dot ^^ hardline ^^ reset_implicits_pp ^^ hardline ^^ eq_pp ^^ hardline)
  | TD_enum(id,enums,_) ->
     (match id with
      | Id_aux ((Id "read_kind"),_) -> empty
      | Id_aux ((Id "write_kind"),_) -> empty
      | Id_aux ((Id "a64_barrier_domain"),_) -> empty
      | Id_aux ((Id "a64_barrier_type"),_) -> empty
      | Id_aux ((Id "barrier_kind"),_) -> empty
      | Id_aux ((Id "trans_kind"),_) -> empty
      | Id_aux ((Id "instruction_kind"),_) -> empty
      | Id_aux ((Id "regfp"),_) -> empty
      | Id_aux ((Id "niafp"),_) -> empty
      | Id_aux ((Id "diafp"),_) -> empty
      | _ ->
         let enums_doc = group (separate_map (break 1 ^^ pipe ^^ space) doc_id_ctor enums) in
         let id_pp = doc_id_type types_mod None id in
         let typ_pp = (doc_op coloneq)
                        (concat [string "Inductive"; space; id_pp])
                        (enums_doc) in
         let eq1_pp = string "Scheme Equality for" ^^ space ^^ id_pp ^^ dot in
         let eq2_pp = string "Instance Decidable_eq_" ^^ id_pp ^^ space ^^ colon ^/^
           string "forall (x y : " ^^ id_pp ^^ string "), Decidable (x = y) :=" ^/^
           string "Decidable_eq_from_dec " ^^ id_pp ^^ string "_eq_dec." in
          typ_pp ^^ dot ^^ hardline ^^ eq1_pp ^^ hardline ^^ eq2_pp ^^ twice hardline)

let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    (P_aux (P_id id, (l, mk_tannot env typ no_effect)), typ),
    E_aux (E_id id, (l, mk_tannot env typ no_effect)) in
  List.split (List.mapi arg typs)

(* Sail currently has a single pattern to match against a list of
   argument types.  We need to tweak everything to match up,
   especially so that the function is presented in curried form.  In
   particular, if there's a single binder for multiple arguments
   (which rewriting can currently introduce) then we need to turn it
   into multiple binders and reconstruct it in the function body. *)
let rec untuple_args_pat typs (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let identity = (fun body -> body) in
  match paux, typs with
  | P_tup [], _ ->
     let annot = (l, mk_tannot Env.empty unit_typ no_effect) in
     [P_aux (P_lit (mk_lit L_unit), annot), unit_typ], identity
  | P_tup pats, _ -> List.combine pats typs, identity
  | P_wild, _ ->
     let wild typ = P_aux (P_wild, (l, mk_tannot env typ no_effect)), typ in
     List.map wild typs, identity
  | P_typ (_, pat), _ -> untuple_args_pat typs pat
  | P_as _, _::_::_ | P_id _, _::_::_ ->
     let argpats, argexps = args_of_typ l env typs in
     let argexp = E_aux (E_tuple argexps, annot) in
     let bindargs (E_aux (_, bannot) as body) =
       E_aux (E_let (LB_aux (LB_val (pat, argexp), annot), body), bannot) in
     argpats, bindargs
  | _, [typ] ->
     [pat,typ], identity
  | _, _ ->
     unreachable l __POS__ "Unexpected pattern/type combination"

let doc_fun_body ctxt exp =
  let doc_exp = doc_exp ctxt false exp in
  if ctxt.early_ret
  then align (string "catch_early_return" ^//^ parens (doc_exp))
  else doc_exp

(* Coq doesn't support "as" patterns well in Definition binders, so we push
   them over to the r.h.s. of the := *)
let demote_as_pattern i (P_aux (_,p_annot) as pat,typ) =
  let open Rewriter in
  if fst (fold_pat ({ (compute_pat_alg false (||)) with p_as = (fun ((_,p),id) -> true, P_as (p,id)) }) pat)
  then
    let id = mk_id ("arg" ^ string_of_int i) in (* TODO: name conflicts *)
    (P_aux (P_id id, p_annot),typ),
    fun (E_aux (_,e_ann) as e) ->
      E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_id id, p_annot)),p_annot),e),e_ann)
  else (pat,typ), fun e -> e

let pat_is_plain_binder env (P_aux (p,_)) =
  match p with
  | P_id id
  | P_typ (_,P_aux (P_id id,_))
  when not (is_enum env id) -> Some (Some id)
  | P_wild -> Some None
  | _ -> None

let demote_all_patterns env i (P_aux (p,p_annot) as pat,typ) =
  match pat_is_plain_binder env pat with
  | Some id ->
     if Util.is_none (is_auto_decomposed_exist empty_ctxt env typ)
     then (pat,typ), fun e -> e
     else begin
       match id with
       | Some id ->
          (P_aux (P_id id, p_annot),typ),
          fun (E_aux (_,e_ann) as e) ->
          E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_id id, p_annot)),p_annot),e),e_ann)
       | None -> (P_aux (P_wild, p_annot),typ), fun e -> e
       end
  | None ->
    let id = mk_id ("arg" ^ string_of_int i) in (* TODO: name conflicts *)
    (P_aux (P_id id, p_annot),typ),
    fun (E_aux (_,e_ann) as e) ->
      E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_id id, p_annot)),p_annot),e),e_ann)

(* Add equality constraints between arguments and nexps, except in the case
   that they've been merged. *)

let rec atom_constraint ctxt (pat, typ) =
  let typ = Env.base_typ_of (env_of_pat pat) typ in
  match pat, typ with
  | P_aux (P_id id, _),
      Typ_aux (Typ_app (Id_aux (Id "atom",_),
                        [A_aux (A_nexp nexp,_)]),_) ->
     (match nexp with
       (* When the kid is mapped to the id, we don't need a constraint *)
     | Nexp_aux (Nexp_var kid,_)
         when (try Id.compare (Util.option_get_exn Not_found (KBindings.find kid ctxt.kid_id_renames)) id == 0 with _ -> false) ->
           None
     | _ ->
        Some (bquote ^^ braces (string "ArithFact" ^^ space ^^
                                  parens (doc_op (string "=?") (doc_id id) (doc_nexp ctxt nexp)))))
  | P_aux (P_typ (_,p),_), _ -> atom_constraint ctxt (p, typ)
  | _ -> None

let all_ids pexp =
  let open Rewriter in
  fold_pexp (
    { (pure_exp_alg IdSet.empty IdSet.union) with
      e_id = (fun id -> IdSet.singleton id);
      e_ref = (fun id -> IdSet.singleton id);
      e_app = (fun (id,ids) ->
        List.fold_left IdSet.union (IdSet.singleton id) ids);
      e_app_infix = (fun (ids1,id,ids2) ->
        IdSet.add id (IdSet.union ids1 ids2));
      e_for = (fun (id,ids1,ids2,ids3,_,ids4) ->
        IdSet.add id (IdSet.union ids1 (IdSet.union ids2 (IdSet.union ids3 ids4))));
      lEXP_id = IdSet.singleton;
      lEXP_memory = (fun (id,ids) ->
        List.fold_left IdSet.union (IdSet.singleton id) ids);
      lEXP_cast = (fun (_,id) -> IdSet.singleton id);
      pat_alg = { (pure_pat_alg IdSet.empty IdSet.union) with
        p_as = (fun (ids,id) -> IdSet.add id ids);
        p_id = IdSet.singleton;
        p_app = (fun (id,ids) ->
          List.fold_left IdSet.union (IdSet.singleton id) ids);
      }
    }) pexp

let tyvars_of_typquant (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_no_forall -> KidSet.empty
  | TypQ_tq qs -> List.fold_left KidSet.union KidSet.empty
     (List.map tyvars_of_quant_item qs)

let mk_kid_renames ids_to_avoid kids =
  let map_id = function
    | Id_aux (Id i, _) -> Some (fix_id false i)
    | Id_aux (Operator _, _) -> None
  in
  let ids = StringSet.of_list (Util.map_filter map_id (IdSet.elements ids_to_avoid)) in
  let rec check_kid kid (newkids,rebindings) =
    let rec check kid1 =
      let kid_string = fix_id true (string_of_kid kid1) in
      if StringSet.mem kid_string ids
      then let kid2 = match kid1 with Kid_aux (Var x,l) -> Kid_aux (Var (x ^ "0"),l) in
           check kid2
      else
        KidSet.add kid1 newkids, KBindings.add kid kid1 rebindings
    in check kid
  in snd (KidSet.fold check_kid kids (kids, KBindings.empty))

let merge_kids_atoms pats =
  let try_eliminate (acc,gone,map,seen) (pat,typ) =
    let tryon maybe_id env typ =
      let merge kid l =
        if KidSet.mem kid seen then
          let () =
            Reporting.print_err l "merge_kids_atoms"
              ("want to merge tyvar and argument for " ^ string_of_kid kid ^
                 " but rearranging arguments isn't supported yet") in
          (pat,typ)::acc,gone,map,seen
        else
          let pat,id = match maybe_id with
            | Some id -> pat,id
                       (* TODO: name clashes *)
            | None -> let id = id_of_kid kid in
                      P_aux (P_id id,match pat with P_aux (_,ann) -> ann), id
          in
          (pat,typ)::acc,
          KidSet.add kid gone, KBindings.add kid (Some id) map, KidSet.add kid seen
      in
      match Type_check.destruct_atom_nexp env typ with
      | Some (Nexp_aux (Nexp_var kid,l)) -> merge kid l
      | _ ->
         match Type_check.destruct_atom_bool env typ with
         | Some (NC_aux (NC_var kid,l)) -> merge kid l
         | _ -> (pat,typ)::acc,gone,map,KidSet.union seen (tyvars_of_typ typ)
    in
    match pat,typ with
    | P_aux (P_id id, ann), typ
    | P_aux (P_typ (_,P_aux (P_id id, ann)),_), typ ->
       tryon (Some id) (env_of_annot ann) typ
    | P_aux (P_wild, ann), typ ->
       tryon None (env_of_annot ann) typ
    | _ -> (pat,typ)::acc,gone,map,KidSet.union seen (tyvars_of_typ typ)
  in
  let r_pats,gone,map,_ = List.fold_left try_eliminate ([],KidSet.empty, KBindings.empty, KidSet.empty) pats in
  List.rev r_pats,gone,map


let merge_var_patterns map pats =
  let map,pats = List.fold_left (fun (map,pats) (pat, typ) ->
    match pat with
    | P_aux (P_var (P_aux (P_id id,_), TP_aux (TP_var kid,_)),ann) ->
       KBindings.add kid (Some id) map, (P_aux (P_id id,ann), typ) :: pats
    | _ -> map, (pat,typ)::pats) (map,[]) pats
  in map, List.rev pats

type mutrec_pos = NotMutrec | FirstFn | LaterFn

let doc_funcl_init types_mod mutrec rec_opt ?rec_set (FCL_aux(FCL_Funcl(id, pexp), annot)) =
  let env = env_of_annot annot in
  let (tq,typ) = Env.get_val_spec_orig id env in
  let (arg_typs, ret_typ, eff) = match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ, eff),_) -> arg_typs, ret_typ, eff
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  let ids_to_avoid = all_ids pexp in
  let bound_kids = tyvars_of_typquant tq in
  let pat,guard,exp,(l,_) = destruct_pexp pexp in
  let pats, bind = untuple_args_pat arg_typs pat in
  (* Fixpoint definitions can only use simple binders, but even Definitions
     can't handle as patterns *)
  let pattern_elim =
    match rec_opt with
    | Rec_aux (Rec_nonrec,_) -> demote_as_pattern
    | _ -> demote_all_patterns env
  in
  let pats, binds = List.split (Util.list_mapi pattern_elim pats) in
  let pats, eliminated_kids, kid_to_arg_rename = merge_kids_atoms pats in
  let kid_to_arg_rename, pats = merge_var_patterns kid_to_arg_rename pats in
  let kids_used = KidSet.diff bound_kids eliminated_kids in
  let is_measured = match rec_opt with
    | Rec_aux (Rec_measure _,_) -> true
    | _ -> false
  in
  let kir_rev =
    KBindings.fold
      (fun kid idopt m -> match idopt with Some id -> Bindings.add id kid m | None -> m)
      kid_to_arg_rename Bindings.empty
  in
  let ctxt0 =
    { types_mod = types_mod;
      early_ret = contains_early_return exp;
      kid_renames = mk_kid_renames ids_to_avoid kids_used;
      kid_id_renames = kid_to_arg_rename;
      kid_id_renames_rev = kir_rev;
      bound_nvars = bound_kids;
      build_at_return = None; (* filled in below *)
      recursive_fns = Bindings.empty; (* filled in later *)
      debug = List.mem (string_of_id id) (!opt_debug_on);
      ret_typ_pp = PPrint.empty; (* filled in below *)
    } in
  let build_ex, ret_typ = replace_atom_return_type ret_typ in
  let build_ex = match classify_ex_type ctxt0 env (Env.expand_synonyms env (expand_range_type ret_typ)) with
    | ExGeneral, _, _ -> Some "build_ex"
    | ExNone, _, _ -> build_ex
  in
  let ctxt = { ctxt0 with
      build_at_return = if effectful eff then build_ex else None;
      ret_typ_pp = doc_typ ctxt0 Env.empty ret_typ
             } in
  let () =
    debug ctxt (lazy ("Function " ^ string_of_id id));
    debug ctxt (lazy (" return type " ^ string_of_typ ret_typ));
    debug ctxt (lazy (" build_ex " ^ match build_ex with Some s -> s ^ " needed" | _ -> "not needed"));
    debug ctxt (lazy (if effectful eff then " effectful" else " pure"));
    debug ctxt (lazy (" kid_id_renames " ^ String.concat ", " (List.map
                        (fun (kid,id) -> string_of_kid kid ^ " |-> " ^ 
                                           match id with Some id -> string_of_id id | None -> "<>")
                        (KBindings.bindings kid_to_arg_rename))))
  in
  (* Put the constraints after pattern matching so that any type variable that's
     been replaced by one of the term-level arguments is bound. *)
  let quantspp, constrspp = doc_typquant_items_separate ctxt env braces tq in
  let exp = List.fold_left (fun body f -> f body) (bind exp) binds in
  let used_a_pattern = ref false in
  let doc_binder (P_aux (p,ann) as pat, typ) =
    let env = env_of_annot ann in
    let exp_typ = Env.expand_synonyms env typ in
    let () =
      debug ctxt (lazy (" pattern " ^ string_of_pat pat));
      debug ctxt (lazy (" with expanded type " ^ string_of_typ exp_typ))
    in
    (* TODO: probably should provide partial environments to doc_typ *)
    match pat_is_plain_binder env pat with
    | Some id -> begin
       let id_pp = match id with Some id -> doc_id id | None -> underscore in
       match classify_ex_type ctxt env ?binding:id exp_typ with
       | ExNone, _, typ' ->
         parens (separate space [id_pp; colon; doc_typ ctxt Env.empty typ'])
       | ExGeneral, _, _ ->
           let full_typ = (expand_range_type exp_typ) in
           match destruct_exist_plain (Env.expand_synonyms env full_typ) with
           | Some ([kopt], NC_aux (NC_true,_),
                   Typ_aux (Typ_app (Id_aux (Id ("atom" | "atom_bool" as tyname),_),
                                     [A_aux (A_nexp (Nexp_aux (Nexp_var kid,_)),_)]),_))
               when Kid.compare (kopt_kid kopt) kid == 0 ->
              let coqty = if tyname = "atom" then "Z" else "bool" in
              parens (separate space [id_pp; colon; string coqty])
           | Some ([kopt], nc,
                   Typ_aux (Typ_app (Id_aux (Id ("atom" | "atom_bool"),_),
                                     [A_aux (A_nexp (Nexp_aux (Nexp_var kid,_)),_)]),_))
               when Kid.compare (kopt_kid kopt) kid == 0 && not is_measured ->
              (used_a_pattern := true;
               squote ^^ parens (separate space [string "existT"; underscore; id_pp; underscore; colon; doc_typ ctxt Env.empty typ]))
           | _ ->
              parens (separate space [id_pp; colon; doc_typ ctxt Env.empty typ])
         end
    | None ->
       let typ =
         match classify_ex_type ctxt env ~binding:id exp_typ with
         | ExNone, _, typ' -> typ'
       | ExGeneral, _, _ -> typ
       in
       (used_a_pattern := true;
        squote ^^ parens (separate space [doc_pat ctxt true true (pat, exp_typ); colon; doc_typ ctxt Env.empty typ]))
  in
  let patspp = flow_map (break 1) doc_binder pats in
  let atom_constrs = Util.map_filter (atom_constraint ctxt) pats in
  let retpp =
    (* TODO: again, probably should provide proper environment *)
    if effectful eff
    then string "M" ^^ space ^^ parens ctxt.ret_typ_pp
    else doc_typ ctxt Env.empty ret_typ
  in
  let idpp = doc_id id in
  let intropp, accpp, measurepp, fixupspp = match rec_opt with
    | Rec_aux (Rec_measure _,_) ->
       let fixupspp =
         Util.map_filter (fun (pat,typ) ->
             match pat_is_plain_binder env pat with
             | Some (Some id) -> begin
                 match destruct_exist_plain (Env.expand_synonyms env (expand_range_type typ)) with
                 | Some (_, NC_aux (NC_true,_), _) -> None
                 | Some ([KOpt_aux (KOpt_kind (_, kid), _)], nc,
                         Typ_aux (Typ_app (Id_aux (Id "atom",_),
                           [A_aux (A_nexp (Nexp_aux (Nexp_var kid',_)),_)]),_))
                      when Kid.compare kid kid' == 0 ->
                    Some (string "let " ^^ doc_id id ^^ string " := projT1 " ^^ doc_id id ^^ string " in")
                 | _ -> None
               end
             | _ -> None) pats
       in
       string "Fixpoint",
       [parens (string "_acc : Acc (Zwf 0) _reclimit")],
       [string "{struct _acc}"],
       fixupspp
    | Rec_aux (r,_) ->
       let d = match r with Rec_nonrec -> "Definition" | _ -> "Fixpoint" in
       string d, [], [], []
  in
  let intropp =
    match mutrec with
    | NotMutrec -> intropp
    | FirstFn -> string "Fixpoint"
    | LaterFn -> string "with"
  in
  let terminalpp = match mutrec with NotMutrec -> dot | _ -> empty in
  (* Work around Coq bug 7975 about pattern binders followed by implicit arguments *)
  let implicitargs =
    if !used_a_pattern && List.length constrspp + List.length atom_constrs > 0 then
      break 1 ^^ separate space
        ([string "Arguments"; idpp;] @
            List.map (fun _ -> string "{_}") quantspp @
            List.map (fun _ -> string "_") pats @
            List.map (fun _ -> string "{_}") constrspp @
            List.map (fun _ -> string "{_}") atom_constrs)
      ^^ dot
    else empty
  in
  let ctxt =
    if is_measured then
      { ctxt with recursive_fns =
                    Bindings.singleton id
                      (List.length quantspp, List.length constrspp + List.length atom_constrs) }
    else ctxt in
  let _ = match guard with
    | None -> ()
    | _ ->
       raise (Reporting.err_unreachable l __POS__
               "guarded pattern expression should have been rewritten before pretty-printing") in
  ((group (flow (break 1) ([intropp; idpp] @ quantspp @ [patspp] @ constrspp @ atom_constrs @ accpp) ^/^
      flow (break 1) (measurepp @ [colon; retpp])),
    implicitargs),
   ctxt,
   (exp, eff, build_ex, fixupspp))


let doc_funcl_body ctxt (exp, eff, build_ex, fixupspp) =
  let bodypp = doc_fun_body ctxt exp in
  let bodypp =
    if effectful eff
    then bodypp
    else match build_ex with
         | Some s -> surround 3 0 (string (s ^ " (")) bodypp (string ")")
         | None -> bodypp in
  let bodypp = separate (break 1) (fixupspp @ [bodypp]) in
  group bodypp

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_),_))::_ -> id

(* Coq doesn't support multiple clauses for a single function joined
   by "and".  However, all the funcls should have been merged by the
   merge_funcls rewrite now. *)
let doc_fundef_rhs types_mod ?(mutrec=NotMutrec) rec_set (FD_aux(FD_function(r, typa, efa, funcls),(l,_))) =
  match funcls with
  | [] -> unreachable l __POS__ "function with no clauses"
  | [funcl] -> doc_funcl_init types_mod mutrec r ~rec_set funcl
  | (FCL_aux (FCL_Funcl (id,_),_))::_ -> unreachable l __POS__ ("function " ^ string_of_id id ^ " has multiple clauses in backend")

let doc_mutrec types_mod rec_set = function
  | [] -> failwith "DEF_internal_mutrec with empty function list"
  | fundef::fundefs ->
     let prepost1,ctxt1,details1 = doc_fundef_rhs types_mod ~mutrec:FirstFn rec_set fundef in
     let prepostn,ctxtn,detailsn = Util.split3 (List.map (doc_fundef_rhs types_mod ~mutrec:LaterFn rec_set) fundefs) in
     let recursive_fns = List.fold_left (fun m c -> Bindings.union (fun _ x _ -> Some x) m c.recursive_fns) ctxt1.recursive_fns ctxtn in
     let ctxts = List.map (fun c -> { c with recursive_fns }) (ctxt1::ctxtn) in
     let bodies = List.map2 doc_funcl_body ctxts (details1::detailsn) in
     let idpps = List.map (fun fd -> string (string_of_id (id_of_fundef fd))) (fundef::fundefs) in
     let bodies = List.map2 (fun idpp b -> surround 3 0 (string "(*" ^^ idpp ^^ string "*) exact (") b (string ").")) idpps bodies in
     let pres, posts = List.split (prepost1::prepostn) in
     separate hardline pres ^^ dot ^^ hardline ^^
       separate hardline bodies ^^
         break 1 ^^ string "Defined." ^^ hardline ^^
           separate hardline posts

let doc_funcl types_mod mutrec r funcl =
  let (pre,post),ctxt,details = doc_funcl_init types_mod mutrec r funcl in
  let body = doc_funcl_body ctxt details in
  pre,body,post

let rec doc_fundef types_mod (FD_aux(FD_function(r, typa, efa, fcls),fannot)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux (FCL_Funcl(id,_),annot) as funcl]
    when not (Env.is_extern id (env_of_annot annot) "coq") ->
     begin
       let pre,body,post = doc_funcl types_mod NotMutrec r funcl in
       match r with
       | Rec_aux (Rec_measure _,_) ->
          group (pre ^^ dot ^^ hardline ^^
                   surround 3 0 (string "exact (") body (string ").") ^^
                     hardline ^^ string "Defined.") ^^ hardline ^^ post
       | _ -> group (prefix 3 1 (pre ^^ space ^^ coloneq) (body ^^ dot)) ^^ post
     end
   | [_] -> empty (* extern *)
  | _ -> failwith "FD_function with more than one clause"



let doc_dec (DEC_aux (reg, ((l, _) as annot))) =
  match reg with
  | DEC_reg(_,_,typ,id) -> empty
     (*
       let env = env_of_annot annot in
       let rt = Env.base_typ_of env typ in
       if is_vector_typ rt then
         let start, (size, order, etyp) = vector_start_index rt, vector_typ_args_of rt in
         if is_bit_typ etyp && is_nexp_constant start && is_nexp_constant size then
           let o = if is_order_inc order then "true" else "false" in
           (doc_op equals)
             (string "let" ^^ space ^^ doc_id id)
             (string "Register" ^^ space ^^
                align (separate space [string_lit(doc_id id);
                                       doc_nexp (size);
                                       doc_nexp (start);
                                       string o;
                                       string "[]"]))
           ^/^ hardline
         else raise (Reporting.err_unreachable l __POS__ ("can't deal with register type " ^ string_of_typ typ))
       else raise (Reporting.err_unreachable l __POS__ ("can't deal with register type " ^ string_of_typ typ)) *)
  | DEC_config(id, typ, exp) -> separate space [string "Definition"; doc_id id; coloneq; doc_exp empty_ctxt false exp] ^^ dot ^^ hardline
  | DEC_alias(id,alspec) -> empty
  | DEC_typ_alias(typ,id,alspec) -> empty

let is_field_accessor regtypes fdef =
  let is_field_of regtyp field =
    List.exists (fun (tname, (_, _, fields)) -> tname = regtyp &&
      List.exists (fun (_, fid) -> string_of_id fid = field) fields) regtypes in
  match Util.split_on_char '_' (string_of_id (id_of_fundef fdef)) with
  | [access; regtyp; field] ->
     (access = "get" || access = "set") && is_field_of regtyp field
  | _ -> false


let int_of_field_index tname fid nexp =
  match int_of_nexp_opt nexp with
  | Some i -> i
  | None -> raise (Reporting.err_typ Parse_ast.Unknown
                   ("Non-constant bitfield index in field " ^ string_of_id fid ^ " of " ^ tname))

let doc_regtype_fields (tname, (n1, n2, fields)) =
  let const_int fid idx = int_of_field_index tname fid idx in
  let i1, i2 = match n1, n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) -> i1, i2
    | _ -> raise (Reporting.err_typ Parse_ast.Unknown
       ("Non-constant indices in register type " ^ tname)) in
  let dir_b = i1 < i2 in
  let dir = (if dir_b then "true" else "false") in
  let doc_field (fr, fid) =
    let i, j = match fr with
    | BF_aux (BF_single i, _) -> let i = const_int fid i in (i, i)
    | BF_aux (BF_range (i, j), _) -> (const_int fid i, const_int fid j)
    | _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__
        ("Unsupported type in field " ^ string_of_id fid ^ " of " ^ tname)) in
    let fsize = Big_int.succ (Big_int.abs (Big_int.sub i j)) in
    (* TODO Assumes normalised, decreasing bitvector slices; however, since
       start indices or indexing order do not appear in Lem type annotations,
       this does not matter. *)
    let ftyp = vector_typ (nconstant fsize) dec_ord bit_typ in
    let reftyp =
      mk_typ (Typ_app (Id_aux (Id "field_ref", Parse_ast.Unknown),
        [mk_typ_arg (A_typ (mk_id_typ (mk_id tname)));
         mk_typ_arg (A_typ ftyp)])) in
    let rfannot = doc_tannot empty_ctxt Env.empty false reftyp in
    doc_op equals
     (concat [string "let "; parens (concat [string tname; underscore; doc_id fid; rfannot])])
     (concat [
       space; langlebar; string " field_name = \"" ^^ doc_id fid ^^ string "\";"; hardline;
       space; space; space; string (" field_start = " ^ Big_int.to_string i ^ ";"); hardline;
       space; space; space; string (" field_is_inc = " ^ dir ^ ";"); hardline;
       space; space; space; string (" get_field = get_" ^ tname ^ "_" ^ string_of_id fid ^ ";"); hardline;
       space; space; space; string (" set_field = set_" ^ tname ^ "_" ^ string_of_id fid ^ " "); ranglebar])
  in
  separate_map hardline doc_field fields

(* Remove some type variables in a similar fashion to merge_kids_atoms *)
let doc_axiom_typschm typ_env l (tqs,typ) =
  let typ_env = Env.add_typquant l tqs typ_env in
  match typ with
  | Typ_aux (Typ_fn (typs, ret_ty, eff),l') ->
     let check_typ (args,used) typ =
       match Type_check.destruct_atom_nexp typ_env typ with
       | Some (Nexp_aux (Nexp_var kid,_)) ->
          if KidSet.mem kid used then args,used else
            KidSet.add kid args, used
       | Some _ -> args, used
       | _ ->
          match Type_check.destruct_atom_bool typ_env typ with
          | Some (NC_aux (NC_var kid,_)) ->
             if KidSet.mem kid used then args,used else
               KidSet.add kid args, used
          | _ ->
             args, KidSet.union used (tyvars_of_typ typ)
     in
     let args, used = List.fold_left check_typ (KidSet.empty, KidSet.empty) typs in
     let used = if is_number ret_ty then used else KidSet.union used (tyvars_of_typ ret_ty) in
     let kopts,constraints = quant_split tqs in
     let used = List.fold_left (fun used nc -> KidSet.union used (tyvars_of_constraint nc)) used constraints in
     let tqs = match tqs with
       | TypQ_aux (TypQ_tq qs,l) -> TypQ_aux (TypQ_tq (List.filter (function
         | QI_aux (QI_id kopt,_) ->
            let kid = kopt_kid kopt in
            KidSet.mem kid used && not (KidSet.mem kid args)
         | _ -> true) qs),l)
       | _ -> tqs
     in
     let typ_count = ref 0 in
     let fresh_var () =
       let n = !typ_count in
       let () = typ_count := n+1 in
       string ("x" ^ string_of_int n)
     in
     let doc_typ' typ =
       match Type_check.destruct_atom_nexp typ_env typ with
       | Some (Nexp_aux (Nexp_var kid,_)) when KidSet.mem kid args ->
          parens (doc_var empty_ctxt kid ^^ string " : Z")
       (* This case is silly, but useful for tests *)
       | Some (Nexp_aux (Nexp_constant n,_)) ->
          let v = fresh_var () in
          parens (v ^^ string " : Z") ^/^
            bquote ^^ braces (string "ArithFact " ^^
                                parens (v ^^ string " =? " ^^ string (Big_int.to_string n)))
       | _ ->
          match Type_check.destruct_atom_bool typ_env typ with
          | Some (NC_aux (NC_var kid,_)) when KidSet.mem kid args ->
             parens (doc_var empty_ctxt kid ^^ string " : bool")
          | _ ->
             parens (underscore ^^ string " : " ^^ doc_typ empty_ctxt Env.empty typ)
     in
     let arg_typs_pp = separate space (List.map doc_typ' typs) in
     let _, ret_ty = replace_atom_return_type ret_ty in
     let ret_typ_pp = doc_typ empty_ctxt Env.empty ret_ty in
     let ret_typ_pp =
       if effectful eff
       then string "M" ^^ space ^^ parens ret_typ_pp
       else ret_typ_pp
     in
     let tyvars_pp, constrs_pp = doc_typquant_items_separate empty_ctxt typ_env braces tqs in
     string "forall" ^/^ separate space tyvars_pp ^/^
       arg_typs_pp ^/^ separate space constrs_pp ^^ comma ^/^ ret_typ_pp
  | _ -> doc_typschm empty_ctxt typ_env true (TypSchm_aux (TypSchm_ts (tqs,typ),l))

let doc_val_spec unimplemented (VS_aux (VS_val_spec(_,id,_,_),(l,ann)) as vs) =
  if !opt_undef_axioms && IdSet.mem id unimplemented then
    let typ_env = env_of_annot (l,ann) in
    (* The type checker will expand the type scheme, and we need to look at the
       environment afterwards to find it. *)
    let _, next_env = check_val_spec typ_env vs in
    let tys = Env.get_val_spec id next_env in
    group (separate space
             [string "Axiom"; doc_id id; colon; doc_axiom_typschm typ_env l tys] ^^ dot) ^/^ hardline
  else empty (* Type signatures appear in definitions *)

(* If a top-level value is declared with an existential type, we turn it into
   a type annotation expression instead (unless it duplicates an existing one). *)
let doc_val pat exp =
  let (id,pat_typ) = match pat with
    | P_aux (P_typ (typ, P_aux (P_id id,_)),_) -> id, Some typ
    | P_aux (P_id id, _) -> id, None
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)),_) when Id.compare id (id_of_kid kid) == 0 ->
       id, None
    | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)),_)),_) when Id.compare id (id_of_kid kid) == 0 ->
       id, Some typ
    | _ -> raise (Reporting.err_todo (pat_loc pat)
                    "Top-level value definition with complex pattern not supported for Coq yet")
  in
  let typpp = match pat_typ with
    | None -> empty
    | Some typ -> space ^^ colon ^^ space ^^ doc_typ empty_ctxt Env.empty typ
  in
  let env = env_of exp in
  let ctxt = { empty_ctxt with debug  = List.mem (string_of_id id) (!opt_debug_on) } in
  let () =
    debug ctxt (lazy ("Checking definition " ^ string_of_id id));
    debug_depth := 1
  in
  let typpp, exp =
    match pat_typ with
    | None -> typpp, exp
    | Some typ ->
       let typ = expand_range_type (Env.expand_synonyms env typ) in
       match destruct_exist_plain typ with
       | None -> typpp, exp
       | Some _ ->
          empty, match exp with
          | E_aux (E_cast (typ',_),_) when alpha_equivalent env typ typ' -> exp
          | _ -> E_aux (E_cast (typ,exp), (Parse_ast.Unknown, mk_tannot env typ (effect_of exp)))
  in
  let idpp = doc_id id in
  let base_pp = doc_exp ctxt false exp ^^ dot in
  let () = debug_depth := 0 in
  group (string "Definition" ^^ space ^^ idpp ^^ typpp ^^ space ^^ coloneq ^/^ base_pp) ^^ hardline ^^
  group (separate space [string "Hint Unfold"; idpp; colon; string "sail."]) ^^ hardline

let rec doc_def types_mod unimplemented generic_eq_types def =
  match def with
  | DEF_spec v_spec -> doc_val_spec unimplemented v_spec
  | DEF_fixity _ -> empty
  | DEF_overload _ -> empty
  | DEF_type t_def -> doc_typdef types_mod generic_eq_types t_def
  | DEF_reg_dec dec -> group (doc_dec dec)

  | DEF_default df -> empty
  | DEF_fundef fdef -> group (doc_fundef types_mod fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec types_mod (ids_of_def def) fundefs ^/^ hardline
  | DEF_val (LB_aux (LB_val (pat, exp), _)) -> doc_val pat exp
  | DEF_scattered sdef -> failwith "doc_def: shoulnd't have DEF_scattered at this point"
  | DEF_mapdef (MD_aux (_, (l,_))) -> unreachable l __POS__ "Coq doesn't support mappings"
  | DEF_pragma _ -> empty
  | DEF_measure (id,_,_) -> unreachable (id_loc id) __POS__
                              ("Termination measure for " ^ string_of_id id ^
                                 " should have been rewritten before backend")
  | DEF_loop_measures (id,_) ->
     unreachable (id_loc id) __POS__
       ("Loop termination measures for " ^ string_of_id id ^
          " should have been rewritten before backend")

let find_exc_typ defs =
  let is_exc_typ_def = function
    | DEF_type td -> string_of_id (id_of_type_def td) = "exception"
    | _ -> false in
  if List.exists is_exc_typ_def defs then "exception" else "unit"

let find_unimplemented defs =
  let adjust_fundef unimplemented (FD_aux (FD_function (_,_,_,funcls),_)) =
    match funcls with
    | [] -> unimplemented
    | (FCL_aux (FCL_Funcl (id,_),_))::_ ->
       IdSet.remove id unimplemented
  in
  let adjust_def unimplemented = function
    | DEF_spec (VS_aux (VS_val_spec (_,id,exts,_),_)) -> begin
      match Ast_util.extern_assoc "coq" exts with
      | Some _ -> unimplemented
      | None -> IdSet.add id unimplemented
    end
    | DEF_internal_mutrec fds ->
       List.fold_left adjust_fundef unimplemented fds
    | DEF_fundef fd -> adjust_fundef unimplemented fd
    | _ -> unimplemented
  in
  List.fold_left adjust_def IdSet.empty defs

let pp_ast_coq (types_file,types_modules) (defs_file,defs_modules) type_defs_module { defs; _ } top_line suppress_MR_M =
try
  (* let regtypes = find_regtypes d in *)
  let state_ids =
    State.generate_regstate_defs true defs
    |> val_spec_ids
  in
  let is_state_def = function
    | DEF_spec vs -> IdSet.mem (id_of_val_spec vs) state_ids
    | DEF_fundef fd -> IdSet.mem (id_of_fundef fd) state_ids
    | _ -> false
  in
  let is_typ_def = function
    | DEF_type _ -> true
    | _ -> false
  in
  let exc_typ = find_exc_typ defs in
  let typdefs, defs = List.partition is_typ_def defs in
  let statedefs, defs = List.partition is_state_def defs in
  let register_refs = State.register_refs_coq doc_id (State.find_registers defs) in
  let unimplemented = find_unimplemented defs in
  let generic_eq_types = types_used_with_generic_eq defs in
  let doc_def = doc_def type_defs_module unimplemented generic_eq_types in
  let () = if !opt_undef_axioms || IdSet.is_empty unimplemented then () else
      Reporting.print_err Parse_ast.Unknown "Warning"
        ("The following functions were declared but are undefined:\n" ^
            String.concat "\n" (List.map string_of_id (IdSet.elements unimplemented)))
  in
  (print types_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "Require Import";string lib] ^^ dot) types_modules;hardline;
        string "Import ListNotations.";
        hardline;
        string "Open Scope string."; hardline;
        string "Open Scope bool."; hardline;
        string "Open Scope Z."; hardline;
        hardline;
        separate empty (List.map doc_def typdefs); hardline;
        hardline;
        separate empty (List.map doc_def statedefs); hardline;
        hardline;
        register_refs; hardline;
        (if suppress_MR_M then empty else concat [
          string ("Definition MR a r := monadR register_value a r " ^ exc_typ ^ "."); hardline;
          string ("Definition M a := monad register_value a " ^ exc_typ ^ "."); hardline;
          string ("Definition returnM {A:Type} := @returnm register_value A " ^ exc_typ ^ "."); hardline;
          string ("Definition returnR {A:Type} (R:Type) := @returnm register_value A (R + " ^ exc_typ ^ ")."); hardline
        ])
        ]);
  (print defs_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "Require Import";string lib] ^^ dot) defs_modules;hardline;
        string "Import ListNotations.";
        hardline;
        string "Open Scope string."; hardline;
        string "Open Scope bool."; hardline;
        string "Open Scope Z."; hardline;
        hardline;
        hardline;
        separate empty (List.map doc_def defs);
        hardline;
        hardline])
with Type_check.Type_error (env,l,err) ->
  let extra =
    "\nError during Coq printing\n" ^
    if Printexc.backtrace_status ()
    then "\n" ^ Printexc.get_backtrace ()
    else "(backtracing unavailable)"
  in
  raise (Reporting.err_typ l (Type_error.string_of_type_error err ^ extra))
