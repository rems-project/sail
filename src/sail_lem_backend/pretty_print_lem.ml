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

open Libsail

open Type_check
open Ast
open Ast_defs
open Ast_util
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

(****************************************************************************
 * PPrint-based sail-to-lem pprinter
****************************************************************************)

let opt_sequential = ref false
let opt_extern_types : string list ref = ref []

let prefix_recordtype = true

type context = {
  early_ret : bool;
  monadic : bool;
  bound_nexps : NexpSet.t;
  top_env : Env.t;
  params_to_print : Util.IntSet.t Bindings.t;
}
let empty_ctxt =
  {
    early_ret = false;
    monadic = false;
    bound_nexps = NexpSet.empty;
    top_env = Env.empty;
    params_to_print = Bindings.empty;
  }

let print_to_from_interp_value = ref false
let langlebar = string "<|"
let ranglebar = string "|>"
let anglebars = enclose langlebar ranglebar

let doc_var (Kid_aux (Var v, _)) = string v

let is_number_char c =
  c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5' || c = '6' || c = '7' || c = '8' || c = '9'

let rec fix_id remove_tick name =
  match name with
  | "assert" | "lsl" | "lsr" | "asr" | "type" | "fun" | "function" | "raise" | "try" | "match" | "with" | "check"
  | "field" | "LT" | "lt" | "lteq" | "GT" | "gt" | "gteq" | "EQ" | "eq" | "neq" | "integer" | "union" | "inter"
  | "subset" | "zero_extend" | "sign_extend" | "zeros" | "B0" | "B1" | "Nothing" | "Just" ->
      name ^ "'"
  | _ ->
      if String.contains name '#' then fix_id remove_tick (String.concat "_" (Util.split_on_char '#' name))
      else if String.contains name '?' then fix_id remove_tick (String.concat "_pat_" (Util.split_on_char '?' name))
      else if name.[0] = '\'' then (
        let var = String.sub name 1 (String.length name - 1) in
        if remove_tick then var else var ^ "'"
      )
      else if is_number_char name.[0] then "v" ^ name ^ "'"
      else name

let doc_id_lem (Id_aux (i, _)) =
  match i with Id i -> string (fix_id false i) | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_id_lem_type (Id_aux (i, _)) =
  match i with
  | Id "int" -> string "ii"
  | Id "nat" -> string "ii"
  | Id "option" -> string "maybe"
  | Id i -> string (fix_id false i)
  | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_id_lem_ctor (Id_aux (i, _)) =
  match i with
  | Id "bit" -> string "bitU"
  | Id "int" -> string "integer"
  | Id "nat" -> string "integer"
  | Id "Some" -> string "Just"
  | Id "None" -> string "Nothing"
  | Id i -> string (fix_id false (String.capitalize_ascii i))
  | Operator x -> string (Util.zencode_string ("op " ^ x))

let deinfix = function Id_aux (Id v, l) -> Id_aux (Operator v, l) | Id_aux (Operator v, l) -> Id_aux (Operator v, l)

let doc_var_lem kid = string (fix_id true (string_of_kid kid))

let doc_fieldname_lem typ_id field_id =
  if prefix_recordtype && string_of_id typ_id <> "regstate" then
    string (fix_id false (string_of_id typ_id ^ "_" ^ string_of_id field_id))
  else doc_id_lem_type field_id

let simple_annot l typ = (Parse_ast.Generated l, Some (Env.empty, typ, no_effect))
let simple_num l n =
  E_aux
    ( E_lit (L_aux (L_num n, Parse_ast.Generated l)),
      simple_annot (Parse_ast.Generated l) (atom_typ (Nexp_aux (Nexp_constant n, Parse_ast.Generated l)))
    )

let is_regtyp (Typ_aux (typ, _)) env =
  match typ with Typ_app (id, _) when string_of_id id = "register" -> true | _ -> false

let lemnum default n =
  if Big_int.less_equal Big_int.zero n && Big_int.less_equal n (Big_int.of_int 128) then "int" ^ Big_int.to_string n
  else if Big_int.greater_equal n Big_int.zero then default n
  else "(int0 - " ^ default (Big_int.abs n) ^ ")"

let doc_nexp_lem nexp =
  let nice_kid kid =
    let (Kid_aux (Var kid, l)) = orig_kid kid in
    Kid_aux (Var (String.map (function '#' -> '_' | c -> c) kid), l)
  in
  let (Nexp_aux (nexp, l) as full_nexp) = nexp_simp nexp in
  match nexp with
  | Nexp_constant i -> string ("ty" ^ Big_int.to_string i)
  | Nexp_var v -> string (string_of_kid (nice_kid v))
  | _ ->
      let rec mangle_nexp (Nexp_aux (nexp, _)) =
        begin
          match nexp with
          | Nexp_id id -> string_of_id id
          | Nexp_var kid -> string_of_id (id_of_kid (nice_kid kid))
          | Nexp_constant i -> lemnum Big_int.to_string i
          | Nexp_times (n1, n2) -> mangle_nexp n1 ^ "_times_" ^ mangle_nexp n2
          | Nexp_sum (n1, n2) -> mangle_nexp n1 ^ "_plus_" ^ mangle_nexp n2
          | Nexp_minus (n1, n2) -> mangle_nexp n1 ^ "_minus_" ^ mangle_nexp n2
          | Nexp_exp n -> "exp_" ^ mangle_nexp n
          | Nexp_neg n -> "neg_" ^ mangle_nexp n
          | _ ->
              raise
                (Reporting.err_unreachable l __POS__ ("cannot pretty-print nexp \"" ^ string_of_nexp full_nexp ^ "\""))
        end
      in
      string ("'" ^ mangle_nexp full_nexp)

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

(* Calculate which type parameters of a data type (for now just records) are
   types or sizes that should be printed. *)
let type_parameters_to_print env defs : Util.IntSet.t Bindings.t =
  let make_type_size_map env id typq typs type_size_map =
    let type_params, _ =
      List.fold_left
        (fun (is, i) q ->
          match q with
          | KOpt_aux (KOpt_kind (K_aux (K_type, _), _), _) -> (Util.IntSet.add i is, i + 1)
          | _ -> (is, i + 1)
        )
        (Util.IntSet.empty, 0) (quant_kopts typq)
    in
    let local_ints, _ =
      List.fold_left
        (fun (map, i) q ->
          match q with
          | KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _) -> (KBindings.add kid i map, i + 1)
          | _ -> (map, i + 1)
        )
        (KBindings.empty, 0) (quant_kopts typq)
    in
    let rec check_typ is typ =
      match Env.expand_synonyms env typ with
      | Typ_aux (Typ_app (id, args), _) -> begin
          match Bindings.find_opt id type_size_map with
          | None -> is
          | Some js ->
              let is' =
                Util.IntSet.fold
                  (fun j is ->
                    match List.nth_opt args j with
                    | Some (A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)) -> (
                        match KBindings.find_opt kid local_ints with Some i -> Util.IntSet.add i is | None -> is
                      )
                    | _ -> is
                  )
                  js is
              in
              List.fold_left
                (fun is (A_aux (arg, _)) -> match arg with A_typ typ -> check_typ is typ | _ -> is)
                is' args
        end
      | Typ_aux (Typ_tuple typs, _) -> List.fold_left check_typ is typs
      | Typ_aux (Typ_exist (_, _, typ), _) -> check_typ is typ
      | _ -> is
    in
    let is = List.fold_left (fun is typ -> check_typ is typ) type_params typs in
    Bindings.add id is type_size_map
  in
  let check_def type_size_map (DEF_aux (def, _)) =
    match def with
    | DEF_type (TD_aux (TD_record (id, typq, fs, _), _)) ->
        let env = Env.add_typquant Unknown typq env in
        make_type_size_map env id typq (List.map fst fs) type_size_map
    | DEF_type (TD_aux (TD_variant (id, typq, tus, _), _)) ->
        let env = Env.add_typquant Unknown typq env in
        make_type_size_map env id typq (List.map (fun (Tu_aux (Tu_ty_id (t, _), _)) -> t) tus) type_size_map
    | DEF_type (TD_aux (TD_abbrev (id, typq, typ_arg), _)) -> begin
        let env = Env.add_typquant Unknown typq env in
        match typ_arg with
        | A_aux (A_typ typ, _) -> make_type_size_map env id typq [typ] type_size_map
        | _ -> type_size_map
      end
    | _ -> type_size_map
  in

  (* Seed parameters to print with builtin types that need a parameter to be printed *)
  let bitvector_itself_prints = if !Monomorphise.opt_mwords then Util.IntSet.singleton 0 else Util.IntSet.empty in
  let init_map =
    Bindings.empty
    |> Bindings.add (mk_id "bitvector") bitvector_itself_prints
    |> Bindings.add (mk_id "itself") bitvector_itself_prints
  in

  let map = List.fold_left check_def init_map defs in
  (*
  Bindings.iter (fun id is ->
      let s = String.concat "," (List.map string_of_int (Util.IntSet.elements is))
      in Printf.eprintf "%s %s\n%!" (string_of_id id) s) map;
  *)
  map

(* Returns the set of type variables that will appear in the Lem output,
   which may be smaller than those in the Sail type.  May need to be
   updated with doc_typ_lem *)
let rec lem_nexps_of_typ params_to_print (Typ_aux (t, l)) =
  let trec = lem_nexps_of_typ params_to_print in
  match t with
  | Typ_id _ -> NexpSet.empty
  | Typ_var kid -> NexpSet.singleton (orig_nexp (nvar kid))
  | Typ_fn (t1, t2) -> List.fold_left NexpSet.union (trec t2) (List.map trec t1)
  | Typ_tuple ts -> List.fold_left (fun s t -> NexpSet.union s (trec t)) NexpSet.empty ts
  | Typ_app (Id_aux (Id "bitvector", _), [A_aux (A_nexp m, _)]) ->
      let m = nexp_simp m in
      if !Monomorphise.opt_mwords && not (is_nexp_constant m) then NexpSet.singleton (orig_nexp m) else trec bit_typ
  | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp m, _); A_aux (A_typ elem_typ, _)]) -> trec elem_typ
  | Typ_app (Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) -> trec etyp
  | Typ_app (Id_aux (Id "range", _), _) | Typ_app (Id_aux (Id "implicit", _), _) | Typ_app (Id_aux (Id "atom", _), _) ->
      NexpSet.empty
  | Typ_app (id, tas) -> begin
      match Bindings.find_opt id params_to_print with
      | Some is ->
          Util.IntSet.fold
            (fun i s -> NexpSet.union s (lem_nexps_of_typ_arg params_to_print (List.nth tas i)))
            is NexpSet.empty
      | None -> List.fold_left (fun s ta -> NexpSet.union s (lem_nexps_of_typ_arg params_to_print ta)) NexpSet.empty tas
    end
  | Typ_exist (kids, _, t) -> trec t
  | Typ_bidir _ -> raise (Reporting.err_unreachable l __POS__ "Lem doesn't support bidir types")
  | Typ_internal_unknown -> raise (Reporting.err_unreachable l __POS__ "escaped Typ_internal_unknown")

and lem_nexps_of_typ_arg params_to_print (A_aux (ta, _)) =
  match ta with
  | A_nexp nexp ->
      let nexp = nexp_simp (orig_nexp nexp) in
      if is_nexp_constant nexp then NexpSet.empty else NexpSet.singleton nexp
  | A_typ typ -> lem_nexps_of_typ params_to_print typ
  | A_bool _ -> NexpSet.empty

let lem_tyvars_of_typ params_to_print typ =
  NexpSet.fold
    (fun nexp ks -> KidSet.union ks (tyvars_of_nexp nexp))
    (lem_nexps_of_typ params_to_print typ) KidSet.empty

(* When making changes here, check whether they affect lem_tyvars_of_typ *)
let doc_typ_lem, doc_typ_lem_brackets, doc_atomic_typ_lem =
  (* following the structure of parser for precedence *)
  let rec typ params_to_print atyp_needed ty = tup_typ params_to_print atyp_needed ty
  and tup_typ params_to_print atyp_needed (Typ_aux (t, l) as ty) =
    match t with
    | Typ_fn (args, ret) ->
        let ret_typ =
          (* TODO EFFECT: Monadicity as parameter or separate function. See Coq *)
          (*
           if effectful efct
           then separate space [string "M"; tup_typ true ret]
           else *)
          separate space [tup_typ params_to_print false ret]
        in
        let arg_typs = List.map (tup_typ params_to_print false) args in
        let tpp = separate (space ^^ arrow ^^ space) (arg_typs @ [ret_typ]) in
        (* once we have proper excetions we need to know what the exceptions type is *)
        if atyp_needed then parens tpp else tpp
    | Typ_tuple typs -> parens (separate_map (space ^^ star ^^ space) (app_typ params_to_print false) typs)
    | _ -> app_typ params_to_print atyp_needed ty
  and app_typ params_to_print atyp_needed (Typ_aux (t, l) as ty) =
    match t with
    | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp m, _); A_aux (A_typ elem_typ, _)]) ->
        let tpp = string "list" ^^ space ^^ typ params_to_print true elem_typ in
        if atyp_needed then parens tpp else tpp
    | Typ_app (Id_aux (Id "bitvector", _), [A_aux (A_nexp m, _)]) ->
        let tpp =
          if !Monomorphise.opt_mwords then string "mword " ^^ doc_nexp_lem (nexp_simp m)
          else string "list" ^^ space ^^ typ params_to_print true bit_typ
        in
        if atyp_needed then parens tpp else tpp
    | Typ_app (Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) ->
        let tpp = string "register_ref regstate register_value " ^^ typ params_to_print true etyp in
        if atyp_needed then parens tpp else tpp
    | Typ_app (Id_aux (Id "range", _), _) -> string "integer"
    | Typ_app (Id_aux (Id "implicit", _), _) -> string "integer"
    | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp n, _)]) -> string "integer"
    | Typ_app (Id_aux (Id "atom_bool", _), [A_aux (A_bool nc, _)]) -> string "bool"
    | Typ_app (id, args) ->
        let args =
          match Bindings.find_opt id params_to_print with
          | None -> args
          | Some is ->
              let args, _ =
                List.fold_left
                  (fun (l, i) a -> if Util.IntSet.mem i is then (a :: l, i + 1) else (l, i + 1))
                  ([], 0) args
              in
              List.rev args
        in
        let tpp = doc_id_lem_type id ^^ space ^^ separate_map space (doc_typ_arg_lem params_to_print) args in
        if atyp_needed then parens tpp else tpp
    | _ -> atomic_typ params_to_print atyp_needed ty
  and atomic_typ params_to_print atyp_needed (Typ_aux (t, l) as ty) =
    match t with
    | Typ_id (Id_aux (Id "bool", _)) -> string "bool"
    | Typ_id (Id_aux (Id "bit", _)) -> string "bitU"
    | Typ_id id ->
        (*if List.exists ((=) (string_of_id id)) regtypes
          then string "register"
          else*)
        doc_id_lem_type id
    | Typ_var v -> doc_var v
    | Typ_app _ | Typ_tuple _ | Typ_fn _ ->
        (* exhaustiveness matters here to avoid infinite loops
         * if we add a new Typ constructor *)
        let tpp = typ params_to_print true ty in
        if atyp_needed then parens tpp else tpp
    | Typ_exist (kopts, _, ty) when List.for_all is_int_kopt kopts -> begin
        let kids = List.map kopt_kid kopts in
        let tpp = typ params_to_print true ty in
        let visible_vars = lem_tyvars_of_typ params_to_print ty in
        match List.filter (fun kid -> KidSet.mem kid visible_vars) kids with
        | [] -> if atyp_needed then parens tpp else tpp
        | bad ->
            raise
              (Reporting.err_general l
                 ("Existential type variable(s) " ^ String.concat ", " (List.map string_of_kid bad) ^ " escape into Lem")
              )
      end
    (* AA: I think the correct thing is likely to filter out
       non-integer kinded_id's, then use the above code. *)
    | Typ_exist (_, _, Typ_aux (Typ_app (id, [_]), _)) when string_of_id id = "atom_bool" -> string "bool"
    | Typ_exist _ -> unreachable l __POS__ "Non-integer existentials currently unsupported in Lem" (* TODO *)
    | Typ_bidir _ -> unreachable l __POS__ "Lem doesn't support bidir types"
    | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
  and doc_typ_arg_lem params_to_print (A_aux (t, _)) =
    match t with
    | A_typ t -> app_typ params_to_print true t
    | A_nexp n -> doc_nexp_lem (nexp_simp n)
    | A_bool _ -> empty
  in
  let top atyp_needed params_to_print env ty =
    (* If we use the bitlist representation of bitvectors, the type argument in
       type abbreviations such as "bits('n)" becomes dead, which confuses HOL; as a
       workaround, we expand type synonyms in this case. *)
    let ty' = if !Monomorphise.opt_mwords then ty else Env.expand_synonyms env ty in
    typ params_to_print atyp_needed ty'
  in
  (top false, top true, atomic_typ)

let doc_fn_typ_lem ?(monad = empty) params_to_print env (Typ_aux (aux, l) as ty) =
  match aux with
  | Typ_fn (args, ret) ->
      separate
        (space ^^ arrow ^^ space)
        (List.map (doc_typ_lem params_to_print env) args @ [monad ^^ (doc_typ_lem_brackets params_to_print env) ret])
  | _ -> doc_typ_lem params_to_print env ty

(* Check for variables in types that would be pretty-printed. *)
let contains_t_pp_var ctxt (Typ_aux (t, a) as typ) =
  lem_nexps_of_typ ctxt.params_to_print typ |> NexpSet.exists (fun nexp -> not (is_nexp_constant nexp))

let rec replace_typ_size ctxt env (Typ_aux (t, a) as typ) =
  let rewrap t = Typ_aux (t, a) in
  let recur = replace_typ_size ctxt env in
  match t with
  | Typ_tuple typs -> begin
      match Util.option_all (List.map recur typs) with Some typs' -> Some (rewrap (Typ_tuple typs')) | None -> None
    end
  | Typ_app (id, args) when contains_t_pp_var ctxt typ -> begin
      match Util.option_all (List.map (replace_typ_arg_size ctxt env) args) with
      | Some args' -> Some (rewrap (Typ_app (id, args')))
      | None -> None
    end
  | Typ_app _ -> Some typ
  | Typ_id _ -> Some typ
  | Typ_fn (argtyps, rtyp) -> begin
      match (Util.option_all (List.map recur argtyps), recur rtyp) with
      | Some argtyps', Some rtyp' -> Some (rewrap (Typ_fn (argtyps', rtyp')))
      | _ -> None
    end
  | Typ_var kid ->
      let is_kid nexp = Nexp.compare nexp (nvar kid) = 0 in
      if NexpSet.exists is_kid ctxt.bound_nexps then Some typ else None
  | Typ_exist (kids, nc, typ) -> begin
      match recur typ with Some typ' -> Some (rewrap (Typ_exist (kids, nc, typ'))) | None -> None
    end
  | Typ_internal_unknown | Typ_bidir (_, _) -> None

and replace_typ_arg_size ctxt env (A_aux (ta, a) as targ) =
  let rewrap ta = A_aux (ta, a) in
  match ta with
  | A_nexp nexp -> begin
      match Type_check.solve_unique env nexp with
      | Some n -> Some (rewrap (A_nexp (nconstant n)))
      | None -> (
          let is_equal nexp' = prove __POS__ env (NC_aux (NC_equal (nexp, nexp'), Parse_ast.Unknown)) in
          match List.find is_equal (NexpSet.elements ctxt.bound_nexps) with
          | nexp' -> Some (rewrap (A_nexp nexp'))
          | exception Not_found -> None
        )
    end
  | A_typ typ -> begin
      match replace_typ_size ctxt env typ with Some typ' -> Some (rewrap (A_typ typ')) | None -> None
    end
  | A_bool _ -> Some targ

let make_printable_type ctxt env typ =
  if contains_t_pp_var ctxt typ then (try replace_typ_size ctxt env (Env.expand_synonyms env typ) with _ -> None)
  else Some typ

let doc_tannot_lem ctxt env eff typ =
  match make_printable_type ctxt env typ with
  | None -> empty
  | Some typ ->
      let ta = doc_typ_lem ctxt.params_to_print env typ in
      if eff then string " : M " ^^ parens ta else string " : " ^^ ta

let min_int32 = Big_int.of_int64 (Int64.of_int32 Int32.min_int)
let max_int32 = Big_int.of_int64 (Int64.of_int32 Int32.max_int)

let rec doc_lit_lem (L_aux (lit, l)) =
  match lit with
  | L_unit -> utf8string "()"
  | L_zero -> utf8string "B0"
  | L_one -> utf8string "B1"
  | L_false -> utf8string "false"
  | L_true -> utf8string "true"
  | L_num i ->
      let ipp = Big_int.to_string i in
      utf8string (if Big_int.less i Big_int.zero then "((0" ^ ipp ^ "):ii)" else "(" ^ ipp ^ ":ii)")
  | L_hex n when !Monomorphise.opt_mwords -> utf8string ("0x" ^ n)
  | L_bin n when !Monomorphise.opt_mwords -> utf8string ("0b" ^ n)
  | L_hex _ | L_bin _ ->
      vector_string_to_bit_list (L_aux (lit, l)) |> flow_map (semi ^^ break 0) doc_lit_lem |> group |> align |> brackets
  | L_undef -> utf8string "(return (failwith \"undefined value of unsupported type\"))"
  | L_string s -> utf8string ("\"" ^ String.escaped s ^ "\"")
  | L_real s ->
      (* Lem does not support decimal syntax, so we translate a string
         of the form "x.y" into the ratio (x * 10^len(y) + y) / 10^len(y).
         The OCaml library has a conversion function from strings to floats, but
         not from floats to ratios. ZArith's Q library does have the latter, but
         using this would require adding a dependency on ZArith to Sail. *)
      let parts = Util.split_on_char '.' s in
      let num, denom =
        match parts with
        | [i] -> (Big_int.of_string i, Big_int.of_int 1)
        | [i; f] ->
            let denom = Big_int.pow_int_positive 10 (String.length f) in
            (Big_int.add (Big_int.mul (Big_int.of_string i) denom) (Big_int.of_string f), denom)
        | _ -> raise (Reporting.err_syntax_loc l "could not parse real literal")
      in
      parens (separate space (List.map string ["realFromFrac"; Big_int.to_string num; Big_int.to_string denom]))

let kid_nexps_of_typquant tq =
  quant_kopts tq |> List.filter (fun k -> is_int_kopt k || is_typ_kopt k) |> List.map kopt_kid |> List.map nvar

let doc_typquant_items_lem quant_nexps = separate_map space doc_nexp_lem quant_nexps

(* Produce Size type constraints for bitvector sizes when using
   machine words.  Often these will be unnecessary, but this simple
   approach will do for now. *)

let rec typeclass_nexps params_to_print (Typ_aux (t, l)) =
  let typeclass_nexps = typeclass_nexps params_to_print in
  if !Monomorphise.opt_mwords then (
    match t with
    | Typ_id _ | Typ_var _ -> NexpSet.empty
    | Typ_fn (ts, t) -> List.fold_left NexpSet.union (typeclass_nexps t) (List.map typeclass_nexps ts)
    | Typ_tuple ts -> List.fold_left NexpSet.union NexpSet.empty (List.map typeclass_nexps ts)
    | Typ_app (id, args) ->
        let add_arg_subtyp_nexps nexps = function
          | A_aux (A_typ typ, _) -> NexpSet.union nexps (typeclass_nexps typ)
          | _ -> nexps
        in
        let add_arg_nexps nexps = function
          | A_aux (A_nexp nexp, _) ->
              let nexp = nexp_simp nexp in
              if is_nexp_constant nexp then nexps else NexpSet.add (orig_nexp nexp) nexps
          | _ -> nexps
        in
        begin
          let subtyp_nexps = List.fold_left add_arg_subtyp_nexps NexpSet.empty args in
          match Bindings.find_opt id params_to_print with
          | Some is -> Util.IntSet.fold (fun i set -> add_arg_nexps set (List.nth args i)) is subtyp_nexps
          | None -> subtyp_nexps
        end
    | Typ_exist (kids, _, t) -> NexpSet.empty (* todo *)
    | Typ_bidir _ -> unreachable l __POS__ "Lem doesn't support bidir types"
    | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
  )
  else NexpSet.empty

let doc_typclasses_lem params_to_print t =
  let nexps = typeclass_nexps params_to_print t in
  if NexpSet.is_empty nexps then (empty, NexpSet.empty)
  else
    ( separate_map comma_sp (fun nexp -> string "Size " ^^ doc_nexp_lem nexp) (NexpSet.elements nexps) ^^ string " => ",
      nexps
    )

let doc_typschm_lem ?(monad = empty) params_to_print env quants (TypSchm_aux (TypSchm_ts (tq, t), l)) =
  let env = Env.add_typquant l tq env in
  let pt = doc_fn_typ_lem ~monad params_to_print env t in
  if quants then (
    let nexps_used = lem_nexps_of_typ params_to_print t in
    let ptyc, nexps_sizes = doc_typclasses_lem params_to_print t in
    let nexps_to_include = NexpSet.union nexps_used nexps_sizes in
    if NexpSet.is_empty nexps_to_include then pt
    else string "forall " ^^ doc_typquant_items_lem (NexpSet.elements nexps_to_include) ^^ string ". " ^^ ptyc ^^ pt
  )
  else pt

let is_ctor env id = match Env.lookup_id id env with Enum _ -> true | _ -> false

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat_lem ctxt apat_needed (P_aux (p, (l, annot)) as pa) =
  match p with
  | P_app (id, _) when string_of_id id = "None" -> string "Nothing"
  | P_app (id, (_ :: _ as pats)) ->
      let ppp = doc_unop (doc_id_lem_ctor id) (parens (separate_map comma (doc_pat_lem ctxt true) pats)) in
      if apat_needed then parens ppp else ppp
  | P_app (id, []) -> doc_id_lem_ctor id
  | P_lit lit -> doc_lit_lem lit
  | P_wild -> underscore
  | P_id id -> doc_id_lem id
  | P_var (p, _) -> doc_pat_lem ctxt true p
  | P_as (p, id) -> parens (separate space [doc_pat_lem ctxt true p; string "as"; doc_id_lem id])
  | P_typ (Typ_aux (Typ_tuple typs, _), P_aux (P_tuple pats, _)) ->
      (* Isabelle does not seem to like type-annotated tuple patterns;
         it gives a syntax error. Avoid this by annotating the tuple elements instead *)
      let env = env_of_pat pa in
      let doc_elem typ pat = doc_pat_lem ctxt true (add_p_typ env typ pat) in
      parens (separate comma_sp (List.map2 doc_elem typs pats))
  | P_typ (typ, p) -> (
      let doc_p = doc_pat_lem ctxt true p in
      match make_printable_type ctxt (env_of_annot (l, annot)) typ with
      | None -> doc_p
      | Some typ -> parens (doc_op colon doc_p (doc_typ_lem ctxt.params_to_print (env_of_annot (l, annot)) typ))
    )
  | P_vector pats ->
      let ppp = brackets (separate_map semi (doc_pat_lem ctxt true) pats) in
      if apat_needed then parens ppp else ppp
  | P_struct (fpats, FP_no_wild) ->
      let doc_field field =
        match destruct_tannot annot with
        | (Some (env, Typ_aux (Typ_id tid, _)) | Some (env, Typ_aux (Typ_app (tid, _), _))) when Env.is_record tid env
          ->
            doc_fieldname_lem tid field
        | _ -> Reporting.unreachable l __POS__ "P_struct pattern with no record type"
      in
      string "<|" ^^ space
      ^^ separate_map (semi ^^ space)
           (fun (field, pat) -> separate space [doc_field field; equals; doc_pat_lem ctxt false pat])
           fpats
      ^^ space ^^ string "|>"
  | P_struct (_, FP_wild l) -> Reporting.unreachable l __POS__ "field wildcard should not have reached lem backend"
  | P_vector_concat pats ->
      Reporting.unreachable l __POS__ "vector concatenation patterns should have been removed before pretty-printing"
  | P_tuple pats -> (
      match pats with
      | [p] -> doc_pat_lem ctxt apat_needed p
      | _ -> parens (separate_map comma_sp (doc_pat_lem ctxt false) pats)
    )
  | P_list pats -> brackets (separate_map semi (doc_pat_lem ctxt false) pats) (*Never seen but easy in lem*)
  | P_cons (p, p') ->
      let doc_p = doc_op (string "::") (doc_pat_lem ctxt true p) (doc_pat_lem ctxt true p') in
      if apat_needed then parens doc_p else doc_p
  | P_string_append _ -> unreachable l __POS__ "Lem doesn't support string append patterns"
  | P_vector_subrange _ -> unreachable l __POS__ "Lem doesn't support vector subrange patterns"
  | P_not _ -> unreachable l __POS__ "Lem doesn't support not patterns"
  | P_or _ -> unreachable l __POS__ "Lem doesn't support or patterns"

let rec typ_needs_printed params_to_print (Typ_aux (t, _)) =
  let typ_needs_printed = typ_needs_printed params_to_print in
  match t with
  | Typ_tuple ts -> List.exists typ_needs_printed ts
  | Typ_app (id, targs) -> begin
      match Bindings.find_opt id params_to_print with
      | Some is when not (Util.IntSet.is_empty is) -> true
      | _ -> List.exists (typ_needs_printed_arg params_to_print) targs
    end
  | Typ_fn (ts, t) -> List.exists typ_needs_printed ts || typ_needs_printed t
  | Typ_exist (kopts, _, t) ->
      let kids = List.map kopt_kid kopts in
      (* TODO: Check this *)
      let visible_kids = KidSet.inter (KidSet.of_list kids) (lem_tyvars_of_typ params_to_print t) in
      typ_needs_printed t && KidSet.is_empty visible_kids
  | _ -> false

and typ_needs_printed_arg params_to_print (A_aux (targ, _)) =
  match targ with A_typ t -> typ_needs_printed params_to_print t | _ -> false

let contains_early_return exp =
  let e_app (f, args) =
    let rets, args = List.split args in
    (List.fold_left ( || ) (string_of_id f = "early_return") rets, E_app (f, args))
  in
  fst
    (fold_exp { (Rewriter.compute_exp_alg false ( || )) with e_return = (fun (_, r) -> (true, E_return r)); e_app } exp)

(* Does the expression have the form of a bitvector cast from the monomorphiser? *)
type is_bitvector_cast = BVC_yes | BVC_allowed | BVC_not
let is_bitvector_cast_out exp =
  let merge x y =
    match (x, y) with
    | BVC_allowed, _ -> y
    | _, BVC_allowed -> x
    | BVC_not, _ -> BVC_not
    | _, BVC_not -> BVC_not
    | _ -> BVC_yes
  in
  let rec aux (E_aux (e, _)) =
    match e with
    | E_tuple es -> List.fold_left merge BVC_allowed (List.map aux es)
    | E_typ (_, e) -> aux e
    | E_app (Id_aux (Id "bitvector_cast_out", _), _) -> BVC_yes
    | E_id _ -> BVC_allowed
    | _ -> BVC_not
  in
  aux exp = BVC_yes

let replace_env_for_cast_out new_env pat = map_pat_annot (fun (l, a) -> (l, replace_env new_env a)) pat

let find_e_ids exp =
  let e_id id = (IdSet.singleton id, E_id id) in
  fst (fold_exp { (compute_exp_alg IdSet.empty IdSet.union) with e_id } exp)

let typ_id_of (Typ_aux (typ, l)) =
  match typ with
  | Typ_id id -> id
  | Typ_app (register, [A_aux (A_typ (Typ_aux (Typ_id id, _)), _)]) when string_of_id register = "register" -> id
  | Typ_app (id, _) -> id
  | _ -> raise (Reporting.err_unreachable l __POS__ "failed to get type id")

let report = Reporting.err_unreachable
let doc_exp_lem, doc_let_lem =
  let rec top_exp (ctxt : context) (aexp_needed : bool) (E_aux (e, (l, annot)) as full_exp) =
    let expY = top_exp ctxt true in
    let expN = top_exp ctxt false in
    let expV = top_exp ctxt in
    let wrap_parens doc = if aexp_needed then parens doc else doc in
    let liftR doc =
      if ctxt.early_ret && effectful (effect_of full_exp) then wrap_parens (separate space [string "liftR"; parens doc])
      else wrap_parens doc
    in
    match e with
    | E_assign ((LE_aux (le_act, tannot) as le), e) -> (
        (* can only be register writes *)
        match le_act (*, t, tag*) with
        | LE_vector_range (le, e2, e3) -> (
            match le with
            | LE_aux (LE_field ((LE_aux (_, lannot) as le), id), fannot) ->
                if is_bit_typ (typ_of_annot fannot) then
                  raise (report l __POS__ "indexing a register's (single bit) bitfield not supported")
                else (
                  let field_ref = doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^ underscore ^^ doc_id_lem id in
                  liftR
                    ((prefix 2 1) (string "write_reg_field_range")
                       (align (doc_lexp_deref_lem ctxt le ^/^ field_ref ^/^ expY e2 ^/^ expY e3 ^/^ expY e))
                    )
                )
            | _ ->
                let deref = doc_lexp_deref_lem ctxt le in
                liftR ((prefix 2 1) (string "write_reg_range") (align (deref ^/^ expY e2 ^/^ expY e3) ^/^ expY e))
          )
        | LE_vector (le, e2) -> (
            match le with
            | LE_aux (LE_field ((LE_aux (_, lannot) as le), id), fannot) ->
                if is_bit_typ (typ_of_annot fannot) then
                  raise (report l __POS__ "indexing a register's (single bit) bitfield not supported")
                else (
                  let field_ref = doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^ underscore ^^ doc_id_lem id in
                  let call =
                    if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot fannot)) then
                      "write_reg_field_bit"
                    else "write_reg_field_pos"
                  in
                  liftR
                    ((prefix 2 1) (string call)
                       (align (doc_lexp_deref_lem ctxt le ^/^ field_ref ^/^ expY e2 ^/^ expY e))
                    )
                )
            | LE_aux (_, lannot) ->
                let deref = doc_lexp_deref_lem ctxt le in
                let call =
                  if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot lannot)) then "write_reg_bit"
                  else "write_reg_pos"
                in
                liftR ((prefix 2 1) (string call) (deref ^/^ expY e2 ^/^ expY e))
          )
        | LE_field ((LE_aux (_, lannot) as le), id) ->
            let field_ref =
              doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^ underscore ^^ doc_id_lem id
              (*^^
                dot ^^
                string "set_field"*)
            in
            liftR ((prefix 2 1) (string "write_reg_field") (doc_lexp_deref_lem ctxt le ^^ space ^^ field_ref ^/^ expY e))
        | LE_deref re -> liftR ((prefix 2 1) (string "write_reg") (expY re ^/^ expY e))
        | _ -> liftR ((prefix 2 1) (string "write_reg") (doc_lexp_deref_lem ctxt le ^/^ expY e))
      )
    | E_vector_append (le, re) ->
        raise (Reporting.err_unreachable l __POS__ "E_vector_append should have been rewritten before pretty-printing")
    | E_cons (le, re) -> wrap_parens (doc_op (group (colon ^^ colon)) (expY le) (expY re))
    | E_if (c, t, e) -> wrap_parens (align (if_exp ctxt false c t e))
    | E_for (id, exp1, exp2, exp3, Ord_aux (order, _), exp4) ->
        raise (report l __POS__ "E_for should have been rewritten before pretty-printing")
    | E_loop _ -> raise (report l __POS__ "E_loop should have been rewritten before pretty-printing")
    | E_let (leb, e) -> wrap_parens (let_exp ctxt leb ^^ space ^^ string "in" ^^ hardline ^^ expN e)
    | E_app (f, args) -> begin
        match f with
        | Id_aux (Id "None", _) as none -> doc_id_lem_ctor none
        | (Id_aux (Id "and_bool", _) | Id_aux (Id "or_bool", _)) when effectful (effect_of full_exp) ->
            let call = doc_id_lem (append_id f "M") in
            wrap_parens (hang 2 (flow (break 1) (call :: List.map expY args)))
        (* temporary hack to make the loop body a function of the temporary variables *)
        | Id_aux (Id "foreach#", _) -> begin
            match args with
            | [exp1; exp2; exp3; ord_exp; vartuple; body] ->
                let loopvar, body =
                  match body with
                  | E_aux
                      ( E_if
                          ( _,
                            E_aux
                              ( E_let
                                  ( LB_aux
                                      ( LB_val
                                          ( ( P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _)
                                            | P_aux (P_var (P_aux (P_id id, _), _), _)
                                            | P_aux (P_id id, _) ),
                                            _
                                          ),
                                        _
                                      ),
                                    body
                                  ),
                                _
                              ),
                            _
                          ),
                        _
                      ) ->
                      (id, body)
                  | _ ->
                      raise
                        (Reporting.err_unreachable l __POS__ ("Unable to find loop variable in " ^ string_of_exp body))
                in
                let step =
                  match ord_exp with
                  | E_aux (E_lit (L_aux (L_false, _)), _) -> parens (separate space [string "integerNegate"; expY exp3])
                  | _ -> expY exp3
                in
                let combinator =
                  if ctxt.monadic && effectful (effect_of body) then "foreachM"
                  else if effectful (effect_of body) then "foreachE"
                  else "foreach"
                in
                let indices_pp = parens (separate space [string "index_list"; expY exp1; expY exp2; step]) in
                let used_vars_body = find_e_ids body in
                let body_lambda =
                  (* Work around indentation issues in Lem when translating
                     tuple or literal unit patterns to Isabelle *)
                  match fst (uncast_exp vartuple) with
                  | E_aux (E_tuple _, _) when not (IdSet.mem (mk_id "varstup") used_vars_body) ->
                      separate space [string "fun"; doc_id_lem loopvar; string "varstup"; arrow]
                      ^^ break 1
                      ^^ separate space [string "let"; expY vartuple; string "= varstup in"]
                  | E_aux (E_lit (L_aux (L_unit, _)), _) when not (IdSet.mem (mk_id "unit_var") used_vars_body) ->
                      separate space [string "fun"; doc_id_lem loopvar; string "unit_var"; arrow]
                  | _ -> separate space [string "fun"; doc_id_lem loopvar; expY vartuple; arrow]
                in
                parens
                  ((prefix 2 1)
                     ((separate space) [string combinator; indices_pp; expY vartuple])
                     (parens (prefix 2 1 (group body_lambda) (expN body)))
                  )
            | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
          end
        | Id_aux (Id (("while#" | "until#" | "while#t" | "until#t") as combinator), _) ->
            let combinator = String.sub combinator 0 (String.index combinator '#') in
            begin
              match args with
              | [cond; varstuple; body] | [cond; varstuple; body; _] ->
                  (* Ignore termination measures - not used in Lem *)
                  let return (E_aux (e, a)) = E_aux (E_internal_return (E_aux (e, a)), a) in
                  let csuffix, cond, body =
                    match (effectful (effect_of cond), effectful (effect_of body)) with
                    | false, false -> ("", cond, body)
                    | false, true -> ("M", return cond, body)
                    | true, false -> ("M", cond, return body)
                    | true, true -> ("M", cond, body)
                  in
                  let used_vars_body = find_e_ids body in
                  let lambda =
                    (* Work around indentation issues in Lem when translating
                       tuple or literal unit patterns to Isabelle *)
                    match fst (uncast_exp varstuple) with
                    | E_aux (E_tuple _, _) when not (IdSet.mem (mk_id "varstup") used_vars_body) ->
                        separate space [string "fun varstup"; arrow]
                        ^^ break 1
                        ^^ separate space [string "let"; expY varstuple; string "= varstup in"]
                    | E_aux (E_lit (L_aux (L_unit, _)), _) when not (IdSet.mem (mk_id "unit_var") used_vars_body) ->
                        separate space [string "fun unit_var"; arrow]
                    | _ -> separate space [string "fun"; expY varstuple; arrow]
                  in
                  parens
                    ((prefix 2 1)
                       ((separate space) [string (combinator ^ csuffix); expY varstuple])
                       ((prefix 0 1)
                          (parens (prefix 2 1 (group lambda) (expN cond)))
                          (parens (prefix 2 1 (group lambda) (expN body)))
                       )
                    )
              | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
            end
        | Id_aux (Id "early_return", _) -> begin
            match args with
            | [exp] ->
                let returner, monad, arg_order =
                  if ctxt.monadic then ("early_return", "MR", fun x -> x) else ("Left", "either", List.rev)
                in
                let epp = separate space [string returner; expY exp] in
                let aexp_needed, tepp =
                  match
                    ( Option.bind (Env.get_ret_typ (env_of exp)) (make_printable_type ctxt ctxt.top_env),
                      make_printable_type ctxt (env_of full_exp) (typ_of full_exp)
                    )
                  with
                  | Some typ, Some full_typ ->
                      let tannot =
                        separate space
                          ([string monad]
                          @ arg_order
                              [
                                doc_atomic_typ_lem ctxt.params_to_print false full_typ;
                                doc_atomic_typ_lem ctxt.params_to_print false typ;
                              ]
                          )
                      in
                      (true, doc_op colon epp tannot)
                  | _ -> (aexp_needed, epp)
                in
                if aexp_needed then parens tepp else tepp
            | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for early_return builtin")
          end
        | _ -> begin
            match destruct_tannot annot with
            | Some (env, typ) when Env.is_union_constructor f env ->
                (* If the union has type variables, we may need an annotation for Lem to typecheck it *)
                (* let _, _, union_id, _ = Env.union_constructor_info f env |> unwrap in
                   let typq, _ = Env.get_variants env |> Bindings.find_opt union_id |> unwrap in *)
                let annotation_needed = false (* List.length (quant_items typq) > 0 *) in
                let wrap_union doc = if aexp_needed || annotation_needed then parens doc else doc in
                let epp =
                  match args with
                  | [] -> doc_id_lem_ctor f
                  | [arg] -> doc_id_lem_ctor f ^^ space ^^ expV true arg
                  | _ -> doc_id_lem_ctor f ^^ space ^^ parens (separate_map comma (expV false) args)
                in
                wrap_union (if annotation_needed then align epp ^^ doc_tannot_lem ctxt env false typ else align epp)
            | _ ->
                let call, is_extern =
                  match destruct_tannot annot with
                  | Some (env, _) when Env.is_extern f env "lem" -> (string (Env.get_extern f env "lem"), true)
                  | _ -> (doc_id_lem f, false)
                in
                let epp = hang 2 (flow (break 1) (call :: List.map expY args)) in
                let taepp, aexp_needed =
                  let env = env_of full_exp in
                  let t = Env.expand_synonyms env (typ_of full_exp) in
                  let eff = effect_of full_exp in
                  if typ_needs_printed ctxt.params_to_print t then
                    if
                      Id.compare f (mk_id "bitvector_cast_out") <> 0
                      && Id.compare f (mk_id "zero_extend_type_hack") <> 0
                    then (align (group (prefix 0 1 epp (doc_tannot_lem ctxt env (effectful eff) t))), true)
                      (* TODO: coordinate with the code in monomorphise.ml to find the correct
                         typing environment to use *)
                    else (align (group (prefix 0 1 epp (doc_tannot_lem ctxt ctxt.top_env (effectful eff) t))), true)
                  else (epp, aexp_needed)
                in
                liftR (if aexp_needed then parens (align taepp) else taepp)
          end
      end
    | E_vector_access (v, e) ->
        raise (Reporting.err_unreachable l __POS__ "E_vector_access should have been rewritten before pretty-printing")
    | E_vector_subrange (v, e1, e2) ->
        raise (Reporting.err_unreachable l __POS__ "E_vector_subrange should have been rewritten before pretty-printing")
    | E_field ((E_aux (_, (l, fannot)) as fexp), id) -> (
        match destruct_tannot fannot with
        | (Some (env, Typ_aux (Typ_id tid, _)) | Some (env, Typ_aux (Typ_app (tid, _), _))) when Env.is_record tid env
          ->
            let fname = doc_fieldname_lem tid id in
            expY fexp ^^ dot ^^ fname
        | _ -> raise (report l __POS__ "E_field expression with no register or record type")
      )
    | E_block [] -> string "()"
    | E_block exps -> raise (report l __POS__ "Blocks should have been removed till now.")
    | E_id id | E_ref id ->
        let env = env_of full_exp in
        let typ = typ_of full_exp in
        let base_typ = Env.base_typ_of env typ in
        if Env.is_register id env && match e with E_id _ -> true | _ -> false then (
          let epp = separate space [string "read_reg"; doc_id_lem (append_id id "_ref")] in
          if is_bitvector_typ base_typ then
            liftR (parens (align (group (prefix 0 1 epp (doc_tannot_lem ctxt env true base_typ)))))
          else liftR epp
        )
        else if Env.is_register id env && match e with E_ref _ -> true | _ -> false then doc_id_lem (append_id id "_ref")
        else if is_ctor env id then doc_id_lem_ctor id
        else doc_id_lem id
    | E_lit lit ->
        let env = env_of full_exp in
        let typ = Env.expand_synonyms env (typ_of full_exp) in
        let eff = effect_of full_exp in
        if typ_needs_printed ctxt.params_to_print typ then
          parens (doc_lit_lem lit ^^ doc_tannot_lem ctxt env (effectful eff) typ)
        else doc_lit_lem lit
    | E_typ (typ, e) ->
        expV aexp_needed
          e (*parens (expN e ^^ doc_tannot_lem ctxt (env_of full_exp) (effectful (effect_of full_exp)) typ)*)
    | E_tuple exps -> parens (align (group (separate_map (comma ^^ break 1) expN exps)))
    | E_struct fexps ->
        let recordtyp, annotation_needed, env, typ =
          match destruct_tannot annot with
          | Some (env, (Typ_aux (Typ_id tid, _) as typ)) -> (tid, false, env, typ)
          (* We need an annotation here because some record type parameters may be phantom *)
          | Some (env, (Typ_aux (Typ_app (tid, _), _) as typ)) -> (tid, true, env, typ)
          | _ ->
              Reporting.unreachable l __POS__
                ("cannot get record type from annot " ^ string_of_tannot annot ^ " of exp " ^ string_of_exp full_exp)
        in
        let wrap_record doc = if aexp_needed || annotation_needed then parens doc else doc in
        wrap_record
          (anglebars (space ^^ align (separate_map (semi_sp ^^ break 1) (doc_fexp ctxt recordtyp) fexps) ^^ space)
          ^^ if annotation_needed then doc_tannot_lem ctxt env false typ else empty
          )
    | E_struct_update (e, fexps) ->
        let recordtyp =
          match destruct_tannot annot with
          | (Some (env, Typ_aux (Typ_id tid, _)) | Some (env, Typ_aux (Typ_app (tid, _), _))) when Env.is_record tid env
            ->
              tid
          | _ ->
              raise
                (report l __POS__
                   ("cannot get record type from annot " ^ string_of_tannot annot ^ " of exp " ^ string_of_exp full_exp)
                )
        in
        anglebars
          (space ^^ doc_op (string "with") (expY e) (separate_map semi_sp (doc_fexp ctxt recordtyp) fexps) ^^ space)
    | E_vector exps ->
        let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
        let _, etyp =
          if is_vector_typ t || is_bitvector_typ t then vector_typ_args_of t
          else raise (Reporting.err_unreachable l __POS__ "E_vector of non-vector type")
        in
        let expspp = align (group (flow_map (semi ^^ break 0) expN exps)) in
        let epp = brackets expspp in
        let epp, aexp_needed =
          if is_bit_typ etyp && !Monomorphise.opt_mwords then (
            let bepp = string "vec_of_bits" ^^ space ^^ align epp in
            (align (group (prefix 0 1 bepp (doc_tannot_lem ctxt (env_of full_exp) false t))), true)
          )
          else (epp, aexp_needed)
        in
        if aexp_needed then parens (align epp) else epp
    | E_vector_update (v, e1, e2) ->
        raise (Reporting.err_unreachable l __POS__ "E_vector_update should have been rewritten before pretty-printing")
    | E_vector_update_subrange (v, e1, e2, e3) ->
        raise (Reporting.err_unreachable l __POS__ "E_vector_update should have been rewritten before pretty-printing")
    | E_list exps -> brackets (separate_map semi expN exps)
    | E_match (e, pexps) ->
        let only_integers e = expY e in
        wrap_parens
          (group
             (separate space [string "match"; only_integers e; string "with"]
             ^/^ separate_map (break 1) (doc_case ctxt) pexps
             ^/^ string "end"
             )
          )
    | E_try (e, pexps) ->
        if effectful (effect_of e) then (
          let try_catch = if ctxt.early_ret then "try_catchR" else "try_catch" in
          wrap_parens
            (group
               (separate space [string try_catch; expY e; string "(function "]
               ^/^ separate_map (break 1) (doc_case ctxt) pexps
               ^/^ string "end)"
               )
            )
        )
        else raise (Reporting.err_todo l "Warning: try-block around pure expression")
    | E_throw e -> align (liftR (separate space [string "throw"; expY e]))
    | E_exit e -> liftR (separate space [string "exit"; expY e])
    | E_assert (e1, e2) -> align (liftR (separate space [string "assert_exp"; expY e1; expY e2]))
    | E_app_infix (e1, id, e2) -> expV aexp_needed (E_aux (E_app (deinfix id, [e1; e2]), (l, annot)))
    | E_var (lexp, eq_exp, in_exp) -> raise (report l __POS__ "E_vars should have been removed before pretty-printing")
    | E_internal_plet (pat, e1, e2) ->
        let bind, bind_unit = if ctxt.monadic then (">>=", ">>") else (">>$=", ">>$") in
        let epp =
          let b = match e1 with E_aux (E_if _, _) -> true | _ -> false in
          let middle =
            match fst (untyp_pat pat) with
            | (P_aux (P_wild, _) | P_aux (P_typ (_, P_aux (P_wild, _)), _)) when is_unit_typ (typ_of_pat pat) ->
                string bind_unit
            | P_aux (P_tuple _, _) when not (IdSet.mem (mk_id "varstup") (find_e_ids e2)) ->
                (* Work around indentation issues in Lem when translating
                   tuple patterns to Isabelle *)
                separate space [string (bind ^ " fun varstup -> let"); doc_pat_lem ctxt true pat; string "= varstup in"]
            | _ -> separate space [string (bind ^ " fun"); doc_pat_lem ctxt true pat; arrow]
          in
          infix 0 1 middle (expV b e1) (expN e2)
        in
        wrap_parens (align epp)
    | E_internal_return e1 ->
        let return = if ctxt.monadic then "return" else "Right" in
        wrap_parens (align (separate space [string return; expY e1]))
    | E_sizeof nexp -> (
        match nexp_simp nexp with
        | Nexp_aux (Nexp_constant i, _) -> doc_lit_lem (L_aux (L_num i, l))
        | _ ->
            raise
              (Reporting.err_unreachable l __POS__
                 "pretty-printing non-constant sizeof expressions to Lem not supported"
              )
      )
    | E_return r ->
        let ta =
          match
            ( Option.bind (Env.get_ret_typ (env_of full_exp)) (make_printable_type ctxt ctxt.top_env),
              make_printable_type ctxt (env_of r) (typ_of r)
            )
          with
          | Some full_typ, Some r_typ ->
              separate space
                [
                  string ": MR";
                  parens (doc_typ_lem ctxt.params_to_print (env_of full_exp) full_typ);
                  parens (doc_typ_lem ctxt.params_to_print (env_of r) r_typ);
                ]
          | _ -> empty
        in
        align (parens (string "early_return" ^//^ expV true r ^//^ ta))
    | E_constraint _ -> string "true"
    | E_internal_assume (nc, e1) ->
        string "(* " ^^ string (string_of_n_constraint nc) ^^ string " *)" ^/^ wrap_parens (expN e1)
    | E_internal_value _ ->
        raise (Reporting.err_unreachable l __POS__ "unsupported internal expression encountered while pretty-printing")
  and if_exp ctxt (elseif : bool) c t e =
    let if_pp = string (if elseif then "else if" else "if") in
    let else_pp =
      match e with
      | E_aux (E_if (c', t', e'), _) | E_aux (E_typ (_, E_aux (E_if (c', t', e'), _)), _) -> if_exp ctxt true c' t' e'
      (* Special case to prevent current arm decoder becoming a staircase *)
      (* TODO: replace with smarter pretty printing *)
      | E_aux (E_internal_plet (pat, exp1, E_aux (E_typ (typ, (E_aux (E_if (_, _, _), _) as exp2)), _)), ann)
        when Typ.compare typ unit_typ == 0 ->
          string "else" ^/^ top_exp ctxt false (E_aux (E_internal_plet (pat, exp1, exp2), ann))
      | _ -> prefix 2 1 (string "else") (top_exp ctxt false e)
    in
    prefix 2 1 (soft_surround 2 1 if_pp (top_exp ctxt true c) (string "then")) (top_exp ctxt false t)
    ^^ break 1 ^^ else_pp
  and let_exp ctxt (LB_aux (lb, _)) =
    match lb with
    | LB_val (pat, e) ->
        let pat = if is_bitvector_cast_out e then replace_env_for_cast_out ctxt.top_env pat else pat in
        prefix 2 1 (separate space [string "let"; doc_pat_lem ctxt true pat; equals]) (top_exp ctxt false e)
  and doc_fexp ctxt recordtyp (FE_aux (FE_fexp (id, e), _)) =
    let fname = doc_fieldname_lem recordtyp id in
    group (doc_op equals fname (top_exp ctxt true e))
  and doc_case ctxt = function
    | Pat_aux (Pat_exp (pat, e), _) ->
        group (prefix 3 1 (separate space [pipe; doc_pat_lem ctxt false pat; arrow]) (group (top_exp ctxt false e)))
    | Pat_aux (Pat_when (_, _, _), (l, _)) ->
        raise
          (Reporting.err_unreachable l __POS__
             "guarded pattern expression should have been rewritten before pretty-printing"
          )
  and doc_lexp_deref_lem ctxt (LE_aux (lexp, (l, annot))) =
    match lexp with
    | LE_field (le, id) -> parens (separate empty [doc_lexp_deref_lem ctxt le; dot; doc_id_lem id])
    | LE_id id -> doc_id_lem (append_id id "_ref")
    | LE_typ (typ, id) -> doc_id_lem (append_id id "_ref")
    | LE_tuple lexps -> parens (separate_map comma_sp (doc_lexp_deref_lem ctxt) lexps)
    | _ -> raise (Reporting.err_unreachable l __POS__ "doc_lexp_deref_lem: Unsupported lexp")
    (* expose doc_exp_lem and doc_let *)
  in
  (top_exp, let_exp)

(*TODO Upcase and downcase type and constructors as needed*)
let doc_type_union_lem params_to_print env (Tu_aux (Tu_ty_id (typ, id), _)) =
  separate space [pipe; doc_id_lem_ctor id; string "of"; parens (doc_typ_lem params_to_print env typ)]

(*
let rec doc_range_lem (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)
 *)

let doc_typquant_sorts idpp (TypQ_aux (typq, _)) =
  match typq with
  | TypQ_tq qs ->
      let q (QI_aux (qi, _)) =
        match qi with
        | QI_id (KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _)) -> Some (string "`len`")
        | QI_id (KOpt_aux (KOpt_kind (K_aux (K_type, _), kid), _)) -> Some underscore
        | QI_id (KOpt_aux (KOpt_kind (K_aux (K_bool, _), kid), _)) -> None
        | QI_constraint _ -> None
      in
      if
        List.exists
          (function QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_int, _), _), _)), _) -> true | _ -> false)
          qs
      then (
        let qs_pp = List.filter_map q qs in
        string "declare isabelle target_sorts " ^^ idpp ^^ space ^^ separate space (equals :: qs_pp) ^^ hardline
      )
      else empty
  | TypQ_no_forall -> empty

let doc_sia_id (Id_aux (i, _)) = match i with Id i -> string i | Operator x -> string ("operator " ^ x)

let typq_to_print params_to_print id typq =
  match Bindings.find_opt id params_to_print with
  | None -> typq
  | Some is -> (
      match typq with
      | TypQ_aux (TypQ_no_forall, _) -> typq
      | TypQ_aux (TypQ_tq qs, l) ->
          List.fold_left
            (fun (t, i) h ->
              if is_quant_kopt h then if Util.IntSet.mem i is then (h :: t, i + 1) else (t, i + 1) else (t, i)
            )
            ([], 0) qs
          |> fst |> List.rev
          |> fun qs -> TypQ_aux (TypQ_tq qs, l)
    )

let doc_typdef_lem params_to_print env (TD_aux (td, (l, annot))) =
  match td with
  | TD_abbrev (id, typq, A_aux (A_typ typ, _)) ->
      let typq_to_print = typq_to_print params_to_print id typq in
      let typschm = TypSchm_aux (TypSchm_ts (typq, typ), l) in
      let sorts_pp = doc_typquant_sorts (doc_id_lem_type id) typq_to_print in
      doc_op equals
        (separate space
           [string "type"; doc_id_lem_type id; doc_typquant_items_lem (kid_nexps_of_typquant typq_to_print)]
        )
        (doc_typschm_lem params_to_print env false typschm)
      ^^ hardline ^^ sorts_pp
  | TD_abbrev _ -> empty
  | TD_record (id, typq, fs, _) ->
      let f_pp (typ, fid) =
        concat [doc_fieldname_lem id fid; space; colon; space; doc_typ_lem params_to_print env typ; semi]
      in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      let typq_to_print = typq_to_print params_to_print id typq in
      let sorts_pp = doc_typquant_sorts (doc_id_lem_type id) typq_to_print in
      doc_op equals
        (separate space
           [string "type"; doc_id_lem_type id; doc_typquant_items_lem (kid_nexps_of_typquant typq_to_print)]
        )
        (anglebars (space ^^ align fs_doc ^^ space))
      ^^ hardline ^^ sorts_pp
      (* if !opt_sequential && string_of_id id = "regstate" then empty
         else separate_map hardline doc_field fs *)
  | TD_variant (id, typq, ar, _) -> (
      match id with
      | Id_aux (Id "read_kind", _) -> empty
      | Id_aux (Id "write_kind", _) -> empty
      | Id_aux (Id "a64_barrier_domain", _) -> empty
      | Id_aux (Id "a64_barrier_type", _) -> empty
      | Id_aux (Id "barrier_kind", _) -> empty
      | Id_aux (Id "trans_kind", _) -> empty
      | Id_aux (Id "instruction_kind", _) -> empty
      | Id_aux (Id "option", _) -> empty
      | _ ->
          let env = Env.add_typquant l typq env in
          let ar_doc = group (separate_map (break 1) (doc_type_union_lem params_to_print env) ar) in
          let typq_to_print = typq_to_print params_to_print id typq in
          let typ_pp =
            (doc_op equals)
              (concat
                 [
                   string "type";
                   space;
                   doc_id_lem_type id;
                   space;
                   doc_typquant_items_lem (kid_nexps_of_typquant typq_to_print);
                 ]
              )
              ar_doc
          in
          let make_id pat id =
            separate space
              [
                string "SIA.Id_aux";
                parens (string "SIA.Id " ^^ string_lit (doc_sia_id id));
                (if pat then underscore else string "SIA.Unknown");
              ]
          in
          let fromInterpValueF = concat [doc_id_lem_type id; string "FromInterpValue"] in
          let toInterpValueF = concat [doc_id_lem_type id; string "ToInterpValue"] in
          let fromInterpValuePP =
            (prefix 2 1)
              (separate space [string "let rec"; fromInterpValueF; string "v"; equals; string "match v with"])
              ((separate_map (break 1))
                 (fun (Tu_aux (Tu_ty_id (ty, cid), _)) ->
                   (separate space)
                     [
                       pipe;
                       string "SI.V_ctor";
                       parens (make_id true cid);
                       underscore;
                       underscore;
                       string "v";
                       arrow;
                       doc_id_lem_ctor cid;
                       parens (string "fromInterpValue v");
                     ]
                 )
                 ar
              ^/^ (separate space) [pipe; string "SI.V_tuple [v]"; arrow; fromInterpValueF; string "v"]
              ^/^
              let failmessage =
                string_lit
                  (concat
                     [string "fromInterpValue"; space; doc_id_lem_type id; colon; space; string "unexpected value. "]
                  )
                ^^ string " ^ Interp.debug_print_value v"
              in
              (separate space) [pipe; string "v"; arrow; string "failwith"; parens failmessage] ^/^ string "end"
              )
          in
          let toInterpValuePP =
            (prefix 2 1)
              (separate space [string "let"; toInterpValueF; equals; string "function"])
              ((separate_map (break 1))
                 (fun (Tu_aux (Tu_ty_id (ty, cid), _)) ->
                   (separate space)
                     [
                       pipe;
                       doc_id_lem_ctor cid;
                       string "v";
                       arrow;
                       string "SI.V_ctor";
                       parens (make_id false cid);
                       parens (string "SIA.T_id " ^^ string_lit (doc_sia_id id));
                       string "SI.C_Union";
                       parens (string "toInterpValue v");
                     ]
                 )
                 ar
              ^/^ string "end"
              )
          in
          let fromToInterpValuePP =
            (prefix 2 1)
              (concat [string "instance "; parens (string "ToFromInterpValue " ^^ doc_id_lem_type id)])
              (concat
                 [
                   string "let toInterpValue = ";
                   toInterpValueF;
                   hardline;
                   string "let fromInterpValue = ";
                   fromInterpValueF;
                 ]
              )
            ^/^ string "end"
          in
          typ_pp ^^ hardline ^^ hardline
          ^^
          if !print_to_from_interp_value then
            toInterpValuePP ^^ hardline ^^ hardline ^^ fromInterpValuePP ^^ hardline ^^ hardline ^^ fromToInterpValuePP
            ^^ hardline
          else empty
    )
  | TD_enum (id, enums, _) -> (
      match id with
      | Id_aux (Id "read_kind", _) -> empty
      | Id_aux (Id "write_kind", _) -> empty
      | Id_aux (Id "a64_barrier_domain", _) -> empty
      | Id_aux (Id "a64_barrier_type", _) -> empty
      | Id_aux (Id "barrier_kind", _) -> empty
      | Id_aux (Id "trans_kind", _) -> empty
      | Id_aux (Id "instruction_kind", _) -> empty
      | Id_aux (Id "cache_op_kind", _) -> empty
      | Id_aux (Id "regfp", _) -> empty
      | Id_aux (Id "niafp", _) -> empty
      | Id_aux (Id "diafp", _) -> empty
      | _ ->
          let rec range i j = if i > j then [] else i :: range (i + 1) j in
          let nats = range 0 in
          let enums_doc = group (pipe ^^ space ^^ separate_map (break 1 ^^ pipe ^^ space) doc_id_lem_ctor enums) in
          let typ_pp = (doc_op equals) (concat [string "type"; space; doc_id_lem_type id]) enums_doc in
          let fromInterpValueF = concat [doc_id_lem_type id; string "FromInterpValue"] in
          let toInterpValueF = concat [doc_id_lem_type id; string "ToInterpValue"] in
          let make_id pat id =
            separate space
              [
                string "SIA.Id_aux";
                parens (string "SIA.Id " ^^ string_lit (doc_sia_id id));
                (if pat then underscore else string "SIA.Unknown");
              ]
          in
          let fromInterpValuePP =
            (prefix 2 1)
              (separate space [string "let rec"; fromInterpValueF; string "v"; equals; string "match v with"])
              ((separate_map (break 1))
                 (fun cid ->
                   (separate space)
                     [
                       pipe;
                       string "SI.V_ctor";
                       parens (make_id true cid);
                       underscore;
                       underscore;
                       string "v";
                       arrow;
                       doc_id_lem_ctor cid;
                     ]
                 )
                 enums
              ^/^ align
                    ((prefix 3 1)
                       (separate space [pipe; string "SI.V_lit (SIA.L_aux (SIA.L_num n) _)"; arrow])
                       (separate space [string "match"; parens (string "natFromInteger n"); string "with"]
                       ^/^ (separate_map (break 1))
                             (fun (cid, number) ->
                               (separate space) [pipe; string (string_of_int number); arrow; doc_id_lem_ctor cid]
                             )
                             (List.combine enums (nats (List.length enums - 1)))
                       ^/^ string "end"
                       )
                    )
              ^/^ (separate space) [pipe; string "SI.V_tuple [v]"; arrow; fromInterpValueF; string "v"]
              ^/^
              let failmessage =
                string_lit
                  (concat
                     [string "fromInterpValue"; space; doc_id_lem_type id; colon; space; string "unexpected value. "]
                  )
                ^^ string " ^ Interp.debug_print_value v"
              in
              (separate space) [pipe; string "v"; arrow; string "failwith"; parens failmessage] ^/^ string "end"
              )
          in
          let toInterpValuePP =
            (prefix 2 1)
              (separate space [string "let"; toInterpValueF; equals; string "function"])
              ((separate_map (break 1))
                 (fun (cid, number) ->
                   (separate space)
                     [
                       pipe;
                       doc_id_lem_ctor cid;
                       arrow;
                       string "SI.V_ctor";
                       parens (make_id false cid);
                       parens (string "SIA.T_id " ^^ string_lit (doc_sia_id id));
                       parens (string ("SI.C_Enum " ^ string_of_int number));
                       parens (string "toInterpValue ()");
                     ]
                 )
                 (List.combine enums (nats (List.length enums - 1)))
              ^/^ string "end"
              )
          in
          let fromToInterpValuePP =
            (prefix 2 1)
              (concat [string "instance "; parens (string "ToFromInterpValue " ^^ doc_id_lem_type id)])
              (concat
                 [
                   string "let toInterpValue = ";
                   toInterpValueF;
                   hardline;
                   string "let fromInterpValue = ";
                   fromInterpValueF;
                 ]
              )
            ^/^ string "end"
          in
          typ_pp ^^ hardline ^^ hardline
          ^^
          if !print_to_from_interp_value then
            toInterpValuePP ^^ hardline ^^ hardline ^^ fromInterpValuePP ^^ hardline ^^ hardline ^^ fromToInterpValuePP
            ^^ hardline
          else empty
    )
  | _ -> raise (Reporting.err_unreachable l __POS__ "register with non-constant indices")

let args_of_typs l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    (P_aux (P_id id, (l, mk_tannot env typ)), E_aux (E_id id, (l, mk_tannot env typ)))
  in
  List.split (List.mapi arg typs)

let rec untuple_args_pat (P_aux (paux, ((l, _) as annot)) as pat) arg_typs =
  let env = env_of_annot annot in
  let identity body = body in
  match (paux, arg_typs) with
  | P_tuple [], _ ->
      let annot = (l, mk_tannot Env.empty unit_typ) in
      ([P_aux (P_lit (mk_lit L_unit), annot)], identity)
  | P_wild, _ :: _ :: _ ->
      let wild typ = P_aux (P_wild, (l, mk_tannot env typ)) in
      (List.map wild arg_typs, identity)
  | P_typ (_, pat), _ -> untuple_args_pat pat arg_typs
  | P_as _, _ :: _ :: _ | P_id _, _ :: _ :: _ ->
      let argpats, argexps = args_of_typs l env arg_typs in
      let argexp = E_aux (E_tuple argexps, annot) in
      let bindargs (E_aux (_, bannot) as body) = E_aux (E_let (LB_aux (LB_val (pat, argexp), annot), body), bannot) in
      (argpats, bindargs)
  (* The type checker currently has a special case for a single arg type; if
     that is removed, then remove the next case. *)
  | P_tuple pats, [_] -> ([pat], identity)
  | P_tuple pats, _ -> (pats, identity)
  | _, _ -> ([pat], identity)

let doc_tannot_opt_lem params_to_print env (Typ_annot_opt_aux (t, _)) =
  match t with
  | Typ_annot_opt_some (tq, typ) -> (*doc_typquant_lem tq*) doc_typ_lem params_to_print env typ
  | Typ_annot_opt_none -> empty

let doc_fun_body_lem ctxt exp =
  let doc_exp = doc_exp_lem ctxt false exp in
  if ctxt.early_ret && ctxt.monadic then align (string "catch_early_return" ^//^ parens doc_exp)
  else if ctxt.early_ret then align (string "pure_early_return" ^//^ parens doc_exp)
  else doc_exp

let doc_funcl_lem monadic params_to_print type_env (FCL_aux (FCL_funcl (id, pexp), (def_annot, _))) =
  let l = def_annot.loc in
  let tq, typ =
    try Env.get_val_spec_orig id type_env
    with _ -> raise (unreachable l __POS__ ("Could not get val-spec of " ^ string_of_id id))
  in
  let arg_typs =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, typ_ret), _) -> arg_typs
    | Typ_aux (_, l) -> raise (unreachable l __POS__ "Non-function type for funcl")
  in
  let pat, guard, exp, (l, _) = destruct_pexp pexp in
  let ctxt =
    {
      early_ret = contains_early_return exp;
      monadic;
      bound_nexps = NexpSet.union (lem_nexps_of_typ params_to_print typ) (typeclass_nexps params_to_print typ);
      top_env = type_env;
      params_to_print;
    }
  in
  let pats, bind = untuple_args_pat pat arg_typs in
  let patspp = separate_map space (doc_pat_lem ctxt true) pats in
  let wrap_monadic =
    if monadic && not (effectful (effect_of exp)) then fun doc -> string "return" ^^ space ^^ parens doc
    else fun doc -> doc
  in
  let _ =
    match guard with
    | None -> ()
    | _ ->
        raise
          (Reporting.err_unreachable l __POS__
             "guarded pattern expression should have been rewritten before pretty-printing"
          )
  in
  group (prefix 3 1 (separate space [doc_id_lem id; patspp; equals]) (wrap_monadic (doc_fun_body_lem ctxt (bind exp))))

let get_id = function [] -> failwith "FD_function with empty list" | FCL_aux (FCL_funcl (id, _), _) :: _ -> id

module StringSet = Set.Make (String)

(* Strictly speaking, Lem doesn't support multiple clauses for a single function
   joined by "and", although it has worked for Isabelle before.  However, all
   the funcls should have been merged by the merge_funcls rewrite now. *)
let doc_fundef_rhs_lem monadic params_to_print env (FD_aux (FD_function (r, typa, funcls), fannot)) =
  separate_map (hardline ^^ string "and ") (doc_funcl_lem monadic params_to_print env) funcls

let doc_mutrec_lem effect_info params_to_print env = function
  | [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "Empty internal_mutrec"
  | fundef :: _ as fundefs ->
      let id = id_of_fundef fundef in
      let required_monadic = not (Effects.function_is_pure id effect_info) in
      string "let rec "
      ^^ separate_map (hardline ^^ string "and ") (doc_fundef_rhs_lem required_monadic params_to_print env) fundefs

let doc_fundef_lem effect_info params_to_print env (FD_aux (FD_function (r, typa, fcls), fannot) as fd) =
  match fcls with
  | [] -> Reporting.unreachable (fst fannot) __POS__ "FD_function with empty function list"
  | FCL_aux (FCL_funcl (id, pexp), annot) :: _ when not (Env.is_extern id env "lem") ->
      (* A function is required to be monadic if Sail thinks it is impure *)
      let required_monadic = not (Effects.function_is_pure id effect_info) in
      (* Output "rec" modifier if function calls itself.  Mutually recursive
         functions are handled separately by doc_mutrec_lem. *)
      let is_funcl_rec =
        fold_pexp
          {
            (pure_exp_alg false ( || )) with
            e_app = (fun (id', args) -> List.fold_left ( || ) (Id.compare id id' = 0) args);
            e_app_infix = (fun (l, id', r) -> l || Id.compare id id' = 0 || r);
          }
          pexp
      in
      let doc_rec = if is_funcl_rec then [string "rec"] else [] in
      separate space ([string "let"] @ doc_rec @ [doc_fundef_rhs_lem required_monadic params_to_print env fd])
  | _ -> empty

let doc_dec_lem (DEC_aux (reg, (l, _))) = match reg with DEC_reg (typ, id, _) -> empty

let doc_spec_lem effect_info params_to_print env (VS_aux (valspec, annot)) =
  match valspec with
  | VS_val_spec (typschm, id, exts) when Ast_util.extern_assoc "lem" exts = None ->
      let monad = if Effects.function_is_pure id effect_info then empty else string "M" ^^ space in
      (* let (TypSchm_aux (TypSchm_ts (tq, typ), _)) = typschm in
         if contains_t_pp_var typ then empty else *)
      separate space [string "val"; doc_id_lem id; string ":"; doc_typschm_lem ~monad params_to_print env true typschm]
      ^/^ hardline
  (* | VS_val_spec (_,_,Some _) -> empty *)
  | _ -> empty

let is_field_accessor regtypes fdef =
  let is_field_of regtyp field =
    List.exists
      (fun (tname, (_, _, fields)) -> tname = regtyp && List.exists (fun (_, fid) -> string_of_id fid = field) fields)
      regtypes
  in
  match Util.split_on_char '_' (string_of_id (id_of_fundef fdef)) with
  | [access; regtyp; field] -> (access = "get" || access = "set") && is_field_of regtyp field
  | _ -> false

let int_of_field_index tname fid nexp =
  match int_of_nexp_opt nexp with
  | Some i -> i
  | None ->
      raise
        (Reporting.err_typ Parse_ast.Unknown
           ("Non-constant bitfield index in field " ^ string_of_id fid ^ " of " ^ tname)
        )

let doc_regtype_fields (tname, (n1, n2, fields)) =
  let const_int fid idx = int_of_field_index tname fid idx in
  let i1, i2 =
    match (n1, n2) with
    | Nexp_aux (Nexp_constant i1, _), Nexp_aux (Nexp_constant i2, _) -> (i1, i2)
    | _ -> raise (Reporting.err_typ Parse_ast.Unknown ("Non-constant indices in register type " ^ tname))
  in
  let dir_b = i1 < i2 in
  let dir = if dir_b then "true" else "false" in
  let doc_field (fr, fid) =
    let i, j =
      match fr with
      | BF_aux (BF_single i, _) ->
          let i = const_int fid i in
          (i, i)
      | BF_aux (BF_range (i, j), _) -> (const_int fid i, const_int fid j)
      | _ ->
          raise
            (Reporting.err_unreachable Parse_ast.Unknown __POS__
               ("Unsupported type in field " ^ string_of_id fid ^ " of " ^ tname)
            )
    in
    let fsize = Big_int.succ (Big_int.abs (Big_int.sub i j)) in
    let ftyp = bitvector_typ (nconstant fsize) in
    let reftyp =
      mk_typ
        (Typ_app
           ( Id_aux (Id "field_ref", Parse_ast.Unknown),
             [mk_typ_arg (A_typ (mk_id_typ (mk_id tname))); mk_typ_arg (A_typ ftyp)]
           )
        )
    in
    let rfannot = doc_tannot_lem empty_ctxt Env.empty false reftyp in
    doc_op equals
      (concat [string "let "; parens (concat [string tname; underscore; doc_id_lem fid; rfannot])])
      (concat
         [
           space;
           langlebar;
           string " field_name = \"" ^^ doc_id_lem fid ^^ string "\";";
           hardline;
           space;
           space;
           space;
           string (" field_start = " ^ Big_int.to_string i ^ ";");
           hardline;
           space;
           space;
           space;
           string (" field_is_inc = " ^ dir ^ ";");
           hardline;
           space;
           space;
           space;
           string (" get_field = get_" ^ tname ^ "_" ^ string_of_id fid ^ ";");
           hardline;
           space;
           space;
           space;
           string (" set_field = set_" ^ tname ^ "_" ^ string_of_id fid ^ " ");
           ranglebar;
         ]
      )
  in
  separate_map hardline doc_field fields

let doc_def_lem effect_info params_to_print type_env (DEF_aux (aux, _) as def) =
  match aux with
  | DEF_val v_spec -> doc_spec_lem effect_info params_to_print type_env v_spec
  | DEF_fixity _ -> empty
  | DEF_overload _ -> empty
  | DEF_type t_def ->
      if List.mem (string_of_id (id_of_type_def t_def)) !opt_extern_types then empty
      else group (doc_typdef_lem params_to_print type_env t_def) ^/^ hardline
  | DEF_register dec -> group (doc_dec_lem dec)
  | DEF_default df -> empty
  | DEF_fundef fdef -> group (doc_fundef_lem effect_info params_to_print type_env fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec_lem effect_info params_to_print type_env fundefs ^/^ hardline
  | DEF_let (LB_aux (LB_val (pat, _), _) as lbind) ->
      group (doc_let_lem { empty_ctxt with params_to_print } lbind) ^/^ hardline
  | DEF_scattered sdef -> unreachable (def_loc def) __POS__ "doc_def_lem: shoulnd't have DEF_scattered at this point"
  | DEF_mapdef (MD_aux (_, (l, _))) -> unreachable l __POS__ "Lem doesn't support mappings"
  | DEF_outcome _ | DEF_impl _ | DEF_instantiation _ ->
      unreachable (def_loc def) __POS__ "Event definition found when generating lem"
  | DEF_pragma _ -> empty
  | DEF_measure _ -> empty (* we might use these in future *)
  | DEF_loop_measures _ -> empty

let find_exc_typ defs =
  let is_exc_typ_def = function
    | DEF_aux (DEF_type td, _) -> string_of_id (id_of_type_def td) = "exception"
    | _ -> false
  in
  if List.exists is_exc_typ_def defs then "exception" else "unit"

let pp_ast_lem (types_file, types_modules) (defs_file, defs_modules) effect_info type_env ({ defs; _ } as ast)
    concurrency_monad_params top_line =
  (* let regtypes = find_regtypes d in *)
  let state_ids = State.generate_regstate_defs type_env ast |> val_spec_ids in
  let is_state_def = function
    | DEF_aux (DEF_val vs, _) -> IdSet.mem (id_of_val_spec vs) state_ids
    | DEF_aux (DEF_fundef fd, _) -> IdSet.mem (id_of_fundef fd) state_ids
    | _ -> false
  in
  let is_typ_def = function DEF_aux (DEF_type _, _) -> true | _ -> false in
  let exc_typ = find_exc_typ defs in
  let params_to_print = type_parameters_to_print type_env defs in
  let typdefs, defs = List.partition is_typ_def defs in
  let statedefs, defs = List.partition is_state_def defs in
  let register_ref_tannot typ =
    string " : register_ref regstate register_value " ^^ parens (doc_typ_lem params_to_print type_env typ)
  in
  let register_refs = State.register_refs_lem register_ref_tannot type_env (State.find_registers defs) in
  let extra_monad_params =
    match concurrency_monad_params with
    | None -> empty
    | Some params ->
        let open Monad_params in
        space
        ^^ separate_map space
             (doc_typ_lem_brackets params_to_print type_env)
             [
               params.abort_type;
               params.barrier_type;
               params.cache_op_type;
               params.fault_type;
               params.pa_type;
               params.tlbi_type;
               params.translation_summary_type;
               params.arch_ak_type;
             ]
  in

  (print types_file)
    (concat
       [
         string "(*" ^^ string top_line ^^ string "*)";
         hardline;
         (separate_map hardline) (fun lib -> separate space [string "open import"; string lib]) types_modules;
         hardline;
         ( if !print_to_from_interp_value then
             concat
               [
                 (separate_map hardline)
                   (fun lib -> separate space [string "     import"; string lib])
                   ["Interp"; "Interp_ast"];
                 string "open import Deep_shallow_convert";
                 hardline;
                 hardline;
                 string "module SI = Interp";
                 hardline;
                 string "module SIA = Interp_ast";
                 hardline;
                 hardline;
               ]
           else empty
         );
         separate empty (List.map (doc_def_lem effect_info params_to_print type_env) typdefs);
         hardline;
         hardline;
         separate empty (List.map (doc_def_lem effect_info params_to_print type_env) statedefs);
         hardline;
         hardline;
         State.regval_instance_lem;
         hardline;
         register_refs;
         hardline;
         concat
           [
             string "type MR 'a 'r = base_monadR" ^^ extra_monad_params
             ^^ string (" register_value regstate 'a 'r " ^ exc_typ);
             hardline;
             string "type M 'a = base_monad" ^^ extra_monad_params ^^ string (" register_value regstate 'a " ^ exc_typ);
             hardline;
           ];
       ]
    );
  (print defs_file)
    (concat
       [
         string "(*" ^^ string top_line ^^ string "*)";
         hardline;
         (separate_map hardline) (fun lib -> separate space [string "open import"; string lib]) defs_modules;
         hardline;
         hardline;
         separate empty (List.map (doc_def_lem effect_info params_to_print type_env) defs);
         hardline;
       ]
    )
