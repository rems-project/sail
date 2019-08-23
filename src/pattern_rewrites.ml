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

module Big_int = Nat_big_num

open Ast
open Ast_util
open Rewriter

let typ_gen = QCheck.Gen.(sized @@ fix
  (fun self n ->
    let base_typ =
      frequency
        [8, (int_range 0 32 >>= fun n -> return (bitvector_typ (nint n) dec_ord));
         4, return bit_typ;
         4, return int_typ;
         2, return bool_typ;
         1, return unit_typ;
         1, return string_typ]
    in
    match n with
    | 0 -> base_typ
    | n ->
       frequency
         [16, base_typ;
          4, list_size (int_range 2 9) (self (n / 2)) >>= (fun typs -> return (tuple_typ typs));
          2, map list_typ (self (n / 2))]
  ))

let rec sequence =
  QCheck.Gen.(function x :: xs -> x >>= fun y -> sequence xs >>= fun ys -> return (y :: ys) | [] -> return [])

let rec split_length len depth =
  let open QCheck.Gen in
  if len = 0 || depth = 0 then (
    return [len]
  ) else (
    int_range 0 (len - 1) >>= fun split ->
    split_length split (depth - 1) >>= fun xs ->
    split_length (len - split) (depth - 1) >>= fun ys ->
    return (xs @ ys)
  )

           (*
let () =
  QCheck.Gen.generate ~n:20 (split_length 10 2)
  |> List.iter (fun nexp -> prerr_endline (Util.string_of_list ", " string_of_int nexp))
            *)

let is_literal = function
  | P_aux (P_lit _, _) -> true
  | _ -> false

let rec pattern_gen infer n (Typ_aux (aux, _) as typ) =
  let open QCheck.Gen in
  let open Value in
  let open Sail_lib in
  let gen_bits_literal len =
    list_repeat len (oneofl [B0; B1])
    |> map (fun bits -> mk_vector bits, mk_pat (P_lit (mk_lit (L_bin (String.concat "" (List.map string_of_bit bits))))))
  in
  let rec combine_vectors = function
    | V_vector xs :: xxs -> xs @ combine_vectors xxs
    | _ :: _ -> assert false
    | [] -> []
  in
  let gen = match aux with
    | Typ_app (id, [A_aux (A_nexp nexp, _); A_aux (A_order ord, _)]) when string_of_id id = "bitvector" ->
       begin match nexp with
       | Nexp_aux (Nexp_constant c, _) ->
          let c = Big_int.to_int c in
          if c = 0 then
            return (V_vector [], mk_pat P_wild)
          else if c < 10 then
            frequency
              [1, gen_bits_literal c;
               1, list_repeat c (pattern_gen infer (n - 1) bit_typ) |> map (fun gens -> V_vector (List.map fst gens), mk_pat (P_vector (List.map snd gens)))]
          else
            frequency
              [1, gen_bits_literal c;
               1, int_range 2 4 >>= fun depth ->
                  split_length c depth >>= fun splits ->
                  sequence (List.map (fun len -> let typ = bitvector_typ (nint len) dec_ord in pattern_gen true (n - 1) typ) splits) >>= fun gens ->
                  return (V_vector (combine_vectors (List.map fst gens)), mk_pat (P_vector_concat (List.map snd gens)))]
       | _ -> assert false
       end
    | Typ_id id when string_of_id id = "bool" ->
       oneof [return (V_bool true, mk_pat (P_lit (mk_lit L_true)));
              return (V_bool false, mk_pat (P_lit (mk_lit L_false)));
              oneofl [true; false] >>= fun bool -> return (V_bool bool, mk_pat P_wild)]
    | Typ_id id when string_of_id id = "bit" ->
       oneof [return (V_bit B1, mk_pat (P_lit (mk_lit L_one)));
              return (V_bit B0, mk_pat (P_lit (mk_lit L_zero)));
              oneofl [B0; B1] >>= fun bit -> return (V_bit bit, mk_pat P_wild)]
    | Typ_app (id, [A_aux (A_typ elem_typ, _)]) when string_of_id id = "list" ->
       let empty_list =
         oneofl [V_list [], mk_pat P_wild;
                 V_list [], mk_pat (P_list [])]
       in
       let list_pattern =
         int_range 1 6 >>= fun len ->
         list_repeat len (pattern_gen infer (n - 1) elem_typ) >>= fun gens ->
         return (V_list (List.map fst gens), mk_pat (P_list (List.map snd gens)))
       in
       let cons_pattern =
         pattern_gen infer (n - 1) elem_typ >>= fun gen1 ->
         pattern_gen infer (n - 1) typ >>= fun gen2 ->
         return (V_list (fst gen1 :: coerce_list (fst gen2)), mk_pat (P_cons (snd gen1, snd gen2)))
       in
       frequency [1, empty_list;
                  2, list_pattern;
                  4, cons_pattern]
    | Typ_id id when string_of_id id = "int" ->
       frequency
         [4, map (fun n -> V_int (Big_int.of_int n), mk_pat (P_lit (mk_lit (L_num (Big_int.of_int n))))) small_nat;
          1, map (fun n -> V_int (Big_int.of_int n), mk_pat P_wild) small_nat]
    | Typ_tup typs ->
       sequence (List.map (pattern_gen infer (n - 1)) typs) >>= fun gens ->
       if n = 0 then
         return (V_tuple (List.map fst gens), mk_pat P_wild)
       else
         return (V_tuple (List.map fst gens), mk_pat (P_tup (List.map snd gens)))
    | Typ_id id when string_of_id id = "unit" ->
       oneofl [V_unit, mk_pat (P_lit (mk_lit L_unit));
               V_unit, mk_pat P_wild]
    | Typ_id id when string_of_id id = "string" ->
       oneofl [V_string "", mk_pat P_wild;
               V_string "test", mk_pat (P_lit (mk_lit (L_string "test")))]
    | _ ->
       print_endline ("Cannot generate type " ^ string_of_typ typ);
       assert false
  in
  if infer then
    map (fun (value, pat) -> if not (is_literal pat) then value, mk_pat (P_typ (typ, pat)) else value, pat) gen
  else
    frequency
      [8, gen;
       1, map (fun (value, pat) -> value, mk_pat (P_typ (typ, pat))) gen]

let pattern_typ_gen = QCheck.Gen.(typ_gen >>= fun typ -> pattern_gen false 3 typ >>= fun pat -> return (pat, typ))

let test_pattern_gen env =
  QCheck.Test.make ~count:1000 ~name:"pattern_gen_type_checks"
    (QCheck.make pattern_typ_gen ~print:(fun ((value, pat), typ) -> Value.string_of_value value ^ " , " ^ string_of_pat pat ^ " : " ^ string_of_typ typ))
    Type_check.(fun ((_, pat), typ) -> try (let _, env, guards = bind_pat env pat typ in let _, _ = check_guards env guards in true) with Type_check.Type_error _ -> false)

    (*
let () =
  QCheck.Gen.generate ~n:30 pattern_typ_gen
  |> List.iter (fun ((value, pat), typ) -> prerr_endline (Value.string_of_value value ^ " , " ^ string_of_pat pat ^ ", " ^ string_of_typ typ))
     *)

let test_pattern_gen2 env =
  let open Type_check in
  let test ((value, pat), typ) =
    let pat, env, guards = bind_pat env pat typ in
    let guards, env = check_guards env guards in
    ()
  in
  ()

let run_pattern_rewrite_tests env = QCheck_runner.run_tests [test_pattern_gen env]

let rec irrefutable (P_aux (aux, annot)) =
  let open Type_check in
  match aux with
  | P_id id ->
     let open Type_check in
     let env = env_of_annot annot in
     begin match Env.lookup_id id env with
     | Enum (Typ_aux (Typ_id enum_id, _)) ->
        List.compare_length_with (Env.get_enum enum_id env) 1 = 0
     | _ -> true
     end
  | P_app (ctor, args) ->
     Env.is_singleton_union_constructor ctor (env_of_annot annot) && List.for_all irrefutable args
  | P_wild -> true
  | P_lit _ | P_string_append _ | P_cons _ -> false
  | P_as (pat, _) | P_typ (_, pat) | P_var (pat, _) | P_view (pat, _, _) -> irrefutable pat
  | P_vector pats | P_vector_concat pats | P_list pats | P_tup pats -> List.for_all irrefutable pats
  | P_or _ | P_not _ -> Reporting.unreachable (fst annot) __POS__ "Or or not pattern found in replace_views"

(* Check if one pattern subsumes the other, and if so, calculate a
   substitution of variables that are used in the same position.
   TODO: Check somewhere that there are no variable clashes (the same variable
   name used in different positions of the patterns)
 *)
let rec subsumes_pat (P_aux (p1,annot1) as pat1) (P_aux (p2,annot2) as pat2) =
  let open Type_check in
  let rewrap p = P_aux (p,annot1) in
  let subsumes_list s pats1 pats2 =
    if List.length pats1 = List.length pats2
    then
      let subs = List.map2 s pats1 pats2 in
      List.fold_right
        (fun p acc -> match p, acc with
          | Some subst, Some substs -> Some (subst @ substs)
          | _ -> None)
        subs (Some [])
    else None in
  match p1, p2 with
  | P_lit (L_aux (lit1,_)), P_lit (L_aux (lit2,_)) ->
      if lit1 = lit2 then Some [] else None
  | P_or (_, _), _ | _, P_or (_, _)  -> Reporting.unreachable (fst annot1) __POS__ "Or pattern found in subsumes_pat"
  | P_not _, _ | _, P_not _ -> Reporting.unreachable (fst annot1) __POS__ "Not pattern found in subsumes_pat"
  | P_as (pat1,_), _ -> subsumes_pat pat1 pat2
  | _, P_as (pat2,_) -> subsumes_pat pat1 pat2
  | P_typ (_,pat1), _ -> subsumes_pat pat1 pat2
  | _, P_typ (_,pat2) -> subsumes_pat pat1 pat2
  | P_id (Id_aux (id1,_) as aid1), P_id (Id_aux (id2,_) as aid2) ->
    if id1 = id2 then Some []
    else if Env.lookup_id aid1 (env_of_annot annot1) = Unbound
    then if Env.lookup_id aid2 (env_of_annot annot2) = Unbound
      then Some [(id2,id1)]
      else Some []
    else None
  | P_id id1, _ ->
    if Env.lookup_id id1 (env_of_annot annot1) = Unbound then Some [] else None
  | P_var (pat1,_), P_var (pat2,_) -> subsumes_pat pat1 pat2
  | P_wild, _ -> Some []
  | P_app (Id_aux (id1,l1),args1), P_app (Id_aux (id2,_),args2) ->
    if id1 = id2 then subsumes_list subsumes_pat args1 args2 else None
  | P_vector pats1, P_vector pats2
  | P_vector_concat pats1, P_vector_concat pats2
  | P_tup pats1, P_tup pats2
  | P_list pats1, P_list pats2 ->
    subsumes_list subsumes_pat pats1 pats2
  | P_list (pat1 :: pats1), P_cons _ ->
    subsumes_pat (rewrap (P_cons (pat1, rewrap (P_list pats1)))) pat2
  | P_cons _, P_list (pat2 :: pats2)->
    subsumes_pat pat1 (rewrap (P_cons (pat2, rewrap (P_list pats2))))
  | P_cons (pat1, pats1), P_cons (pat2, pats2) ->
    (match subsumes_pat pat1 pat2, subsumes_pat pats1 pats2 with
    | Some substs1, Some substs2 -> Some (substs1 @ substs2)
    | _ -> None)
  | _, P_wild -> if irrefutable pat1 then Some [] else None
  | _ -> None

let id_is_unbound id env =
  match Type_check.Env.lookup_id id env with
  | Unbound -> true
  | _ -> false

(* A simple check for pattern disjointness; used for optimisation in the
   guarded pattern rewrite step *)
let rec disjoint_pat env (P_aux (p1,annot1) as pat1) (P_aux (p2,annot2) as pat2) =
  match p1, p2 with
  | P_as (pat1, _), _ -> disjoint_pat env pat1 pat2
  | _, P_as (pat2, _) -> disjoint_pat env pat1 pat2
  | P_typ (_, pat1), _ -> disjoint_pat env pat1 pat2
  | _, P_typ (_, pat2) -> disjoint_pat env pat1 pat2
  | P_var (pat1, _), _ -> disjoint_pat env pat1 pat2
  | _, P_var (pat2, _) -> disjoint_pat env pat1 pat2
  | P_id id, _ when id_is_unbound id env -> false
  | _, P_id id when id_is_unbound id env -> false
  | P_id id1, P_id id2 -> Id.compare id1 id2 <> 0
  | P_app (id1, args1), P_app (id2, args2) ->
     Id.compare id1 id2 <> 0 || List.exists2 (disjoint_pat env) args1 args2
  | P_vector pats1, P_vector pats2
  | P_tup pats1, P_tup pats2
  | P_list pats1, P_list pats2 ->
     List.exists2 (disjoint_pat env) pats1 pats2
  | _ -> false

let equiv_pats pat1 pat2 =
  match subsumes_pat pat1 pat2, subsumes_pat pat2 pat1 with
  | Some _, Some _ -> true
  | _, _ -> false

let subst_id_pat pat (id1,id2) =
  let p_id (Id_aux (id,l)) = (if id = id1 then P_id (Id_aux (id2,l)) else P_id (Id_aux (id,l))) in
  fold_pat { id_algebra with p_id = p_id } pat

let subst_id_exp exp (id1,id2) =
  Ast_util.subst (Id_aux (id1, Parse_ast.Unknown))
    (E_aux (E_id (Id_aux (id2, Parse_ast.Unknown)), (Parse_ast.Unknown, Type_check.empty_tannot (Type_check.env_of exp))))
    exp

let subst_id_guards guards (id1,id2) =
  Ast_util.subst_guards (Id_aux (id1, Parse_ast.Unknown))
    (E_aux (E_id (Id_aux (id2, Parse_ast.Unknown)), (Parse_ast.Unknown, Type_check.empty_tannot Type_check.initial_env)))
    guards

let remove_wildcards pre (P_aux (_,(l,_)) as pat) =
  fold_pat
    { id_algebra with
      p_aux = function
              | (P_wild,(l,annot)) -> P_aux (P_id (mk_id "w__0") ,(l,annot))
              | (p,annot) -> P_aux (p,annot) }
    pat

(**************************************************************************)
(* 1. Pattern rewrites                                                    *)
(**************************************************************************)

type action =
  | Subst_id of (id -> unit guard list)
  | No_change

(** The Pattern_rewriter module implements a bottom up traversal of
   all patterns with the AST, applying actions at each pattern. *)
module Pattern_rewriter = struct
  open Type_check

  module type Config = sig
    val id_root : string
    val action : Ast.l -> Type_check.tannot pat -> action
  end

  module Make (C : Config) : sig
    val rewrite : tannot defs -> tannot defs
    val test_rewrite : Type_check.tannot defs -> Type_check.Env.t -> QCheck.Test.t
  end = struct

    let rec rewrite_pat n env (P_aux (aux, annot)) =
      let wrap gs (P_aux (_, annot) as pat) =
        match C.action (gen_loc (fst annot)) pat with
        | No_change -> pat, gs
        | Subst_id to_guards ->
           let typ = typ_of_annot annot in
           let replaced_id = mk_id (C.id_root ^ "__" ^ string_of_int !n) in
           incr n;
           let env = Env.add_local replaced_id (Immutable, typ) env in
           (* Make sure casts don't interfere with re-writing *)
           let gs', _ = check_guards (Env.no_casts env) (to_guards replaced_id) in
           P_aux (P_typ (typ, P_aux (P_id replaced_id, annot)), annot), gs' @ gs
      in
      match aux with
      | P_view (pat, id, args) ->
         let pat, guards = rewrite_pat n env pat in
         wrap guards (P_aux (P_view (pat, id, args), annot))
      | P_lit _ | P_wild | P_id _ ->
         wrap [] (P_aux (aux, annot))
      | P_as (pat, id) ->
         let pat, guards = rewrite_pat n env pat in
         wrap guards (P_aux (P_as (pat, id), annot))
      | P_typ (typ, pat) ->
         let pat, guards = rewrite_pat n env pat in
         wrap guards (P_aux (P_typ (typ, pat), annot))
      | P_app (id, pats) ->
         let rewritten = List.map (rewrite_pat n env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_app (id, List.map fst rewritten), annot))
      | P_vector pats ->
         let rewritten = List.map (rewrite_pat n env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_vector (List.map fst rewritten), annot))
      | P_vector_concat pats ->
         let rewritten = List.map (rewrite_pat n env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_vector_concat (List.map fst rewritten), annot))
      | P_tup pats ->
         let rewritten = List.map (rewrite_pat n env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_tup (List.map fst rewritten), annot))
      | P_list pats ->
         let rewritten = List.map (rewrite_pat n env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_list (List.map fst rewritten), annot))
      | P_cons (pat1, pat2) ->
         let pat1, guards1 = rewrite_pat n env pat1 in
         let pat2, guards2 = rewrite_pat n env pat2 in
         wrap (guards1 @ guards2) (P_aux (P_cons (pat1, pat2), annot))
      | P_string_append pats ->
         let rewritten = List.map (rewrite_pat n env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_string_append (List.map fst rewritten), annot))
      | P_var (pat, tpat) ->
         let pat, guards = rewrite_pat n env pat in
         wrap guards (P_aux (P_var (pat, tpat), annot))
      | P_or _ | P_not _ -> Reporting.unreachable (fst annot) __POS__ "Or and not patterns are currently not implemented"

    and rewrite_guard n env (G_aux (aux, l)) =
      match aux with
      | G_if exp -> G_aux (G_if exp, l), []
      | G_pattern (pat, exp) ->
         let pat, guards = rewrite_pat n env pat in
         G_aux (G_pattern (pat, exp), l), guards

    (* For pattern re-writes that introduce new guards, we need to
       check those guards using the environment that the first
       existing guard was originally checked using, or the expression
       if no guard exists *)
    let first_guard_environment guards exp =
      match guards with
      | [] -> env_of exp
      | G_aux (G_if exp, _) :: _ -> env_of exp
      | G_aux (G_pattern (pat, _), _) :: _ -> env_of_pat pat

    let rewrite_case (pat, guards, exp) =
      let n = ref 0 in
      let pat, guards' = rewrite_pat n (first_guard_environment guards exp) pat in
      let rewritten_guards = List.map (rewrite_guard n (env_of exp)) guards in
      Pat_case (pat, guards' @ List.map fst rewritten_guards @ List.concat (List.map snd rewritten_guards), exp)

    let rewrite_exp = fold_exp { id_algebra with pat_case = rewrite_case }

    let rewrite_funcl (FCL_aux (FCL_Funcl (f, Pat_aux (Pat_case (pat, guards, exp), p_l)), annot)) =
      FCL_aux (FCL_Funcl (f, Pat_aux (rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)

    let rewrite_fundef (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), annot)) =
      FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, List.map rewrite_funcl funcls), annot)

    let rewrite_mapcl (MCL_aux (aux, annot)) =
      match aux with
      | MCL_forwards (Pat_aux (Pat_case (pat, guards, exp), p_l)) ->
         MCL_aux (MCL_forwards (Pat_aux (rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)
      | MCL_backwards (Pat_aux (Pat_case (pat, guards, exp), p_l)) ->
         MCL_aux (MCL_backwards (Pat_aux (rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)
      | MCL_bidir _ ->
         Reporting.unreachable (fst annot) __POS__ "Bi-directional mapping clauses should have been removed before pattern rewriting"

    let rewrite_mapdef (MD_aux (MD_mapping (m, args, tannot_opt, mapcls), annot)) =
      MD_aux (MD_mapping (m, args, tannot_opt, List.map rewrite_mapcl mapcls), annot)

    let rewrite_def = function
      | DEF_fundef fdef -> DEF_fundef (rewrite_fundef fdef)
      | DEF_mapdef mdef -> DEF_mapdef (rewrite_mapdef mdef)
      | def -> def

    let rewrite (Defs defs) = Defs (List.map rewrite_def defs)

    (* Automatically derive a quickcheck test that uses the
       interpreter to test that random patterns have the same behavior
       before and after the re-write. *)
    let test_rewrite ast env =
      let open Type_check in
      let open Interpreter in
      let test ((value, pat), typ) =
        try
          let pat, env', guards = bind_pat env pat typ in
          let guards, env'' = check_guards env' guards in
          let wildcard, _, _ = bind_pat env (mk_pat P_wild) typ in
          let test =
            E_aux (E_case (exp_of_value value,
                           [construct_pexp (pat, guards, check_exp env'' (mk_lit_exp L_true) bool_typ, Parse_ast.Unknown);
                            construct_pexp (wildcard, [], check_exp env (mk_lit_exp L_false) bool_typ, Parse_ast.Unknown)]),
                   (Parse_ast.Unknown, mk_tannot env bool_typ no_effect))
          in
          let state = initial_state ~registers:true ast env Value.primops in
          let frame = Step (lazy (Pretty_print_sail.(to_string (doc_exp test))), state, return test, []) in
          match run_frame_result frame with
          | Ok (Value.V_bool true) ->
             let test = rewrite_exp test in
             let frame = Step (lazy (Pretty_print_sail.(to_string (doc_exp test))), state, return test, []) in
             begin match run_frame_result frame with
             | Ok (Value.V_bool true) -> true
             | _ -> false
             end
          | _ -> false
        with
          Type_check.Type_error (_, _, err) ->
          prerr_endline (Type_error.string_of_type_error err);
          false
      in
      QCheck.Test.make ~count:100 ~name:("Pattern rewrite test: " ^ C.id_root)
        (QCheck.make pattern_typ_gen ~print:(fun ((value, pat), typ) -> Value.string_of_value value ^ " , " ^ string_of_pat pat ^ " : " ^ string_of_typ typ))
        test

  end
end

(* Rewrite a view pattern of the form

   p <- f(x, y, z) => ...
   into
   id let p = f(x, y, z, id) => ...

   i.e. it turns view patterns into pattern guards. *)
module View_config = struct
  let id_root = "view"

  let action l = function
    | P_aux (P_view (pat, id, args), (l, _)) ->
       let args = List.map Type_check.strip_exp args in
       Subst_id (fun s ->
           [G_aux (G_pattern (Type_check.strip_pat pat, mk_exp ~loc:l (E_app (id, args @ [mk_exp ~loc:l (E_id s)]))), l)]
         )
    | _ -> No_change
end

module View_rewriter = Pattern_rewriter.Make(View_config)

(* Rewrite a bitvector pattern of the form

   p_1 @ ... @ p_n => ...
   into
   id let p_1 = id[hi_1 .. lo_1], ... , let p_n = id[hi_n .. lo_n] => ... *)
module Bitvector_concat_config = struct
  let id_root = "v"

  let action l = function
    | P_aux (P_vector_concat pats, annot) ->
       let open Type_check in
       let env = env_of_annot annot in
       let typ = typ_of_annot annot in
       let lengths = List.map (fun pat ->
                         match destruct_bitvector env (typ_of_pat pat) with
                         | Some (Nexp_aux (Nexp_constant n, _), _) -> n
                         | _ -> Reporting.unreachable l __POS__ "Non-constant width bitvector concat subpattern found in rewrite"
                       ) pats in
       let _, ranges = List.fold_left (fun (lo, ranges) len ->
                           if Big_int.equal len Big_int.zero then
                             (lo, None :: ranges)
                           else
                             let hi = Big_int.add lo len in (hi, Some (Big_int.pred hi, lo) :: ranges)
                         ) (Big_int.zero, []) (List.rev lengths) in
       let pats = List.map Type_check.strip_pat pats in
       Subst_id (fun s ->
           List.map2 (fun pat range ->
               match range with
               | Some (hi, lo) -> G_aux (G_pattern (pat, mk_exp ~loc:l (E_vector_subrange (mk_exp ~loc:l (E_id s), mk_lit_exp (L_num hi), mk_lit_exp (L_num lo)))), l)
               | None -> G_aux (G_pattern (pat, mk_exp ~loc:l (E_cast (bitvector_typ (nint 0) dec_ord, mk_exp ~loc:l (E_vector [])))), l)
             ) pats ranges
         )
    | _ -> No_change
end

module Bitvector_concat_rewriter = Pattern_rewriter.Make(Bitvector_concat_config)

module Literal_config = struct
  let id_root = "l"

  let action l = function
    | P_aux (P_lit (L_aux (L_unit, _)), annot) -> No_change
    | P_aux (P_lit (L_aux (lit, _)), annot) ->
       Subst_id (fun s ->
           [G_aux (G_if (locate (fun _ -> l) (mk_exp (E_app_infix (mk_exp (E_id s), mk_id "==", mk_lit_exp lit)))), l)]
         )
    | _ -> No_change
end

module Literal_rewriter = Pattern_rewriter.Make(Literal_config)

(* Rewrite a string append pattern of the form

   s_1 ^ ... ^ s_n => ...
   into
   id let (true, m) = __split(T, id), let s_1 = __group(m, 1), ... , let s_n = __group(m, 2) => ...

   where split(T) tokenizes the string append using the regex T derived from the subpattern types. *)
module String_append_config = struct
  let id_root = "s"

  let action l = function
    | P_aux (P_string_append pats, annot) ->
       let subpattern_regex pat =
         let open Type_check in
         match pat, typ_of_pat pat with
         | P_aux (P_lit (L_aux (L_string str, _)), _), _ ->
            None, Regex.Seq (List.map (fun c -> Regex.Char c) (Util.string_to_list str))
         | _, Typ_aux (Typ_regex regex, _) ->
            begin match Regex_util.parse_regex regex with
            | Some regex -> Some pat, Regex.Group regex
            | None -> Reporting.unreachable (fst annot) __POS__ ("Could not parse regular expression: " ^ regex)
            end
         | _, Typ_aux (Typ_id id, _) when string_of_id id = "string" ->
            Some pat, Regex.(Group (Repeat (Dot, At_least 0)))
         | _, _ ->
            Reporting.unreachable (fst annot) __POS__ ("Bad subpattern in string append pattern: " ^ string_of_pat pat)
       in
       let subpattern_regexes = List.map subpattern_regex pats in
       let tokenization = Regex_util.string_of_regex (Regex.Seq (List.map snd subpattern_regexes)) in
       Subst_id (fun s ->
           [G_aux (G_pattern (locate_pat (fun _ -> l) (mk_pat (P_tup [mk_lit_pat L_true; mk_pat (P_id (mk_id "m"))])),
                              locate (fun _ -> l) (mk_exp (E_app (mk_id "__split", [mk_lit_exp (L_string tokenization); mk_exp (E_id s)])))), l)]
           @ (List.fold_left (fun (group, guards) (subpattern, regex) ->
                  match subpattern with
                  | None -> (group, guards)
                  | Some pat ->
                     (group + 1,
                      G_aux (G_pattern (Type_check.strip_pat pat,
                                        locate (fun _ -> l) (mk_exp (E_app (mk_id "__group", [mk_lit_exp (L_num (Big_int.of_int group)); mk_exp (E_id (mk_id "m"))])))), l)
                      :: guards)
                ) (1, []) subpattern_regexes
              |> snd)
         )
    | _ -> No_change
end

module String_append_rewriter = Pattern_rewriter.Make(String_append_config)

let run_pattern_rewrite_tests ast env =
  QCheck_runner.run_tests [
      test_pattern_gen env;
      Bitvector_concat_rewriter.test_rewrite ast env
    ]

(**************************************************************************)
(* 2. Guard removal                                                       *)
(**************************************************************************)

let trivially_pure_functions =
  [ "vector_subrange" ]
  |> List.map mk_id
  |> IdSet.of_list

let rec trivially_pure (E_aux (aux, _)) =
  match aux with
  | E_id _ | E_lit _ -> true
  | E_app (f, args) ->
     IdSet.mem f trivially_pure_functions && List.for_all trivially_pure args
  | _ -> false

(* The idea behind this step is if we have a list of guards in a case
   expression

   g_0, ... , g_n => exp

   we want to push any irrefutable pattern guards into exp as
   letbindings. This is done by taking the list of guards with '<=' as
   a special element representing moving a guard from the right to the
   left, i.e. we start with

   <=, g_n, ... , g_0

   and then apply commutativity rules until we have something like

   g_n, g_{n-2}, <=, g_{n-1}, ... , g_0 which then becomes

   g_0 , ... , g_{n-1} => let X in exp

   where X are letbindings equivalent to the irrefutable pattern
   guards g_n and g_{n-2} on the left of '<='.

   The reason to do this is to reduce the amount of work that needs to
   be done by the generic guard removal step. *)

let swap_guards guards =
  let swap = function
    | None, Some (G_aux (G_pattern (pat, exp), l)) when irrefutable pat ->
       Some (Some (G_aux (G_pattern (pat, exp), l)), None)

    | Some (G_aux (G_if cond, l1)), Some (G_aux (G_pattern (pat, exp), l2)) when irrefutable pat && trivially_pure exp ->
       let P_aux (_, annot) = pat in
       let cond = E_aux (E_let (LB_aux (LB_val (pat, exp), annot), cond), annot) in
       Some (Some (G_aux (G_pattern (pat, exp), l2)), Some (G_aux (G_if cond, l1)))

    | _, _ -> None
  in

  let rec apply_swaps guards =
    let swaps = ref 0 in
    let rec swap_list = function
      | x :: y :: zs ->
         begin match swap (x, y) with
         | Some (y, x) ->
            incr swaps;
            y :: swap_list (x :: zs)
         | None -> x :: swap_list (y :: zs)
         end
      | [x] -> [x]
      | [] -> []
    in
    let lhs, rhs = Util.take_drop Util.is_some guards in
    let rhs = swap_list rhs in
    if !swaps > 0 then
      apply_swaps (lhs @ rhs)
    else
      lhs @ rhs
  in

  let guards = None :: List.rev_map (fun x -> Some x) guards in
  List.rev (Util.option_these (apply_swaps guards))

let rewrite_case (pat, guards, exp) =
  Pat_case (pat, swap_guards guards, exp)

let rewrite_exp = fold_exp { id_algebra with pat_case = rewrite_case }

let rewrite_funcl (FCL_aux (FCL_Funcl (f, Pat_aux (Pat_case (pat, guards, exp), p_l)), annot)) =
  FCL_aux (FCL_Funcl (f, Pat_aux (rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)

let rewrite_fundef (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), annot)) =
  FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, List.map rewrite_funcl funcls), annot)

let rewrite_mapcl (MCL_aux (aux, annot)) =
  match aux with
  | MCL_forwards (Pat_aux (Pat_case (pat, guards, exp), p_l)) ->
     MCL_aux (MCL_forwards (Pat_aux (rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)
  | MCL_backwards (Pat_aux (Pat_case (pat, guards, exp), p_l)) ->
     MCL_aux (MCL_backwards (Pat_aux (rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)
  | MCL_bidir _ ->
     Reporting.unreachable (fst annot) __POS__ "Bi-directional mapping clauses should have been removed before pattern rewriting"

let rewrite_mapdef (MD_aux (MD_mapping (m, args, tannot_opt, mapcls), annot)) =
  MD_aux (MD_mapping (m, args, tannot_opt, List.map rewrite_mapcl mapcls), annot)

let rewrite_def = function
  | DEF_fundef fdef -> DEF_fundef (rewrite_fundef fdef)
  | DEF_mapdef mdef -> DEF_mapdef (rewrite_mapdef mdef)
  | def -> def

let swap_guards (Defs defs) = Defs (List.map rewrite_def defs)

(*
let rec rewrite_case fallthrough (guards, exp) =
  match guards with
  | [] -> exp
  | G_aux (G_if cond, g_l) :: guards ->
     let (E_aux (_, (_, tannot)) as exp) = rewrite_case fallthrough (guards, exp) in
     E_aux (E_if (cond, exp, fallthrough), (gen_loc g_l, tannot))
  | G_aux (G_pattern (pat, exp'), g_l) :: guards ->
     let open Type_check in
     let (E_aux (_, (_, tannot)) as exp) = rewrite_case fallthrough (guards, exp) in
     let wildcard, _, _ = bind_pat (env_of_pat pat) (mk_pat P_wild) (typ_of_pat pat) in
     E_aux (E_case (exp', [Pat_aux (Pat_case (pat, [], exp), gen_loc g_l);
                           Pat_aux (Pat_case (wildcard, [], fallthrough), gen_loc g_l)]),
            (gen_loc g_l, tannot))
*)
