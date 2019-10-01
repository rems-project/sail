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


(**************************************************************************)
(* 1. Random pattern generation                                           *)
(**************************************************************************)

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

let run_pattern_rewrite_tests env = QCheck_runner.run_tests [test_pattern_gen env]

(**************************************************************************)
(* 2. Pattern rewrites                                                    *)
(**************************************************************************)

type action =
  | Subst_id of (id -> unit guard list)
  | No_change

module Case_rewriter = struct
  module type Config = sig
    val rewrite_case : Type_check.tannot pat * Type_check.tannot guard list * Type_check.tannot exp -> Type_check.tannot pexp_aux
  end

  module Make (C : Config) : sig
    val rewrite : Type_check.tannot defs -> Type_check.tannot defs
    val rewrite_exp : Type_check.tannot exp -> Type_check.tannot exp
  end = struct

    let rewrite_exp = fold_exp { id_algebra with pat_case = C.rewrite_case }

    let rewrite_funcl (FCL_aux (FCL_Funcl (f, Pat_aux (Pat_case (pat, guards, exp), p_l)), annot)) =
      FCL_aux (FCL_Funcl (f, Pat_aux (C.rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)

    let rewrite_fundef (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), annot)) =
      FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, List.map rewrite_funcl funcls), annot)

    let rewrite_mapcl (MCL_aux (aux, annot)) =
      match aux with
      | MCL_forwards (Pat_aux (Pat_case (pat, guards, exp), p_l)) ->
         MCL_aux (MCL_forwards (Pat_aux (C.rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)
      | MCL_backwards (Pat_aux (Pat_case (pat, guards, exp), p_l)) ->
         MCL_aux (MCL_backwards (Pat_aux (C.rewrite_case (pat, guards, rewrite_exp exp), p_l)), annot)
      | MCL_bidir _ ->
         Reporting.unreachable (fst annot) __POS__ "Bi-directional mapping clauses should have been removed before pattern rewriting"

    let rewrite_mapdef (MD_aux (MD_mapping (m, args, tannot_opt, mapcls), annot)) =
      MD_aux (MD_mapping (m, args, tannot_opt, List.map rewrite_mapcl mapcls), annot)

    let rewrite_def = function
      | DEF_fundef fdef -> DEF_fundef (rewrite_fundef fdef)
      | DEF_mapdef mdef -> DEF_mapdef (rewrite_mapdef mdef)
      | def -> def

    let rewrite (Defs defs) = Defs (List.map rewrite_def defs)

  end
end

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
           P_aux (P_id replaced_id, annot), gs' @ gs
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

    module Rewrite = struct
      let rewrite_case (pat, guards, exp) =
        let n = ref 0 in
        let pat, guards' = rewrite_pat n (first_guard_environment guards exp) pat in
        let rewritten_guards = List.map (rewrite_guard n (env_of exp)) guards in
        Pat_case (pat, guards' @ List.map fst rewritten_guards @ List.concat (List.map snd rewritten_guards), exp)
    end
    include Case_rewriter.Make(Rewrite)

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
       let pats = List.map strip_pat pats in
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

(* Rewrite P_vector patterns of the form

   [p_0, ..., p_n]
   into
   vec let p_1 = vec[0], ..., let p_n = vec[n] *)
module Vector_config = struct
  let id_root = "vec"

  let action l = function
    | P_aux (P_vector pats, annot) ->
       Subst_id (fun s ->
           List.mapi (fun n pat ->
               G_aux (G_pattern (Type_check.strip_pat pat,
                                 locate (fun _ -> l) (mk_exp (E_vector_access (mk_exp (E_id s),
                                                                               mk_lit_exp (L_num (Big_int.of_int n)))))),
                      l)
             ) pats
         )
    | _ -> No_change
end

module Vector_rewriter = Pattern_rewriter.Make(Vector_config)
                        
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
           [G_aux (G_pattern (locate_pat (fun _ -> l) (mk_pat (P_id (mk_id "m"))),
                              locate (fun _ -> l) (mk_exp (E_app (mk_id "__split", [mk_lit_exp (L_string tokenization);
                                                                                    mk_exp (E_id s);
                                                                                    mk_lit_exp (L_num (Big_int.of_int (List.length subpattern_regexes)))])))), l);
            G_aux (G_if (locate (fun _ -> l) (mk_exp (E_app (mk_id "__matched", [mk_exp (E_id (mk_id "m"))])))), l)]
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
(* 3. Guard removal                                                       *)
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

module Swap_guards_config = struct
  let rewrite_case (pat, guards, exp) = Pat_case (pat, swap_guards guards, exp)
end

module Swap_guards_rewriter = Case_rewriter.Make(Swap_guards_config)

type 'a split_cases =
  | Unguarded of 'a pat * 'a exp * Parse_ast.l * 'a split_cases
  | Guarded of 'a pat * 'a guard list * 'a exp * Parse_ast.l
  | Empty

let rec string_of_split_cases = function
  | Unguarded (pat, exp, l, cases) ->
     "Unguarded: " ^ string_of_pat pat ^ " => " ^ string_of_exp exp ^ "\n" ^ string_of_split_cases cases
  | Guarded (pat, guards, exp, l) ->
     "Guarded: " ^ string_of_pat pat ^ " " ^ Util.string_of_list ", " string_of_guard guards ^ " => " ^ string_of_exp exp
  | Empty ->
     "Empty"

let rec split_guarded_cases acc = function
  | (Pat_aux (Pat_case (pat, [], exp), l)) :: pexps ->
     split_guarded_cases (fun cases -> acc (Unguarded (pat, exp, l, cases))) pexps
  | Pat_aux (Pat_case (pat, guards, exp), l) :: pexps ->
     acc (Guarded (pat, guards, exp, l)) :: split_guarded_cases (fun cases -> cases) pexps
  | [] -> [acc Empty]

let rec rewrite_guards fallthrough annot body = function
  | G_aux (G_if cond, g_l) :: guards ->
     E_aux (E_if (cond, rewrite_guards fallthrough annot body guards, fallthrough), annot)
  | G_aux (G_pattern ((P_aux (_, pannot) as pat), (E_aux (_, eannot) as exp)), g_l) :: guards ->
     E_aux (E_case (exp,
                    [Pat_aux (Pat_case (pat, [], rewrite_guards fallthrough eannot body guards), gen_loc g_l);
                     Pat_aux (Pat_case (P_aux (P_wild, pannot), [], fallthrough), gen_loc g_l)]),
            annot)
  | [] -> body

let rec is_guarded_group = function
  | Unguarded (_, _, _, cases) -> is_guarded_group cases
  | Guarded _ -> true
  | Empty -> false

type 'a rewritten_match =
  | Into_match of 'a pexp list
  | Into_cascade of id * 'a fallthrough * 'a rewritten_match

let rewrite_match_exp (aux, annot) =
  let open Type_check in
  match aux with
  | E_case (exp, cases) ->
     let count = ref 0 in
     let groups = List.rev (split_guarded_cases (fun cases -> cases) cases) in

     let rec build_unguarded_pexps fallthrough annot = function
       | Unguarded (pat, exp, l, cases) ->
          Pat_aux (Pat_case (pat, [], exp), l) :: build_unguarded_pexps fallthrough annot cases
       | Guarded (pat, guards, exp, l) ->
          let exp = rewrite_guards fallthrough annot exp guards in
          [Pat_aux (Pat_case (pat, [], exp), l)]
       | Empty ->
          [Pat_aux (Pat_case (P_aux (P_wild, annot), [], fallthrough), Parse_ast.Unknown)]
     in

     let make_fallthrough previous_fallthrough annot group =
       let id = mk_id ("fallthrough__" ^ string_of_int !count) in
       incr count;
       id, Fallthrough (build_unguarded_pexps previous_fallthrough annot group)
     in

     let rec process_groups fallthrough annot = function
       | [] -> assert false
       | [group] ->
          Into_match (build_unguarded_pexps fallthrough annot group)
       | group :: groups ->
          let id, cases = make_fallthrough fallthrough annot group in
          Into_cascade (id, cases, process_groups (E_aux (E_id id, annot)) annot groups)
     in
     let exit_exp = E_aux (E_exit (E_aux (E_lit (mk_lit L_unit), annot)), annot) in
     begin match process_groups exit_exp annot groups with
     | Into_match cases -> E_aux (E_case (exp, cases), annot)
     | processed ->
        let rec to_cascade = function
          | Into_cascade (id, fallthrough, rest) ->
             let fallthroughs, cases = to_cascade rest in
             (id, fallthrough) :: fallthroughs, cases
          | Into_match cases ->
             [], cases
        in
        let fallthroughs, cases = to_cascade processed in
        let first_fallthrough =
          match List.rev fallthroughs with
          | (id, _) :: _ -> Pat_aux (Pat_case (P_aux (P_wild, annot), [], E_aux (E_id id, annot)), Parse_ast.Unknown)
          | [] -> Pat_aux (Pat_case (P_aux (P_wild, annot), [], exit_exp), Parse_ast.Unknown)
        in
        E_aux (E_internal_cascade (Cascade_match, exp, fallthroughs, cases @ [first_fallthrough]), annot)
     end

  | _ -> E_aux (aux, annot)

let rewrite_guarded_patterns defs =
  let rewrite_exp = fold_exp { id_algebra with e_aux = rewrite_match_exp } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> rewrite_exp) } defs

let rec rewrite_realize_mappings' env acc =
  let open Type_check in
  function
  | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), l), id, externs, is_cast), vs_annot)) :: defs
       when Env.is_mapping id env ->
     let swap left right = function
       | Forwards -> left, right
       | Backwards -> right, left
     in
     let set_typ_direction d =
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_fn (args, Typ_aux (Typ_bidir (left, right), _), effect), l) ->
          let left, right = swap left right d in
          Typ_aux (Typ_fn (args @ [left], right, effect), l)
       | Typ_aux (Typ_bidir (left, right), l) ->
          let left, right = swap left right d in
          Typ_aux (Typ_fn ([left], right, no_effect), l)
       | Typ_aux (_, l) as typ ->
          Reporting.unreachable l __POS__ ("Got invalid mapping type of " ^ string_of_typ typ ^ " when splitting mapping into separate functions")
     in
     let mk_valspec d =
       DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, set_typ_direction d), l), set_id_direction d id, externs, is_cast), vs_annot))
     in
     rewrite_realize_mappings' env (mk_valspec Forwards :: mk_valspec Backwards :: acc) defs

  | DEF_mapdef (MD_aux (MD_mapping (id, args, _, mapcls), md_annot)) :: defs ->
     let rec_opt = Rec_aux (Rec_nonrec, Parse_ast.Unknown) in
     let tannot_opt = Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown) in
     let effect_opt = Effect_opt_aux (Effect_opt_none, Parse_ast.Unknown) in
     let forwards, backwards = split_mapping_clauses mapcls in
     let clause_id = mk_id "clause#var" in
     let mk_case_exp pexps =
       E_aux (E_case (E_aux (E_id clause_id, md_annot),
                      pexps),
              md_annot) in
     let mk_funcl_pexp pexps =
       Pat_aux (Pat_case (P_aux (P_tup (args @ [P_aux (P_id clause_id, md_annot)]), md_annot),
                          [],
                          mk_case_exp pexps),
                Parse_ast.Unknown) in
     let mk_fundef d pexps =
       DEF_fundef (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, [FCL_aux (FCL_Funcl (set_id_direction d id, mk_funcl_pexp pexps), md_annot)]), md_annot))
     in
     rewrite_realize_mappings' env (mk_fundef Forwards forwards :: mk_fundef Backwards backwards :: acc) defs

  | def :: defs ->
     rewrite_realize_mappings' env (def :: acc) defs

  | [] -> List.rev acc

let rewrite_realize_mappings env (Defs defs) = Defs (rewrite_realize_mappings' env [] defs)
