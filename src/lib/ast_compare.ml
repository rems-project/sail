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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
module Big_int = Nat_big_num

module Kid = struct
  type t = kid
  let compare (Kid_aux (Var v1, _)) (Kid_aux (Var v2, _)) = String.compare v1 v2
end

module Kind = struct
  type t = kind
  let compare (K_aux (aux1, _)) (K_aux (aux2, _)) =
    match (aux1, aux2) with
    | K_int, K_int -> 0
    | K_type, K_type -> 0
    | K_bool, K_bool -> 0
    | K_int, _ -> 1
    | _, K_int -> -1
    | K_type, _ -> 1
    | _, K_type -> -1
end

module KOpt = struct
  type t = kinded_id
  let compare (KOpt_aux (KOpt_kind (k1, kid1), _)) (KOpt_aux (KOpt_kind (k2, kid2), _)) =
    let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
    lex_ord (Kid.compare kid1 kid2) (Kind.compare k1 k2)
end

module Id = struct
  type t = id
  let compare id1 id2 =
    match (id1, id2) with
    | Id_aux (And_bool, _), Id_aux (And_bool, _) -> 0
    | Id_aux (Or_bool, _), Id_aux (Or_bool, _) -> 0
    | Id_aux (Id x, _), Id_aux (Id y, _) -> String.compare x y
    | Id_aux (Operator x, _), Id_aux (Operator y, _) -> String.compare x y
    | Id_aux (Id _, _), _ -> -1
    | _, Id_aux (Id _, _) -> 1
    | Id_aux (Operator _, _), _ -> -1
    | _, Id_aux (Operator _, _) -> 1
    | Id_aux (And_bool, _), _ -> -1
    | _, Id_aux (And_bool, _) -> 1
end

let lex_ord f g x1 x2 y1 y2 = match f x1 x2 with 0 -> g y1 y2 | n -> n

let rec nexp_compare (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
  let lex_ord (c1, c2) = if c1 = 0 then c2 else c1 in
  match (nexp1, nexp2) with
  | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2
  | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2
  | Nexp_constant c1, Nexp_constant c2 -> Big_int.compare c1 c2
  | Nexp_app (op1, args1), Nexp_app (op2, args2) ->
      let lex1 = Id.compare op1 op2 in
      let lex2 = List.length args1 - List.length args2 in
      let lex3 =
        if lex2 = 0 then List.fold_left2 (fun l n1 n2 -> lex_ord (l, nexp_compare n1 n2)) 0 args1 args2 else 0
      in
      lex_ord (lex1, lex_ord (lex2, lex3))
  | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b)
  | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b)
  | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) ->
      lex_ord (nexp_compare n1a n2a, nexp_compare n1b n2b)
  | Nexp_exp n1, Nexp_exp n2 -> nexp_compare n1 n2
  | Nexp_neg n1, Nexp_neg n2 -> nexp_compare n1 n2
  | Nexp_if (i1, t1, e1), Nexp_if (i2, t2, e2) ->
      let lex1 = nc_compare i1 i2 in
      let lex2 = nexp_compare t1 t2 in
      let lex3 = nexp_compare e1 e2 in
      lex_ord (lex1, lex_ord (lex2, lex3))
  | Nexp_constant _, _ -> -1
  | _, Nexp_constant _ -> 1
  | Nexp_id _, _ -> -1
  | _, Nexp_id _ -> 1
  | Nexp_var _, _ -> -1
  | _, Nexp_var _ -> 1
  | Nexp_neg _, _ -> -1
  | _, Nexp_neg _ -> 1
  | Nexp_exp _, _ -> -1
  | _, Nexp_exp _ -> 1
  | Nexp_minus _, _ -> -1
  | _, Nexp_minus _ -> 1
  | Nexp_sum _, _ -> -1
  | _, Nexp_sum _ -> 1
  | Nexp_times _, _ -> -1
  | _, Nexp_times _ -> 1
  | Nexp_if _, _ -> -1
  | _, Nexp_if _ -> 1

and nc_compare (NC_aux (nc1, _)) (NC_aux (nc2, _)) =
  match (nc1, nc2) with
  | NC_id id1, NC_id id2 -> Id.compare id1 id2
  | NC_equal (t1, t2), NC_equal (t3, t4) | NC_not_equal (t1, t2), NC_not_equal (t3, t4) ->
      lex_ord typ_arg_compare typ_arg_compare t1 t3 t2 t4
  | NC_ge (n1, n2), NC_ge (n3, n4)
  | NC_gt (n1, n2), NC_gt (n3, n4)
  | NC_le (n1, n2), NC_le (n3, n4)
  | NC_lt (n1, n2), NC_lt (n3, n4) ->
      lex_ord nexp_compare nexp_compare n1 n3 n2 n4
  | NC_set (n1, s1), NC_set (n2, s2) -> lex_ord nexp_compare (Util.compare_list Nat_big_num.compare) n1 n2 s1 s2
  | NC_or (nc1, nc2), NC_or (nc3, nc4) | NC_and (nc1, nc2), NC_and (nc3, nc4) ->
      lex_ord nc_compare nc_compare nc1 nc3 nc2 nc4
  | NC_app (f1, args1), NC_app (f2, args2) -> lex_ord Id.compare (Util.compare_list typ_arg_compare) f1 f2 args1 args2
  | NC_var v1, NC_var v2 -> Kid.compare v1 v2
  | NC_true, NC_true | NC_false, NC_false -> 0
  | NC_equal _, _ -> -1
  | _, NC_equal _ -> 1
  | NC_ge _, _ -> -1
  | _, NC_ge _ -> 1
  | NC_gt _, _ -> -1
  | _, NC_gt _ -> 1
  | NC_le _, _ -> -1
  | _, NC_le _ -> 1
  | NC_lt _, _ -> -1
  | _, NC_lt _ -> 1
  | NC_not_equal _, _ -> -1
  | _, NC_not_equal _ -> 1
  | NC_set _, _ -> -1
  | _, NC_set _ -> 1
  | NC_or _, _ -> -1
  | _, NC_or _ -> 1
  | NC_and _, _ -> -1
  | _, NC_and _ -> 1
  | NC_app _, _ -> -1
  | _, NC_app _ -> 1
  | NC_var _, _ -> -1
  | _, NC_var _ -> 1
  | NC_true, _ -> -1
  | _, NC_true -> 1
  | NC_id _, _ -> -1
  | _, NC_id _ -> 1

and typ_compare (Typ_aux (t1, _)) (Typ_aux (t2, _)) =
  match (t1, t2) with
  | Typ_internal_unknown, Typ_internal_unknown -> 0
  | Typ_id id1, Typ_id id2 -> Id.compare id1 id2
  | Typ_var kid1, Typ_var kid2 -> Kid.compare kid1 kid2
  | Typ_fn (ts1, t2), Typ_fn (ts3, t4) -> (
      match Util.compare_list typ_compare ts1 ts3 with 0 -> typ_compare t2 t4 | n -> n
    )
  | Typ_bidir (t1, t2), Typ_bidir (t3, t4) -> (
      match typ_compare t1 t3 with 0 -> typ_compare t2 t4 | n -> n
    )
  | Typ_tuple ts1, Typ_tuple ts2 -> Util.compare_list typ_compare ts1 ts2
  | Typ_exist (ks1, nc1, t1), Typ_exist (ks2, nc2, t2) -> (
      match Util.compare_list KOpt.compare ks1 ks2 with
      | 0 -> (
          match nc_compare nc1 nc2 with 0 -> typ_compare t1 t2 | n -> n
        )
      | n -> n
    )
  | Typ_app (id1, ts1), Typ_app (id2, ts2) -> (
      match Id.compare id1 id2 with 0 -> Util.compare_list typ_arg_compare ts1 ts2 | n -> n
    )
  | Typ_internal_unknown, _ -> -1
  | _, Typ_internal_unknown -> 1
  | Typ_id _, _ -> -1
  | _, Typ_id _ -> 1
  | Typ_var _, _ -> -1
  | _, Typ_var _ -> 1
  | Typ_fn _, _ -> -1
  | _, Typ_fn _ -> 1
  | Typ_bidir _, _ -> -1
  | _, Typ_bidir _ -> 1
  | Typ_tuple _, _ -> -1
  | _, Typ_tuple _ -> 1
  | Typ_exist _, _ -> -1
  | _, Typ_exist _ -> 1

and typ_arg_compare (A_aux (ta1, _)) (A_aux (ta2, _)) =
  match (ta1, ta2) with
  | A_nexp n1, A_nexp n2 -> nexp_compare n1 n2
  | A_typ t1, A_typ t2 -> typ_compare t1 t2
  | A_bool nc1, A_bool nc2 -> nc_compare nc1 nc2
  | A_nexp _, _ -> -1
  | _, A_nexp _ -> 1
  | A_typ _, _ -> -1
  | _, A_typ _ -> 1

let bit_compare b1 b2 =
  let open Bit in
  match (b1, b2) with B0, B0 -> 0 | B0, B1 -> -1 | B1, B0 -> 1 | B1, B1 -> 0

let lit_compare (L_aux (l1, _)) (L_aux (l2, _)) =
  match (l1, l2) with
  | L_unit, L_unit -> 0
  | L_unit, _ -> -1
  | _, L_unit -> 1
  | L_true, L_true -> 0
  | L_true, _ -> -1
  | _, L_true -> 1
  | L_false, L_false -> 0
  | L_false, _ -> -1
  | _, L_false -> 1
  | L_num n1, L_num n2 -> Big_int_Z.compare_big_int n1 n2
  | L_num _, _ -> -1
  | _, L_num _ -> 1
  | L_hex h1, L_hex h2 -> List.compare bit_compare (BitList.of_hex_lit h1) (BitList.of_hex_lit h2)
  | L_hex _, _ -> -1
  | _, L_hex _ -> 1
  | L_bin b1, L_bin b2 -> List.compare bit_compare (BitList.of_bin_lit b1) (BitList.of_bin_lit b2)
  | L_bin _, _ -> -1
  | _, L_bin _ -> 1
  | L_string s1, L_string s2 -> String.compare s1 s2
  | L_string _, _ -> -1
  | _, L_string _ -> 1
  | L_real r1, L_real r2 -> Q.compare (Util.Rational.from_rocq r1) (Util.Rational.from_rocq r2)

module Nexp = struct
  type t = nexp
  let compare = nexp_compare
end

module NC = struct
  type t = n_constraint
  let compare = nc_compare
end

module Typ = struct
  type t = typ
  let compare = typ_compare
end

module TypArg = struct
  type t = typ_arg
  let compare = typ_arg_compare
end

module Lit = struct
  type t = lit
  let compare = lit_compare
end

module Bindings = Map.Make (Id)
module IdSet = Set.Make (Id)
module KBindings = Map.Make (Kid)
module KidSet = Set.Make (Kid)
module KOptSet = Set.Make (KOpt)
module KOptMap = Map.Make (KOpt)
module NexpSet = Set.Make (Nexp)
module NexpMap = Map.Make (Nexp)
module TypMap = Map.Make (Typ)
module NCMap = Map.Make (NC)
module LitSet = Set.Make (Lit)
