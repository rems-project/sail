(* ************************************************************************ *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2026                                                 *)
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
(*  This work was partially supported by EPSRC grant EP/K008528/1 REMS:     *)
(*  Rigorous Engineering for Mainstream Systems, an ARM iCASE award, EPSRC  *)
(*  IAA KTF funding, and donations from Arm. This project has received      *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union's Horizon 2020 research and innovation programme (grant agreement *)
(*  No 789108, ELVER).                                                      *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(* ************************************************************************ *)

From Ltac2 Require Import Ltac2.

Import Ltac2.Std.

Set Default Proof Mode "Classic".

Ltac2 ltac1_to_intro_pattern x := Option.get (Ltac1.to_intro_pattern x).
Ltac2 ltac1_to_list (f : Ltac1.t -> 'a) (t : Ltac1.t) : 'a list :=
  List.map f (Option.get (Ltac1.to_list t)).

(**
The [reintros] tactic is used to rename generated hypothesis names.
[reintros x y] will revert the last two hypotheses, then call
[intros x y] to reintroduce them with new names. If either [x] or
[y] already exist, then they will be renamed.
*)

Ltac2 rec revert_n (n : int) :=
  if Int.gt n 0 then
    lazy_match! goal with
    | [ h : _ |- _ ] =>
        revert $h; revert_n (Int.sub n 1)
    end
  else ().

Ltac2 reintros0 (ips : intro_pattern list) :=
  let hs := Control.hyps () in
  let names :=
    List.flat_map (fun ip =>
      match ip with
      | IntroNaming (IntroIdentifier n) => [n]
      | _ => []
      end
    ) ips
  in
  let frees := List.append (List.map (fun (n, _, _) => n) hs) names in
  (* Rename any hypotheses we are about to clobber. *)
  let _ :=
    List.fold_left (fun frees name =>
      List.fold_left (fun frees (hyp_name, _, _) =>
        if Ident.equal name hyp_name then
          let f := Fresh.fresh (Fresh.Free.of_ids frees) hyp_name in
          Std.rename [(hyp_name, f)];
          f :: frees
        else frees
      ) frees hs
    ) frees names
  in
  revert_n (List.length ips);
  Std.intros false ips.

Ltac2 Notation "reintros" names(list1(intropattern)) := Control.enter (fun () => reintros0 names).

Tactic Notation "reintros" simple_intropattern_list(names) :=
  let f := ltac2:(l |- reintros0 (ltac1_to_list ltac1_to_intro_pattern l)) in f names.

(**
The [destruct_match] tactic agressively performs case splitting on
the head expression of any match statements that appear in the goal.

This can cause the number of subgoals to explode, and creates a lot of
generated names - but when they can all be solved trivially it can
lead to much more succinct proofs than manually case splitting.
*)

Ltac2 rec destruct_match () :=
  let destruct_match' () :=
    match! goal with
    | [ |- context [ match ?v with _ => _ end ] ] =>
        let e := Fresh.in_goal (Option.get (Ident.of_string "C")) in
        destruct $v eqn : $e;
        destruct_match ()
    | [ |- _ ] => ()
    end
  in Control.enter destruct_match'.

Ltac destruct_match := ltac2:(destruct_match ()).

Ltac2 rec destruct_match_goal () :=
  let destruct_match' () :=
    match! goal with
    | [ |- context [ match ?v with _ => _ end ] ] =>
        let e := Fresh.in_goal (Option.get (Ident.of_string "C")) in
        destruct $v eqn : $e;
        revert $e;
        destruct_match_goal ()
    | [ |- _ ] => ()
    end
  in Control.enter destruct_match'.

Ltac destruct_match_goal := ltac2:(destruct_match_goal ()).
