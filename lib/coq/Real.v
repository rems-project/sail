(*==========================================================================*)
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
(*==========================================================================*)

Require Export Rbase.
Require Import Reals.
Require Export ROrderedType.
Require Import Sail.Values.
Require Import Lia.
Local Open Scope Z.

(* "Decidable" in a classical sense... *)
#[export] Instance Decidable_eq_real : forall (x y : R), Decidable (x = y) :=
  Decidable_eq_from_dec Req_dec.

Definition realFromFrac (num denom : Z) : R := Rdiv (IZR num) (IZR denom).

Definition neg_real := Ropp.
Definition mult_real := Rmult.
Definition sub_real := Rminus.
Definition add_real := Rplus.
Definition div_real := Rdiv.
Definition sqrt_real := sqrt.
Definition abs_real := Rabs.

(* Use flocq definitions, but without making the whole library a dependency. *)
Definition round_down (x : R) := (up x - 1)%Z.
Definition round_up (x : R) := (- round_down (- x))%Z.

Definition to_real := IZR.

Definition eq_real := Reqb.
Definition gteq_real (x y : R) : bool := if Rge_dec x y then true else false.
Definition lteq_real (x y : R) : bool := if Rle_dec x y then true else false.
Definition gt_real (x y : R) : bool := if Rgt_dec x y then true else false.
Definition lt_real (x y : R) : bool := if Rlt_dec x y then true else false.

(* Export select definitions from outside of Rbase *)
Definition pow_real := powerRZ.
Definition real_power := powerRZ.

Definition print_real (_ : string) (_ : R) : unit := tt.
Definition prerr_real (_ : string) (_ : R) : unit := tt.




Lemma IZRdiv m n :
  0 < m -> 0 < n ->
  (IZR (m / n) <= IZR m / IZR n)%R.
intros.
apply Rmult_le_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
rewrite <- mult_IZR.
apply IZR_le.
apply Z.mul_div_le.
assumption.
discrR.
lia.
Qed.

(* One annoying use of reals in the ARM spec I've been looking at. *)
Lemma round_up_div m n :
  0 < m -> 0 < n ->
  round_up (div_real (to_real m) (to_real n)) = (m + n - 1) / n.
intros.
unfold round_up, round_down, div_real, to_real.
apply Z.eq_opp_l.
apply Z.sub_move_r.
symmetry.
apply up_tech.

rewrite Ropp_Ropp_IZR.
apply Ropp_le_contravar.
apply Rmult_le_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
rewrite <- mult_IZR.
apply IZR_le.
assert (diveq : n*((m+n-1)/n) = (m+n-1) - (m+n-1) mod n).
apply Zplus_minus_eq.
rewrite (Z.add_comm ((m+n-1) mod n)).
apply Z.div_mod.
lia.
rewrite diveq.
assert (modmax : (m+n-1) mod n < n).
specialize (Z.mod_pos_bound (m+n-1) n). intuition.
lia.

discrR; lia.

rewrite <- Z.opp_sub_distr.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rmult_lt_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
2: { discrR. lia. }
rewrite <- mult_IZR.
apply IZR_lt.
rewrite Z.mul_sub_distr_l.
apply Z.le_lt_trans with (m := m+n-1-n*1).
apply Z.sub_le_mono_r.
apply Z.mul_div_le.
assumption.
lia.
Qed.
