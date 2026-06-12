open BinNat
open BinPos
open Compare_dec
open PeanoNat
open Base

module Nat :
 sig
  val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision

  val le_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision
 end

module Pos :
 sig
  val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision

  val reverse_go : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val reverse : Big_int_Z.big_int -> Big_int_Z.big_int
 end

module N :
 sig
  val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision
 end
