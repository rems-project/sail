open BinNat
open BinPos
open Compare_dec
open PeanoNat
open Base

module Nat =
 struct
  (** val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision **)

  let eq_dec =
    Nat.eq_dec

  (** val le_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision **)

  let le_dec =
    le_dec
 end

module Pos =
 struct
  (** val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision **)

  let eq_dec =
    Pos.eq_dec

  (** val reverse_go :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec reverse_go p1 p2 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p3 ->
      reverse_go
        ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        p1) p3)
      (fun p3 -> reverse_go (Big_int_Z.mult_int_big_int 2 p1) p3)
      (fun _ -> p1)
      p2

  (** val reverse : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let reverse =
    reverse_go Big_int_Z.unit_big_int
 end

module N =
 struct
  (** val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) coq_RelDecision **)

  let eq_dec =
    N.eq_dec
 end
