open BinInt
open Datatypes
open QArith_base

(** val coq_Qred : coq_Q -> coq_Q **)

let coq_Qred q =
  let { coq_Qnum = q1; coq_Qden = q2 } = q in
  let (r1, r2) = snd (Z.ggcd q1 q2) in
  { coq_Qnum = r1; coq_Qden = (Z.to_pos r2) }
