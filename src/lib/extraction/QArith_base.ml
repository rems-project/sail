open BinInt
open BinPos

type coq_Q = { coq_Qnum : Big_int_Z.big_int; coq_Qden : Big_int_Z.big_int }

(** val coq_Qeq_bool : coq_Q -> coq_Q -> bool **)

let coq_Qeq_bool x y =
  Z.eqb (Z.mul x.coq_Qnum y.coq_Qden) (Z.mul y.coq_Qnum x.coq_Qden)

(** val coq_Qplus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qplus x y =
  { coq_Qnum =
    (Z.add (Z.mul x.coq_Qnum y.coq_Qden) (Z.mul y.coq_Qnum x.coq_Qden));
    coq_Qden = (Pos.mul x.coq_Qden y.coq_Qden) }
