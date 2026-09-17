open BinInt
open BinPos

type coq_Q = { coq_Qnum : Big_int_Z.big_int; coq_Qden : Big_int_Z.big_int }

val coq_Qeq_bool : coq_Q -> coq_Q -> bool

val coq_Qplus : coq_Q -> coq_Q -> coq_Q
