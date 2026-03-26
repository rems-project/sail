open QArith_base
open Qreduction

type coq_Qc = { this : coq_Q }

val coq_Q2Qc : coq_Q -> coq_Qc
