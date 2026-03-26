open Bool
open QArith_base
open Qcanon

val extstring_encode : string -> Big_int_Z.big_int

val extstring_decode : Big_int_Z.big_int -> string option

type 'a coq_EqDecb = { eqb : ('a -> 'a -> bool) }

val string_eqdecb : string coq_EqDecb

val bool_eqdecb : bool coq_EqDecb

val coq_Qc_eqdecb : coq_Qc coq_EqDecb
