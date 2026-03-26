open BinNat
open BinPos
open Base
open Numbers
open Option

type 'a coq_Countable = { encode : ('a -> Big_int_Z.big_int);
                          decode : (Big_int_Z.big_int -> 'a option) }

val coq_N_countable : Big_int_Z.big_int coq_Countable

val nat_countable : Big_int_Z.big_int coq_Countable
