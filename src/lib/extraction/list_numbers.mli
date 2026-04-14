open BinInt
open ListDef
open Base
open List_monad

module Coq_list :
 sig
  val seqZ : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list
 end
