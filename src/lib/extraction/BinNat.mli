open BinNums
open BinPos
open Datatypes
open PosDef

module N :
 sig
  val compare : coq_N -> coq_N -> comparison

  val add : coq_N -> coq_N -> coq_N

  val mul : coq_N -> coq_N -> coq_N
 end
