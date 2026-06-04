open Base

module Coq_list :
 sig
  val list_filter : ('a1 -> coq_Decision) -> 'a1 list -> 'a1 list

  val replicate : Big_int_Z.big_int -> 'a1 -> 'a1 list

  val foldl : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1
 end
