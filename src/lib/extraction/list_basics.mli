
module Coq_list :
 sig
  val replicate : Big_int_Z.big_int -> 'a1 -> 'a1 list

  val foldl : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1
 end
