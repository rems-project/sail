
module Coq__1 : sig
 type bit =
 | B0
 | B1
end
include module type of struct include Coq__1 end

module Three :
 sig
  type ubit =
  | B0
  | B1
  | BU

  val from_bit : bit -> ubit

  val bit_join : ubit -> ubit -> ubit

  val bit_meet : ubit -> ubit -> ubit option

  val bit_leb : ubit -> ubit -> bool
 end
