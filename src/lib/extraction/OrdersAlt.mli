open Datatypes

module Backport_OT :
 functor (O:Orders.OrderedType) ->
 sig
  type t = O.t

  val eq_dec : t -> t -> bool

  val compare : O.t -> O.t -> O.t OrderedType.coq_Compare
 end
