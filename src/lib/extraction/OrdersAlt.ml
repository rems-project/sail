open Datatypes

module Backport_OT =
 functor (O:Orders.OrderedType) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> O.t OrderedType.coq_Compare **)

  let compare x y =
    let c = coq_CompSpec2Type x y (O.compare x y) in
    (match c with
     | CompEqT -> OrderedType.EQ
     | CompLtT -> OrderedType.LT
     | CompGtT -> OrderedType.GT)
 end
