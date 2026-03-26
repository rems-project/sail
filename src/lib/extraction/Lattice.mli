
module type CONCRETE =
 sig
  type t
 end

module DomainProperties :
 functor (C:CONCRETE) ->
 functor (D:sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val _UU03b1_ : C.t -> t
 end) ->
 sig
 end
