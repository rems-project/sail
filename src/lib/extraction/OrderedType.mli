open OrdersTac

type 'x coq_Compare =
| LT
| EQ
| GT

module type MiniOrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare

  val eq_dec : t -> t -> bool
 end

module MOT_to_OT :
 functor (O:MiniOrderedType) ->
 sig
  type t = O.t

  val compare : t -> t -> t coq_Compare

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
 end
