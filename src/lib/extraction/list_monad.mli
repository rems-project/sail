
type __ = Obj.t

module Coq_list :
 sig
  val list_fmap : (__ -> __) -> __ list -> __ list
 end
