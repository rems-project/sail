
type __ = Obj.t

module Coq_list =
 struct
  (** val list_fmap : (__ -> __) -> __ list -> __ list **)

  let rec list_fmap f = function
  | [] -> []
  | x :: l0 -> (f x) :: (list_fmap f l0)
 end
