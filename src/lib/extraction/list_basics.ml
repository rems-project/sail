
module Coq_list =
 struct
  (** val foldl : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

  let rec foldl f a = function
  | [] -> a
  | x :: l0 -> foldl f (f a x) l0
 end
