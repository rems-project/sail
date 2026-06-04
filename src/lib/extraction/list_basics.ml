open Base

module Coq_list =
 struct
  (** val list_filter : ('a1 -> coq_Decision) -> 'a1 list -> 'a1 list **)

  let rec list_filter x = function
  | [] -> []
  | x0 :: l0 ->
    if decide (x x0)
    then x0 :: (filter (fun _ -> list_filter) x l0)
    else filter (fun _ -> list_filter) x l0

  (** val replicate : Big_int_Z.big_int -> 'a1 -> 'a1 list **)

  let rec replicate n x =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> [])
      (fun n0 -> x :: (replicate n0 x))
      n

  (** val foldl : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

  let rec foldl f a = function
  | [] -> a
  | x :: l0 -> foldl f (f a x) l0
 end
