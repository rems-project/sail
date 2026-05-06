
module Coq_list =
 struct
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
