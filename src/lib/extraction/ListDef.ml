
(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val repeat : 'a1 -> Big_int_Z.big_int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n
