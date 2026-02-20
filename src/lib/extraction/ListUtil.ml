
(** val take_drop : Big_int_Z.big_int -> 'a1 list -> 'a1 list * 'a1 list **)

let rec take_drop n xs =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> ([], xs))
    (fun m ->
    match xs with
    | [] -> ([], [])
    | x :: xs0 -> let (ys, zs) = take_drop m xs0 in ((x :: ys), zs))
    n
