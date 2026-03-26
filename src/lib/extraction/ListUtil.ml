
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

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb pred lhs rhs =
  match lhs with
  | [] -> (match rhs with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match rhs with
     | [] -> false
     | y :: ys -> (&&) (pred x y) (list_eqb pred xs ys))

(** val consume :
    ('a3 list -> 'a1 -> 'a2 option * 'a3 list) -> ('a2 list option * 'a3
    list) -> 'a1 -> 'a2 list option * 'a3 list **)

let consume f acc x =
  let (o, xs) = acc in
  (match o with
   | Some rs ->
     let (o0, xs0) = f xs x in
     (match o0 with
      | Some r -> ((Some (r :: rs)), xs0)
      | None -> (None, xs0))
   | None -> (None, xs))

(** val zip_with_opt :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list option **)

let rec zip_with_opt f xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> Some []
           | _ :: _ -> None)
  | x :: xs0 ->
    (match ys with
     | [] -> None
     | y :: ys0 ->
       (match zip_with_opt f xs0 ys0 with
        | Some zs -> Some ((f x y) :: zs)
        | None -> None))
