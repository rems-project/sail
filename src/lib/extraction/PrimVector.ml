open BinInt
open Datatypes
open List0
open ListDef

(** val take : Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec take n = function
| [] -> []
| x :: xs0 ->
  if Z.leb n Big_int_Z.zero_big_int
  then []
  else x :: (take (Z.sub n Big_int_Z.unit_big_int) xs0)

(** val drop : Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec drop n = function
| [] -> []
| x :: xs' ->
  if Z.leb n Big_int_Z.zero_big_int
  then x :: xs'
  else drop (Z.sub n Big_int_Z.unit_big_int) xs'

(** val append : 'a1 list -> 'a1 list -> 'a1 list **)

let append =
  app

(** val length : 'a1 list -> Big_int_Z.big_int **)

let rec length = function
| [] -> Big_int_Z.zero_big_int
| _ :: xs0 -> Z.succ (length xs0)

(** val vector_init : Big_int_Z.big_int -> 'a1 -> 'a1 list **)

let vector_init n elem =
  repeat elem (Z.to_nat n)

(** val subrange :
    'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list **)

let subrange xs n m =
  rev (take (Z.sub n (Z.sub m Big_int_Z.unit_big_int)) (drop m (rev xs)))

(** val subrange_inc :
    'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list **)

let subrange_inc xs n m =
  take (Z.sub m (Z.sub n Big_int_Z.unit_big_int)) (drop n xs)

(** val slice :
    'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list **)

let slice xs n m =
  rev (take m (drop n (rev xs)))

(** val slice_inc :
    'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list **)

let slice_inc xs n m =
  take m (drop n xs)

(** val vector_truncate : 'a1 list -> Big_int_Z.big_int -> 'a1 list **)

let vector_truncate xs n =
  rev (take n (rev xs))

(** val vector_truncateLSB : 'a1 list -> Big_int_Z.big_int -> 'a1 list **)

let vector_truncateLSB xs n =
  take n xs

(** val update_list : 'a1 list -> Big_int_Z.big_int -> 'a1 -> 'a1 list **)

let update_list xs n x =
  let i = Z.sub (Z.sub (length xs) n) Big_int_Z.unit_big_int in
  app (take i xs) (app (x :: []) (drop (Z.add i Big_int_Z.unit_big_int) xs))

(** val update_list_inc : 'a1 list -> Big_int_Z.big_int -> 'a1 -> 'a1 list **)

let update_list_inc xs n x =
  app (take n xs) (app (x :: []) (drop (Z.add n Big_int_Z.unit_big_int) xs))

(** val update : 'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let update xs n x =
  let i = Z.sub (Z.sub (length xs) n) Big_int_Z.unit_big_int in
  app (take i xs) (app x (drop (Z.add i Big_int_Z.unit_big_int) xs))

(** val update_inc : 'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let update_inc xs n x =
  app (take n xs) (app x (drop (Z.add n Big_int_Z.unit_big_int) xs))

(** val update_subrange :
    'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec update_subrange xs o = function
| [] -> xs
| y :: ys0 ->
  update_subrange (update_list xs o y) (Z.sub o Big_int_Z.unit_big_int) ys0

(** val update_subrange_inc :
    'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec update_subrange_inc xs o = function
| [] -> xs
| y :: ys0 ->
  update_subrange_inc (update_list_inc xs o y)
    (Z.add o Big_int_Z.unit_big_int) ys0

(** val replicate_bits : 'a1 list -> Big_int_Z.big_int -> 'a1 list **)

let replicate_bits xs n =
  concat (repeat xs (Z.to_nat n))

(** val reverse_endianness_fuel :
    Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec reverse_endianness_fuel fuel xs =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> xs)
    (fun fuel0 ->
    if Z.leb (length xs) (Big_int_Z.mult_int_big_int 2
         (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
         Big_int_Z.unit_big_int)))
    then xs
    else app
           (reverse_endianness_fuel fuel0
             (drop (Big_int_Z.mult_int_big_int 2
               (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
               Big_int_Z.unit_big_int))) xs))
           (take (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
             (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) xs))
    fuel

(** val reverse_endianness : 'a1 list -> 'a1 list **)

let reverse_endianness xs =
  reverse_endianness_fuel (Datatypes.length xs) xs

(** val arith_shiftr : 'a1 list -> Big_int_Z.big_int -> 'a1 list **)

let arith_shiftr xs y =
  take (length xs)
    (app (replicate_bits (take Big_int_Z.unit_big_int xs) y) xs)

(** val access_inc : 'a1 list -> Big_int_Z.big_int -> 'a1 list **)

let access_inc xs n =
  if Z.ltb n Big_int_Z.zero_big_int
  then []
  else (match nth_error xs (Z.to_nat n) with
        | Some x -> x :: []
        | None -> [])

(** val access : 'a1 list -> Big_int_Z.big_int -> 'a1 list **)

let access xs n =
  access_inc (rev xs) n
