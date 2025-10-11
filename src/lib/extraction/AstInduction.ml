open Ast
open Datatypes
open List0
open ListDef

(** val lexp_subexps : 'a1 lexp -> 'a1 exp list **)

let rec lexp_subexps = function
| LE_aux (aux, _) ->
  (match aux with
   | LE_deref x -> x :: []
   | LE_app (_, xs) -> xs
   | LE_tuple ls -> concat (map lexp_subexps ls)
   | LE_vector_concat ls -> concat (map lexp_subexps ls)
   | LE_vector (l0, x) -> app (lexp_subexps l0) (x :: [])
   | LE_vector_range (l0, n, m) -> app (lexp_subexps l0) (n :: (m :: []))
   | LE_field (l0, _) -> lexp_subexps l0
   | _ -> [])

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

(** val update_lexp_subexps :
    'a1 exp list -> 'a1 lexp -> 'a1 lexp * 'a1 exp list **)

let rec update_lexp_subexps xs l = match l with
| LE_aux (aux, annot) ->
  (match aux with
   | LE_deref _ ->
     (match xs with
      | [] -> (l, xs)
      | y :: ys -> ((LE_aux ((LE_deref y), annot)), ys))
   | LE_app (id, args) ->
     let (ys, zs) = take_drop (length args) xs in
     ((LE_aux ((LE_app (id, ys)), annot)), zs)
   | LE_tuple ls ->
     let (ls0, xs0) =
       fold_left (fun acc l0 ->
         let (ls0, xs0) = acc in
         let (l1, xs1) = update_lexp_subexps xs0 l0 in
         ((app ls0 (l1 :: [])), xs1)) ls ([], xs)
     in
     ((LE_aux ((LE_tuple ls0), annot)), xs0)
   | LE_vector_concat ls ->
     let (ls0, xs0) =
       fold_left (fun acc l0 ->
         let (ls0, xs0) = acc in
         let (l1, xs1) = update_lexp_subexps xs0 l0 in
         ((app ls0 (l1 :: [])), xs1)) ls ([], xs)
     in
     ((LE_aux ((LE_vector_concat ls0), annot)), xs0)
   | LE_vector (l0, _) ->
     let (l1, l2) = update_lexp_subexps xs l0 in
     (match l2 with
      | [] -> (l0, [])
      | n :: xs0 -> ((LE_aux ((LE_vector (l1, n)), annot)), xs0))
   | LE_vector_range (l0, _, _) ->
     let (l1, l2) = update_lexp_subexps xs l0 in
     (match l2 with
      | [] -> (l0, [])
      | n :: l3 ->
        (match l3 with
         | [] -> (l0, [])
         | m :: xs0 -> ((LE_aux ((LE_vector_range (l1, n, m)), annot)), xs0)))
   | LE_field (l0, f) ->
     let (l', ys) = update_lexp_subexps xs l0 in
     ((LE_aux ((LE_field (l', f)), annot)), ys)
   | _ -> (l, xs))
