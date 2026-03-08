open Ast
open Datatypes
open FMapList
open OrdersAlt
open String0

(** val id_eqb : id -> id -> bool **)

let id_eqb id1 id2 =
  let Id_aux (i1, _) = id1 in
  (match i1 with
   | And_bool ->
     let Id_aux (i2, _) = id2 in (match i2 with
                                  | And_bool -> true
                                  | _ -> false)
   | Or_bool ->
     let Id_aux (i2, _) = id2 in (match i2 with
                                  | Or_bool -> true
                                  | _ -> false)
   | Id s1 ->
     let Id_aux (i2, _) = id2 in
     (match i2 with
      | Id s2 -> (=) s1 s2
      | _ -> false)
   | Operator s1 ->
     let Id_aux (i2, _) = id2 in
     (match i2 with
      | Operator s2 -> (=) s1 s2
      | _ -> false))

(** val id_ltb : id -> id -> bool **)

let id_ltb id1 id2 =
  let Id_aux (i1, _) = id1 in
  (match i1 with
   | And_bool -> false
   | Or_bool ->
     let Id_aux (i2, _) = id2 in (match i2 with
                                  | And_bool -> true
                                  | _ -> false)
   | Id s1 ->
     let Id_aux (i2, _) = id2 in
     (match i2 with
      | Id s2 -> ltb s1 s2
      | _ -> true)
   | Operator s1 ->
     let Id_aux (i2, _) = id2 in
     (match i2 with
      | Id _ -> false
      | Operator s2 -> ltb s1 s2
      | _ -> true))

module IdOrdered =
 struct
  type t = id

  (** val compare : id -> id -> comparison **)

  let compare x y =
    if id_eqb x y then Eq else if id_ltb x y then Lt else Gt

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let Id_aux (i, _) = x in
    let Id_aux (i0, _) = y in
    (match i with
     | And_bool -> (match i0 with
                    | And_bool -> true
                    | _ -> false)
     | Or_bool -> (match i0 with
                   | Or_bool -> true
                   | _ -> false)
     | Id s ->
       (match i0 with
        | Id s0 -> if (=) s s0 then true else false
        | _ -> false)
     | Operator s ->
       (match i0 with
        | Operator s0 -> if (=) s s0 then true else false
        | _ -> false))
 end

module IdOrderOrig = Backport_OT(IdOrdered)

module IdMap = Make(IdOrderOrig)
