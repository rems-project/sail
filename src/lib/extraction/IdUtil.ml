open Ast
open FMapList
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

module IdMiniOrdered =
 struct
  type t = id

  (** val compare : id -> id -> id OrderedType.coq_Compare **)

  let compare x y =
    let Id_aux (i, _) = x in
    let Id_aux (i0, _) = y in
    (match i with
     | And_bool ->
       (match i0 with
        | And_bool -> OrderedType.EQ
        | _ -> OrderedType.GT)
     | Or_bool ->
       (match i0 with
        | And_bool -> OrderedType.LT
        | Or_bool -> OrderedType.EQ
        | _ -> OrderedType.GT)
     | Id s ->
       (match i0 with
        | Id s0 ->
          if ltb s s0
          then OrderedType.LT
          else if (=) s s0 then OrderedType.EQ else OrderedType.GT
        | _ -> OrderedType.LT)
     | Operator s ->
       (match i0 with
        | Id _ -> OrderedType.GT
        | Operator s0 ->
          if ltb s s0
          then OrderedType.LT
          else if (=) s s0 then OrderedType.EQ else OrderedType.GT
        | _ -> OrderedType.LT))
 end

module IdOrdered = OrderedType.MOT_to_OT(IdMiniOrdered)

module IdMap = Raw(IdOrdered)
