open Ast
open Datatypes
open FMapList
open OrdersAlt
open SailBase
open String0
open Base
open Countable

module Aux =
 struct
  type t = id_aux

  (** val unwrap : id -> t **)

  let unwrap = function
  | Id_aux (aux, _) -> aux

  (** val eqb : t -> t -> bool **)

  let eqb id1 id2 =
    match id1 with
    | And_bool -> (match id2 with
                   | And_bool -> true
                   | _ -> false)
    | Or_bool -> (match id2 with
                  | Or_bool -> true
                  | _ -> false)
    | Id s1 -> (match id2 with
                | Id s2 -> (=) s1 s2
                | _ -> false)
    | Operator s1 -> (match id2 with
                      | Operator s2 -> (=) s1 s2
                      | _ -> false)

  (** val id_aux_eqdecb : t coq_EqDecb **)

  let id_aux_eqdecb =
    { SailBase.eqb = eqb }

  (** val encode_id_aux : t -> Big_int_Z.big_int **)

  let encode_id_aux = function
  | And_bool -> Big_int_Z.unit_big_int
  | Or_bool -> Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int
  | Id s ->
    Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (extstring_encode s))
  | Operator s ->
    Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (extstring_encode s))

  (** val decode_id_aux : Big_int_Z.big_int -> t option **)

  let decode_id_aux p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun _ -> None)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 ->
        match extstring_decode p1 with
        | Some e -> let str = e in Some (Operator str)
        | None -> None)
        (fun p1 ->
        match extstring_decode p1 with
        | Some e -> let str = e in Some (Id str)
        | None -> None)
        (fun _ -> Some Or_bool)
        p0)
      (fun _ -> Some And_bool)
      p

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match x with
    | And_bool -> (match y with
                   | And_bool -> true
                   | _ -> false)
    | Or_bool -> (match y with
                  | Or_bool -> true
                  | _ -> false)
    | Id s ->
      (match y with
       | Id s0 -> if (=) s s0 then true else false
       | _ -> false)
    | Operator s ->
      (match y with
       | Operator s0 -> if (=) s s0 then true else false
       | _ -> false)

  (** val eq_eqdec : (t, t) coq_RelDecision **)

  let eq_eqdec =
    eq_dec

  (** val id_aux_countable : t coq_Countable **)

  let id_aux_countable =
    { encode = encode_id_aux; decode = decode_id_aux }
 end

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
