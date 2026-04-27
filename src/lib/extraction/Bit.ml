open BinNat
open BvUtil
open Datatypes
open ListDef
open Definitions

type bit =
| B0
| B1

(** val bit_to_bool : bit -> bool **)

let bit_to_bool = function
| B0 -> false
| B1 -> true

module Bits =
 struct
  (** val to_bvn : bit list -> bvn **)

  let to_bvn x =
    { bvn_n = (N.of_nat (length (map bit_to_bool x))); bvn_val =
      (BoolList.to_bv (map bit_to_bool x)) }
 end

module Three =
 struct
  type ubit =
  | B0
  | B1
  | BU

  (** val from_bool : bool -> ubit **)

  let from_bool = function
  | true -> B1
  | false -> B0

  (** val bit_not : ubit -> ubit **)

  let bit_not = function
  | B0 -> B1
  | B1 -> B0
  | BU -> BU

  (** val bit_or : ubit -> ubit -> ubit **)

  let bit_or lhs rhs =
    match lhs with
    | B0 -> rhs
    | B1 -> B1
    | BU -> (match rhs with
             | B0 -> BU
             | x -> x)

  (** val bit_and : ubit -> ubit -> ubit **)

  let bit_and lhs rhs =
    match lhs with
    | B0 -> B0
    | B1 -> rhs
    | BU -> (match rhs with
             | B0 -> B0
             | _ -> BU)

  (** val bit_xor : ubit -> ubit -> ubit **)

  let bit_xor lhs rhs =
    match lhs with
    | B0 -> rhs
    | B1 -> (match rhs with
             | B0 -> B1
             | B1 -> B0
             | BU -> BU)
    | BU -> BU

  (** val bit_add : ubit -> ubit -> ubit * ubit **)

  let bit_add lhs rhs =
    match lhs with
    | B0 -> (match rhs with
             | B0 -> (B0, B0)
             | x -> (x, B0))
    | B1 -> (match rhs with
             | B0 -> (B1, B0)
             | B1 -> (B0, B1)
             | BU -> (BU, BU))
    | BU -> (match rhs with
             | B0 -> (BU, B0)
             | _ -> (BU, BU))

  (** val bit_add_carry : ubit -> ubit -> ubit -> ubit * ubit **)

  let bit_add_carry lhs rhs carry =
    let p = (lhs, rhs) in
    let (u0, u1) = p in
    (match u0 with
     | B0 ->
       (match u1 with
        | B0 -> (match carry with
                 | B0 -> (B0, B0)
                 | x -> (x, B0))
        | B1 ->
          (match carry with
           | B0 -> (B1, B0)
           | B1 -> (B0, B1)
           | BU -> (BU, BU))
        | BU -> (match carry with
                 | B0 -> (BU, B0)
                 | _ -> (BU, BU)))
     | B1 ->
       (match u1 with
        | B0 ->
          (match carry with
           | B0 -> (B1, B0)
           | B1 -> (B0, B1)
           | BU -> (BU, BU))
        | B1 -> (match carry with
                 | B0 -> (B0, B1)
                 | x -> (x, x))
        | BU -> (BU, BU))
     | BU ->
       (match u1 with
        | B0 -> (match carry with
                 | B0 -> (BU, B0)
                 | _ -> (BU, BU))
        | _ -> (BU, BU)))

  (** val bitlist_add_carry_acc :
      ubit list -> ubit list -> ubit -> ubit list -> ubit list * ubit **)

  let rec bitlist_add_carry_acc xs ys c zs =
    match xs with
    | [] -> (zs, c)
    | x :: xs0 ->
      (match ys with
       | [] ->
         let (z, c0) = bit_add x c in
         bitlist_add_carry_acc xs0 ys c0 (z :: zs)
       | y :: ys0 ->
         let (z, c0) = bit_add_carry x y c in
         bitlist_add_carry_acc xs0 ys0 c0 (z :: zs))

  (** val bit_join : ubit -> ubit -> ubit **)

  let bit_join x y =
    match x with
    | B0 -> (match y with
             | B0 -> B0
             | _ -> BU)
    | B1 -> (match y with
             | B0 -> BU
             | x0 -> x0)
    | BU -> BU

  (** val bit_meet : ubit -> ubit -> ubit option **)

  let bit_meet x y =
    match x with
    | B0 -> (match y with
             | B1 -> None
             | _ -> Some B0)
    | B1 -> (match y with
             | B0 -> None
             | _ -> Some B1)
    | BU -> Some y

  (** val bit_leb : ubit -> ubit -> bool **)

  let bit_leb x y =
    match x with
    | B0 -> (match y with
             | B1 -> false
             | _ -> true)
    | B1 -> (match y with
             | B0 -> false
             | _ -> true)
    | BU -> (match y with
             | BU -> true
             | _ -> false)
 end
