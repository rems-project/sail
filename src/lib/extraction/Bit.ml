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
