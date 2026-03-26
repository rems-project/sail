
module Coq__1 = struct
 type bit =
 | B0
 | B1
end
include Coq__1

module Three =
 struct
  type ubit =
  | B0
  | B1
  | BU

  (** val from_bit : bit -> ubit **)

  let from_bit = function
  | Coq__1.B0 -> B0
  | Coq__1.B1 -> B1

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
