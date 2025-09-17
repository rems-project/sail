open BinInt

type bit =
| B0
| B1

type value =
| V_vector of value list
| V_list of value list
| V_int of Big_int_Z.big_int
| V_real of Rational.t
| V_bool of bool
| V_bit of bit
| V_tuple of value list
| V_unit
| V_string of string
| V_ref of string
| V_member of string
| V_ctor of string * value list
| V_record of (string * value) list
| V_attempted_read of string

module Primops =
 struct
  (** val gt_int : value -> value -> value option **)

  let gt_int v1 v2 =
    match v1 with
    | V_int v3 ->
      (match v2 with
       | V_int v4 -> Some (V_bool (Z.gtb v3 v4))
       | _ -> None)
    | _ -> None

  (** val lt_int : value -> value -> value option **)

  let lt_int v1 v2 =
    match v1 with
    | V_int v3 ->
      (match v2 with
       | V_int v4 -> Some (V_bool (Z.ltb v3 v4))
       | _ -> None)
    | _ -> None

  (** val add_int : value -> value -> value option **)

  let add_int v1 v2 =
    match v1 with
    | V_int v3 ->
      (match v2 with
       | V_int v4 -> Some (V_int (Z.add v3 v4))
       | _ -> None)
    | _ -> None

  (** val sub_int : value -> value -> value option **)

  let sub_int v1 v2 =
    match v1 with
    | V_int v3 ->
      (match v2 with
       | V_int v4 -> Some (V_int (Z.sub v3 v4))
       | _ -> None)
    | _ -> None
 end
