open Ast
open BinInt
open BitList
open PrimBits

(** val value_of_lit : lit -> value **)

let value_of_lit = function
| L_aux (aux, _) ->
  (match aux with
   | L_unit -> V_unit
   | L_true -> V_bool true
   | L_false -> V_bool false
   | L_num n -> V_int n
   | L_hex h -> V_bitvector (of_bit_list (of_hex_lit h))
   | L_bin b -> V_bitvector (of_bit_list (of_bin_lit b))
   | L_string s -> V_string s
   | L_real r -> V_real r)

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

  (** val zero_extend : value -> value -> value option **)

  let zero_extend bits n =
    match bits with
    | V_bitvector bv ->
      (match n with
       | V_int n0 ->
         if Z.ltb n0 (width bv)
         then None
         else Some (V_bitvector (zero_extend bv n0))
       | _ -> None)
    | _ -> None
 end
