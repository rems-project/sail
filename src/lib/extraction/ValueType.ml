open Ast
open BinInt
open Bit
open Datatypes
open ListDef
open PeanoNat

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
    | V_bitvector bitlist ->
      (match n with
       | V_int n0 ->
         let len = length bitlist in
         if Z.ltb n0 (Z.of_nat len)
         then None
         else let extend = Nat.sub (Z.to_nat n0) len in
              Some (V_bitvector (app (repeat B0 extend) bitlist))
       | _ -> None)
    | _ -> None
 end
