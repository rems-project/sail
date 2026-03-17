open Ast
open BinInt
open Bit
open BitList
open Bool
open Datatypes
open IdUtil
open ListDef
open ListUtil
open PeanoNat
open QArith_base

(** val value_of_lit : lit -> value **)

let value_of_lit = function
| L_aux (aux, _) ->
  (match aux with
   | L_unit -> V_unit
   | L_true -> V_bool true
   | L_false -> V_bool false
   | L_num n -> V_int n
   | L_hex h -> V_bitvector (of_hex_lit h)
   | L_bin b -> V_bitvector (of_bin_lit b)
   | L_string s -> V_string s
   | L_real r -> V_real r)

(** val value_eqb : value -> value -> bool **)

let rec value_eqb lhs rhs =
  match lhs with
  | V_bitvector l_bv ->
    (match rhs with
     | V_bitvector r_bv -> list_eqb bit_eqb l_bv r_bv
     | _ -> false)
  | V_vector l_v ->
    (match rhs with
     | V_vector r_v -> list_eqb value_eqb l_v r_v
     | _ -> false)
  | V_list l_xs ->
    (match rhs with
     | V_list r_ys -> list_eqb value_eqb l_xs r_ys
     | _ -> false)
  | V_int l -> (match rhs with
                | V_int r -> Z.eqb l r
                | _ -> false)
  | V_real l -> (match rhs with
                 | V_real r -> coq_Qeq_bool l r
                 | _ -> false)
  | V_bool l -> (match rhs with
                 | V_bool r -> eqb l r
                 | _ -> false)
  | V_tuple l_v ->
    (match rhs with
     | V_tuple r_v -> list_eqb value_eqb l_v r_v
     | _ -> false)
  | V_unit -> (match rhs with
               | V_unit -> true
               | _ -> false)
  | V_string l -> (match rhs with
                   | V_string r -> (=) l r
                   | _ -> false)
  | V_ref l -> (match rhs with
                | V_ref r -> id_eqb l r
                | _ -> false)
  | V_member l -> (match rhs with
                   | V_member r -> id_eqb l r
                   | _ -> false)
  | V_ctor (l_id, l_v) ->
    (match rhs with
     | V_ctor (r_id, r_v) ->
       (&&) (id_eqb l_id r_id) (list_eqb value_eqb l_v r_v)
     | _ -> false)
  | V_record l_fields ->
    (match rhs with
     | V_record r_fields ->
       list_eqb (fun pat pat0 ->
         let (l_id, l_v) = pat in
         let (r_id, r_v) = pat0 in (&&) (id_eqb l_id r_id) (value_eqb l_v r_v))
         l_fields r_fields
     | _ -> false)

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
