open BinInt
open Datatypes

(** val coq_Z_le_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let coq_Z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true
