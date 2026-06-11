
(** val le_lt_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let rec le_lt_dec = Big_int_Z.le_big_int

(** val le_gt_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let le_dec =
  le_gt_dec
