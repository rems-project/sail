open Bool
open QArith_base
open Qcanon

(** val extstring_encode : string -> Big_int_Z.big_int **)

let extstring_encode = Extr_util.String_encoding.encode

(** val extstring_decode : Big_int_Z.big_int -> string option **)

let extstring_decode = Extr_util.String_encoding.decode

type 'a coq_EqDecb = { eqb : ('a -> 'a -> bool) }

(** val string_eqdecb : string coq_EqDecb **)

let string_eqdecb =
  { eqb = (=) }

(** val bool_eqdecb : bool coq_EqDecb **)

let bool_eqdecb =
  { eqb = Bool.eqb }

(** val coq_Qc_eqdecb : coq_Qc coq_EqDecb **)

let coq_Qc_eqdecb =
  { eqb = (fun x y -> coq_Qeq_bool x.this y.this) }
