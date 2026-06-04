open Base

(** val coq_True_dec : coq_Decision **)

let coq_True_dec =
  true

(** val coq_False_dec : coq_Decision **)

let coq_False_dec =
  false

(** val coq_Is_true_dec : bool -> coq_Decision **)

let coq_Is_true_dec = function
| true -> coq_True_dec
| false -> coq_False_dec

(** val unit_eq_dec : (unit, unit) coq_RelDecision **)

let unit_eq_dec _ _ =
  true

(** val uncurry_dec :
    ('a1 -> 'a2 -> coq_Decision) -> ('a1 * 'a2) -> coq_Decision **)

let uncurry_dec p_dec = function
| (x, y) -> p_dec x y

(** val bool_decide : coq_Decision -> bool **)

let bool_decide = function
| true -> true
| false -> false
