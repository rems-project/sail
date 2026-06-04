open Base

val coq_True_dec : coq_Decision

val coq_False_dec : coq_Decision

val coq_Is_true_dec : bool -> coq_Decision

val unit_eq_dec : (unit, unit) coq_RelDecision

val uncurry_dec : ('a1 -> 'a2 -> coq_Decision) -> ('a1 * 'a2) -> coq_Decision

val bool_decide : coq_Decision -> bool
