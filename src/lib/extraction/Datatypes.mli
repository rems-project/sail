
val negb : bool -> bool

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big_int_Z.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

val coq_CompareSpec2Type : comparison -> coq_CompareSpecT

type 'a coq_CompSpecT = coq_CompareSpecT

val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT
