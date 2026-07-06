open Datatypes

val tl : 'a1 list -> 'a1 list

val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option

val rev : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list
