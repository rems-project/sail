
val take_drop : Big_int_Z.big_int -> 'a1 list -> 'a1 list * 'a1 list

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val consume :
  ('a3 list -> 'a1 -> 'a2 option * 'a3 list) -> ('a2 list option * 'a3 list)
  -> 'a1 -> 'a2 list option * 'a3 list
