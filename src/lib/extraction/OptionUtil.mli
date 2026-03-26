open List0

val is_none : 'a1 option -> bool

val is_some : 'a1 option -> bool

val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val option_map2 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option

val option_join :
  ('a1 -> 'a1 -> 'a1) -> 'a1 option -> 'a1 option -> 'a1 option

val option_bind2 :
  ('a1 -> 'a1 -> 'a1 option) -> 'a1 option -> 'a1 option -> 'a1 option

val option_all' : 'a1 list option -> 'a1 option list -> 'a1 list option

val option_all : 'a1 option list -> 'a1 list option

val option_is : ('a1 -> bool) -> 'a1 option -> bool
