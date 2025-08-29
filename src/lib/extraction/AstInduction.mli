open Ast
open Datatypes
open List0
open ListDef

val lexp_subexps : 'a1 lexp -> 'a1 exp list

val take_drop : nat -> 'a1 list -> 'a1 list * 'a1 list

val update_lexp_subexps : 'a1 exp list -> 'a1 lexp -> 'a1 lexp * 'a1 exp list
