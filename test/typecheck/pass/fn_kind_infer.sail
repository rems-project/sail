default Order dec

$include <prelude.sail>

val f : forall 'b. bool('b) -> unit

val g : forall 'a. 'a -> 'a

val h : forall 'n 'a. vector('n, 'a) -> unit
