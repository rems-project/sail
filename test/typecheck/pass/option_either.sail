default Order inc

union option ('a : Type) = {None : unit, Some : 'a}

function none () -> forall ('a : Type). option('a) = None()

function some x : 'a -> forall ('a : Type). option('a) = Some(x)

function test x : option('a) -> forall ('a : Type). range(0, 1) = match x {
  None() => 0,
  Some(y) => 1
}

union either ('a : Type) ('b : Type) = {Left : 'a, Right : 'b}

val signed : forall ('n : Int), 'n >= 0. vector('n, inc, bit) -> int

function test2 x : either(int, vector(1, inc, bit)) -> int = match x {
  Left(l) => l,
  Right(r) => signed(r)
}
