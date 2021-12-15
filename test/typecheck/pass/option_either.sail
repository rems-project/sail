default Order inc

$sail_internal

union option('a: Type) = {None : unit, Some : 'a}

function none forall ('a : Type). () -> option('a) = None()

function some forall ('a : Type). x : 'a -> option('a) = Some(x)

function test forall ('a : Type). x : option('a) -> range(0, 1) = match x {
  None() => 0,
  Some(y) => 1
}

union either('a: Type, 'b: Type) = {Left : 'a, Right : 'b}

val signed : forall ('n : Int), 'n >= 0. vector('n, inc, bit) -> int

function test2 x : either(int, vector(1, inc, bit)) -> int = match x {
  Left(l) => l,
  Right(r) => signed(r)
}
