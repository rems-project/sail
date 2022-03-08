default Order dec

$include <prelude.sail>

val czeros = pure "zeros" : forall (constant 'n : Int), 'n >= 0. int('n) -> bits('n)

val multi_param : forall (constant 'n 'm : Int) ('o : Int). (int('n), int('m), int('o)) -> unit

function test forall 'n, 'n >= 0. (n: int('n)) -> unit = {
  let _ = czeros(64);
  multi_param(2 + 3, 5, n);
  ()
}