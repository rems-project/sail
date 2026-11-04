default Order dec

$include <prelude.sail>

val foo : forall 'a. ('a, 'a) -> bool

val bar : forall 'a. 'a -> 'a

val main : unit -> unit

function main() = {
  let x = 3;
  let y = 4;
  let _ = foo(x, y);
  let _ = bar(x);
}
