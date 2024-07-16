default Order dec

$include <prelude.sail>

enum E = A | B

val f : {A} -> unit

register R : bool

val main : unit -> unit

function main() = {
  let b = R;
  let x = if b then A else B;

  match x {
    A => (),
    B => (),
  };

  _not_check(f(x) : unit);
  if b then {
    f(x)
  }
}
