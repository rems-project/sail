default Order dec

$include <prelude.sail>

enum my_enum = A | B | C

val f : forall ('e : Enum E), 'e in {A, B}. (my_enum('e)) -> unit

val h : {('e : Enum my_enum), 'e in {A, B}. my_enum('e)} -> unit

val return_ex : unit -> {('e : Enum my_enum), 'e == A. my_enum('e)}

function return_ex() = B

type D : Enum my_enum = A

val g : unit -> my_enum(D)

function g() = A

val main : unit -> unit

function main() = {
  match g() {
    x => f(x),
  };
  let 'y = g();
  _prove(constraint('y != C));
  _prove(constraint('y != B));
  _prove(constraint('y == A));
  _not_check(f(C) : unit);
  _check(f(A) : unit);
  h(A);
  f(return_ex());
  h(return_ex());
  let 'z = return_ex();
  _prove(constraint('z == A));
}
