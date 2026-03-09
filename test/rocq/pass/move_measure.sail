default Order dec
$include <prelude.sail>

union foo = {
  A : int,
  B : nat,
  C : bool,
}

function f(x : foo) -> int =
  match x {
    A(i) => i,
    B(n) => f(A(n)),
    C(b) => if b then 1 else 0,
  }

function f_measure(x : foo) -> int =
  match x {
    A(_) => 1,
    B(_) => 2,
    C(_) => 1,
  }

termination_measure f(x) = f_measure(x)
