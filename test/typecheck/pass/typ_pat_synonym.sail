default Order dec

$include <prelude.sail>

type foo('n : Int) = vector('n, int)

type bytes('n : Int), 'n >= 0 = vector(8 * 'n, int)

type sw('n : Int, 'm : Int), 'n >= 0 & 'm >= 0 = (bits('n), bits('m))

type pair('a : Type) = ('a, int)

type flag('b : Bool) = (bool('b), int)

function f1(x : bits(4)) -> unit = match x {
  y as bits('n) => { let _ : int('n) = 4; () }
}

function f2(x : foo(4)) -> unit = match x {
  y as foo('n) => { let _ : int('n) = 4; () }
}

function f3(x : vector(32, int)) -> unit = match x {
  y as bytes('n) => { let _ : int('n) = 4; () }
}

function f4(x : (bits(1), bits(2))) -> unit = match x {
  y as sw('m, 'n) => { let _ : int('m) = 1; let _ : int('n) = 2; () }
}

function f5(x : (int(3), int)) -> unit = match x {
  y as pair(int('n)) => { let _ : int('n) = 3; () }
}

function f6(x : bits(4)) -> unit = match x {
  y as bits(_) => ()
}

function f7(x : (bool(true), int)) -> unit = match x {
  y as flag('b) => { let _ : bool('b) = true; () }
}

val f8 : forall 'n. bits('n) -> int('n)

function f8(x) = {
  let y as bits('n) = x;
  let z : int('n) = length(y);
  z
}

function f9(x : bits(4)) -> unit = {
  let y as bits('n) = x;
  let _ : int('n) = 4;
  ()
}
