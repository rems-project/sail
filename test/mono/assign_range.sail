default Order dec
$include <prelude.sail>

val use : forall 'n, 'n >= 8. int('n) -> int

function use(n) = {
  let x : bits('n) = sail_sign_extend(0x12, n);
  unsigned(x)
}

val test1 : forall 'n, 'n in {2,4}. int('n) -> int

function test1(n) = {
  size : {'m, 'm >= 8. int('m)} = n * 8;
  use(size)
}

val test2 : forall 'n, 'n in {2,4}. int('n) -> int

function test2(n) = {
  size : range(8,32) = n * 8;
  use(size)
}

val run : unit -> unit

function run () = {
  assert(test1(2) == 18);
  assert(test1(4) == 18);
  assert(test2(2) == 18);
  assert(test2(4) == 18);
}
