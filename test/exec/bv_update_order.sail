default Order dec

$include <prelude.sail>

bitfield Foo : bits(4) = {
  A : 3 .. 0,
  B : 3 .. 0
}

function foo() -> unit = {
  let x = Mk_Foo(sail_zeros(4));
  let y = [x with A = 0x5, B = 0x6];
  print_endline(bits_str(y[A]))
}

function bar() -> unit = {
  let x = sail_zeros(4);
  let y = [x with 3 .. 0 = 0x5, 3 .. 0 = 0x6];
  print_endline(bits_str(y[3 .. 0]))
}

function baz() -> unit = {
  let x = sail_zeros(4);
  let y = [x with 0 = bitone, 0 = bitzero];
  print_endline(bits_str(y[3 .. 0]))
}

function main() -> unit = {
  foo();
  bar();
  baz();
}
