default Order dec
$include <prelude.sail>

/* Another byte/bit size conversion */

val bar : forall 'n. int('n) -> bits(8 * 'n)

function bar (n) = replicate_bits(0x12,n)

val foo : forall 'size, 8 * 'size >= 0. int('size) -> bits(8 * 'size)

function foo(size) = {
  assert('size == 1 | 'size == 2, "size");
  return bar('size)
}

val run : unit -> unit

function run () = {
  assert(foo(1) == 0x12);
  assert(foo(2) == 0x1212);
}
