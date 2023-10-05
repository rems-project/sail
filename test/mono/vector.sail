default Order dec
$include <prelude.sail>

/* Check case splitting on a vector */

val test : bits(32) -> nat

function test((sel : bits(2)) @ (_ : bits(30))) = {
  match (sel) {
    0b00 => 5,
    0b10 => 1,
    _ => 0
  }
}

val run : unit -> unit

function run () = {
  assert(test(0x0f353533) == 5);
  assert(test(0x84534656) == 1);
  assert(test(0xf3463903) == 0);
}
