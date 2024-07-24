default Order dec
$include <prelude.sail>

/* A pattern that appears in some vector specification - get a size from a
   register and use it in internal computation. */

register size : bits(2)

function get_size () -> {8,16,32} =
  match size {
  0b00 => 8,
  0b01 => 16,
  _ => 32,
  }

register feature_disable : bool

function is_disabled () -> bool = feature_disable

function f () -> bits(64) = {
  let sz = get_size();
  if (is_disabled()) then { return sail_zeros(64); };
  let 'n = sz;
  let v : bits('n) = match n { 16 => 0x1234, 32 => 0x56789abc };
  sail_zero_extend(v, 64)
}

val run : unit -> unit

function run () = {
  feature_disable = false;
  size = 0b01;
  assert(f() == 0x0000000000001234);
  size = 0b10;
  assert(f() == 0x0000000056789abc);
}
