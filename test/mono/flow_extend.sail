default Order dec
$include <prelude.sail>

val byte_extend : forall 'n, 'n >= 8. (bits(8), int('n)) -> bits('n)

function byte_extend (v, n) = if (n == 8) then v else sail_zero_extend(v, n)

val run : unit -> unit

function run() = {
  assert(byte_extend(0x12,8) == 0x12);
  assert(byte_extend(0x12,16) == 0x0012);
}
