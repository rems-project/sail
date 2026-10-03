default Order dec
$include <prelude.sail>

type is_nice_size('sz) -> Bool = 'sz in {32,64}
type is_smaller_size('sz) -> Bool = 'sz == 32
type my_bits('sz), is_nice_size('sz) = bits(if is_smaller_size('sz) then 8 else 16)

function main() -> unit = {
  let x : my_bits(32) = sail_ones(8);
  let y : my_bits(64) = sail_zero_extend(x, 16);
  assert(y == 0x00ff);
}
