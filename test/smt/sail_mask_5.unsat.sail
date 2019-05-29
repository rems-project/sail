default Order dec

$include <prelude.sail>

$property
function prop forall 'n, 31 <= 'n <= 128. (n: int('n)) -> bool = {
  let x = sail_mask(n, 0xdeadbeef);
  if n >= 32 then
     assert(x == sail_zero_extend(0xdeadbeef, n))
  else
     assert(0b1011110101011011011111011101111 == x);
  true
}
