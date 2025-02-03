default Order dec
$include <prelude.sail>

register R0 : bits(32)

function test(v : vector(16, bits(32))) -> bool = {
  let r = R0;
  foreach (i from 0 to 15)
    if v[i] == r then return true;
  false
}
