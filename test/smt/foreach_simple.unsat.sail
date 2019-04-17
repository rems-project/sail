default Order dec

$include <prelude.sail>

$property
function prop() -> bool = {
  let n = 3;
  bv = 0x0;
  foreach (i from 0 to n) {
    bv[i] = bitone
  };
  bv == 0xF
}
