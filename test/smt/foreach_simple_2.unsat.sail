default Order dec

$include <prelude.sail>

let C = 0

$property
function prop() -> bool = {
  let n = 3;
  bv = 0x0;
  foreach (i from C to n) {
    bv[i] = bitone
  };
  bv == 0xF
}
