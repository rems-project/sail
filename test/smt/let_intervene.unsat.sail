default Order dec

$include <prelude.sail>

$property
val prop : unit -> bool

let C = 0
let x = bitone

function prop() = {
  let n = 3;
  bv = 0x0;
  foreach (i from C to n) {
    bv[i] = x
  };
  bv == 0xF
}
