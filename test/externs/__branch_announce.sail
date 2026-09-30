default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __branch_announce primitive
function main() -> unit = {
  __branch_announce(64, 0x0000_0000_8000_0000);
  __branch_announce(32, 0x8000_0000);
}
