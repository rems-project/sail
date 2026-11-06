default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the __monomorphize primitive
function main() -> unit = {
  assert(__monomorphize(0xDEAD_BEEF) == 0xDEAD_BEEF);
  assert(__monomorphize(0b1) == 0b1);
}
