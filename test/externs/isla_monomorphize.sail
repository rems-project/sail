default Order dec

$include <prelude.sail>
$include <isla.sail>

// Test for the isla_monomorphize primitive
function main() -> unit = {
  assert(isla_monomorphize(0xDEAD_BEEF) == 0xDEAD_BEEF);
}
