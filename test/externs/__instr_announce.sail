default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __instr_announce primitive
function main() -> unit = {
  __instr_announce(0xDEAD_BEEF);
}
