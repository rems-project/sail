default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the _builtin_mod_nat primitive
function main() -> unit = {
  assert(_builtin_mod_nat(7, 3) == 1);
  assert(_builtin_mod_nat(6, 3) == 0);
  assert(_builtin_mod_nat(0, 3) == 0);
}
