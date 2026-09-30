default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the _builtin_pow2 primitive
function main() -> unit = {
  assert(_builtin_pow2(0) == 1);
  assert(_builtin_pow2(4) == 16);
  assert(_builtin_pow2(64) == 18446744073709551616);
}
