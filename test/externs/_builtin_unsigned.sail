default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the _builtin_unsigned primitive
function main() -> unit = {
  assert(_builtin_unsigned(0x00) == 0);
  assert(_builtin_unsigned(0xFF) == 255);
  assert(_builtin_unsigned(0xFFFF_FFFF_FFFF_FFFF) == 18446744073709551615);
}
