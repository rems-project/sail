default Order dec

$include <prelude.sail>

register R : bits(32) = 0x0000_0000

// Test for the __deref primitive
function main() -> unit = {
  R = 0xDEAD_BEEF;
  assert(__deref(ref R) == 0xDEAD_BEEF);
  let r = ref R;
  R = 0xCAFE_F00D;
  assert(__deref(r) == 0xCAFE_F00D);
}
