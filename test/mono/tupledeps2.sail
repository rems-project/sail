default Order dec
$include <prelude.sail>

// In this version the 'n will be rewritten to bitvector_length(v) by the
// typechecker, so the analysis has to spot that the dependency is on 'n
// and not v.

val f : forall 'n, 'n in {8, 16, 32}. (bits('n)) -> bits(16)

function f(v) = {
  let (w, sz) : (bits(32), nat) = match 'n {
    8 => (sail_zero_extend(v, 32), 4),
    16 => (sail_zero_extend(v, 32), 8),
    32 => (v, 12),
  };
  assert(0 < sz & sz <= 12);
  sail_zero_extend(w[sz - 1 .. 0], 16)
}

function run () -> unit = {
  assert(f(0x11) == 0x0001);
  assert(f(0x1234) == 0x0034);
  assert(f(0x12345678) == 0x0678);
}
