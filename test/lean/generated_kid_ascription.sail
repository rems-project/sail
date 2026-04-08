// Regression test for generated type kid filtering.
// After rewrite_var_updates, the match acquires an E_typ wrapper
// whose type mentions a generated kid (k___datasize or similar).
// The Lean printer must suppress this ascription to avoid emitting
// invalid Lean identifiers.
default Order dec

$include <prelude.sail>

val test : (bits(1), bool) -> int
function test(x, wide) = {
  let n : {32, 64} = if wide then 64 else 32;
  acc = sail_zeros(n);
  match x {
    0b0 => acc = sail_ones(n),
    _   => ()
  };
  unsigned(acc)
}
