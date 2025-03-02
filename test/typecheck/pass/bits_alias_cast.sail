default Order dec
$include <prelude.sail>

// Check that we can put a suitable bitvector into a context that expects a
// non-trivial bitvector alias.  A case involving a struct like this came up in
// the RISC-V model and required a more explicit cast for the Coq version.

type foo('a) = bits(if 'a == 1 then 8 else 16)

struct bar('a) = {
  fld : foo('a),
}

function change forall 'n, 'n in {1,2}. (x : bits(8 * 'n)) -> bar('n) = struct { fld = x }
