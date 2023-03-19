/* An example where we need to introduce a new case split in the middle of
   the function.  A purer companion to the vectorsize test. */

default Order dec
$include <prelude.sail>
$include <smt.sail>

register size : bits(2)

function get_size() -> {|8,16,32,64|} = {
  shl_int(8, unsigned(size))
}

// Functions that will force their arguments to be monomorphised

val use_bytes : forall 'bytes, 'bytes > 0. int('bytes) -> bits(8 * 'bytes)

function use_bytes(bytes) = {
  let x : bits(8 * 'bytes) = sail_zero_extend(0b1, 8 * bytes);
  x
}

val use_size : forall 'n, 'n > 0. int('n) -> int

function use_size(n) = {
  let x : bits('n) = sail_zero_extend(0b1, n);
  unsigned(x)
}

// Get a size, derive another integer that will need to be
// monomorphised (for the call to use_bytes), and only then
// actually bind a type variable.

function f() -> int = {
  let sz = get_size();
  let bytes = ediv_int(sz,8);

  let 'n = sz;

  let a : bits('n) = sail_zeros(sz);
  let b : bits('n) = add_bits(a, use_bytes(bytes));
  let c : bits('n) = add_bits_int(b, use_size(sz));

  unsigned(c)
}

// Similar test, but makes both explicit type variables

function g() -> int = {
  let sz = get_size();
  let sz2 = 2 * sz;

  let 'm = sz;
  let 'n = sz2;

  let a : bits('m) = sail_zeros(sz);
  let b : bits('n) = add_bits(sail_zero_extend(a, sz2), sail_zero_extend(0x3, sz2));
  let c : bits('m) = add_bits_int(b[sz - 1 .. 0], use_size(sz));

  unsigned(c)
}

function run() -> unit = {
  assert(f() == 2);
  assert(g() == 4);
}
