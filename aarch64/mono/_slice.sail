val IsZero_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsZero_slice (xs, i, 'l) = {
  assert(constraint('l >= 0));
  IsZero(xs & slice_mask(i, l))
}

val IsOnes_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsOnes_slice (xs, i, 'l) = {
  assert(constraint('l >= 0));
  let m : bits('n) = slice_mask(i,l) in
  (xs & m) == m
}

val ZeroExtend_slice_append : forall 'n 'm 'o, 'n >= 0 & 'm >= 0 & 'o >= 0.
  (bits('n), int, int, bits('m)) -> bits('o) effect {escape}

function ZeroExtend_slice_append (xs, i, 'l, ys) = {
  assert(constraint('l >= 0));
  let xs = xs & slice_mask(i,l) in
  let xs : bits('o) = extzv(xs >> i) << 'm in
  let ys : bits('o) = extzv(ys) in
  xs | ys
}

val IsZero_slice2 : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsZero_slice2 (xs, i, 'l) = {
  assert(constraint('l >= 0));
  IsZero(xs & slice_mask(i, l))
}
