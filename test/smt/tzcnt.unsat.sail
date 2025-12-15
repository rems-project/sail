default Order dec

$include <prelude.sail>

val tzcnt = pure "count_trailing_zeros" : forall 'w. bits('w) -> range(0, 'w)

$property
function prop(l : nat) -> bool = {
  let p1 = tzcnt(0x0) == 4;
  let p2 = tzcnt(0x00) == 8;
  let p3 = tzcnt(0x20) == 5;
  let p4 = tzcnt(0b10000000) == 7;
  let p5 = tzcnt(0b1) == 0;
  let p6 = tzcnt(0xF) == 0;
  let p7 = tzcnt(0b0010000) == 4;
  let p8 = (l != 3) | (tzcnt(replicate_bits(0b0, l)) == 3);
  p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8
}
