default Order dec

$include <prelude.sail>

val lzcnt = pure "count_leading_zeros" : forall 'w. bits('w) -> range(0, 'w)

$property
function prop(l : nat) -> bool = {
  let p1 = lzcnt(0x0) == 4;
  let p2 = lzcnt(0x00) == 8;
  let p3 = lzcnt(0x02) == 6;
  let p4 = lzcnt(0b01111111) == 1;
  let p5 = lzcnt(0b1) == 0;
  let p6 = lzcnt(0xF) == 0;
  let p7 = lzcnt(0x007aaaaaaaaaaaaaa) == 9;
  let p8 = (l != 3) | (lzcnt(replicate_bits(0b0, l)) == l);
  p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8
}