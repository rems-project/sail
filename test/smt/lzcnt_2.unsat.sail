default Order dec

$include <prelude.sail>

val lzcnt = "count_leading_zeros" : forall 'w, 'w >= 1. bits('w) -> range(0, 'w)

$property
function prop() -> bool = {
  let p1 = lzcnt(0b000) == 3;
  let p2 = lzcnt(0x000) == 12;
  let p3 = lzcnt(0x020) == 6;
  let p4 = lzcnt(0b011111111) == 1;
  let p5 = lzcnt(0b111) == 0;
  let p6 = lzcnt(0b0 @ 0xF) == 1;
  p1 & p2 & p3 & p4 & p5 & p6
}