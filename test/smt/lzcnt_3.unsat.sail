default Order dec

$include <prelude.sail>

val lzcnt = "count_leading_zeros" : forall 'w, 'w >= 1. bits('w) -> range(0, 'w)

$property
function prop(bv: bits(5)) -> bool = {
  let x = unsigned(bv);
  if x > 0 then {
    let z = sail_zeros(x);
    let p1 = lzcnt(z) == x;
    let p2 = lzcnt(z @ 0xF) == x;
    let p3 = lzcnt(0x0 @ z) == 4 + x;
    p1 & p2
  } else true
}
