default Order dec

$include <prelude.sail>

overload ~ = {not_bool}

$property
function prop(x: int, y: int, z: int) -> bool = {
  let lteq_refl    = x <= x;
  let lteq_trans   = (if x <= y & y <= z then x <= z else true);
  let lteq_antisym = (if x <= y & y <= x then x == y else true);

  let lt_irrefl = ~(x < x);
  let lt_trans  = (if x < y & y < z then x < z else true);

  let lt_implies_lteq = (if x < y then x <= y else true);

  let gteq_refl    = x >= x;
  let gteq_trans   = (if x >= y & y >= z then x >= z else true);
  let gteq_antisym = (if x >= y & y >= x then x == y else true);

  let gt_irrefl = ~(x > x);
  let gt_trans  = (if x > y & y > z then x > z else true);

  let gt_implies_gteq = (if x > y then x >= y else true);

  let lt_negate = (if x > 0 then negate(x) < x else true);
  let gt_negate = (if x < 0 then negate(x) > x else true);

  lteq_refl & lteq_trans & lteq_antisym & lt_irrefl & lt_trans & lt_implies_lteq
  & gteq_refl & gteq_trans & gteq_antisym & gt_irrefl & gt_trans & gt_implies_gteq
  & lt_negate & gt_negate
}
