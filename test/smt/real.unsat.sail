default Order dec

$include <prelude.sail>
$include <real.sail>

$property
val prop : (real, real, real) -> bool effect {escape}

function prop(x, y, z) = {
  assert(x * y == y * x);
  assert(x * (y * z) == (x * y) * z);
  assert(x - x == 0.0);
  assert(x * 0.0 == 0.0);
  assert(x * 1.0 == x);

  if not_bool(x == 0.0) then {
    assert(x * (y / x) == y)
  };

  // Comparisons
  assert(x <= x);
  assert(x >= x);
  if x > y then {
    assert(y < x)
  };
  if x < y & y < z then {
    assert(x < z)
  };
  if x <= y & y <= x then {
    assert(x == y)
  };
  true
}