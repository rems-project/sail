
val operator == = "eq_int" : (int, int) -> bool

val "max_int" : (int, int) -> int

val "min_int" : (int, int) -> int

$property
function prop(a: int, b: int) -> bool = {
  assert(max_int(3, 2) == 3);
  assert(min_int(3, 2) == 2);
  assert(max_int(-132542345, 3) == 3);

  assert(max_int(a, b) == max_int(b, a));
  assert(min_int(a, b) == min_int(b, a));

  assert(max_int(0, 0) == 0);

  true
}
