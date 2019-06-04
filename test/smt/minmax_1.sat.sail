
val operator == = "eq_int" : (int, int) -> bool

val "max_int" : (int, int) -> int

val "min_int" : (int, int) -> int

$counterexample
function prop(a: int, b: int) -> bool = {
  assert(max_int(a, a) == max_int(b, a));
  true
}
