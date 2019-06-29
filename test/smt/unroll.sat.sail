default Order dec

$include <prelude.sail>

$option -smt_unroll_limit 100

$property
function prop(n: int) -> bool = {
  if 0 <= n & n <= 3 then {
    count: int = 0;
    foreach (i from 0 to n) {
      count = count + 1
    };
    count == n
  } else {
    true
  }
}
