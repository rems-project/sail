default Order dec

$include <prelude.sail>

$option -smt_unroll_limit 100

$property :query all return
function prop(n: int) -> bool = {
  if 0 <= n & n <= 50 then {
    count: int = 0;
    foreach (i from 0 to (n - 1)) {
      count = count + 1
    };
    count == n
  } else {
    true
  }
}
