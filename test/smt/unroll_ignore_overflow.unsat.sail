default Order dec

$option -smt_ignore_overflow

$include <prelude.sail>

$property
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
