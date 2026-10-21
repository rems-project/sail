default Order dec
$include <prelude.sail>

function t() -> bool = true
function f() -> bool = false

// The OCaml backend had a bug because the if ... then ... else ... parse included the rest of a tuple

function main() -> unit = {
  let t1 = (if t() then 1 else 2, true);
  let t2 = (true, if f() then 3 else 4);
  let (i, _) = t1;
  let (_, j) = t2;
  assert (i + j == 5);
}