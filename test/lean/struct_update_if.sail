default Order dec
$include <prelude.sail>

// We used to produce output for effectful updates to struct fields with
// conditionals that Lean couldn't cope with; ensure that we're producing a
// working mixing of do-notation and indentation.

struct foo = {
  abcd : int,
  efgh : int,
}

register R1 : bool
register R2 : int

function f(x : foo) -> int = {
  let y = { x with abcd = if R1 then 1 else 1 + R2 };
  y.abcd + y.efgh
}
