default Order dec
$include <prelude.sail>
$include <result.sail>

// Check that result (which is declared as an "external" type, and is provided
// by the coq-sail library) is renamed when it appears as a variable identifier
// and left alone as a type name.

function main() -> bool = {
  let result : int = 5;
  let r : result(int,string) = Ok(result);
  is_ok(r)
}
