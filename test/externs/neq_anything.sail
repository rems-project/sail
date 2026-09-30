default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

// Test for the neq_anything primitive
function main() -> unit = {
  let x : option(int) = Some(5);
  assert(neq_anything(x, Some(6)));
  assert(not_bool(neq_anything(x, Some(5))));
  let s : string = "abc";
  assert(neq_anything(s, "abd"));
  let p : (string, string) = ("a", "b");
  assert(neq_anything(p, ("a", "c")));
}
