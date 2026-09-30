default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

// Test for the eq_anything primitive
function main() -> unit = {
  // Integers are compared within other types, as each integer has its
  // own singleton type
  let x : option(int) = Some(5);
  assert(eq_anything(x, Some(5)));
  assert(not_bool(eq_anything(x, Some(6))));
  let s : string = "abc";
  assert(eq_anything(s, "abc"));
  assert(not_bool(eq_anything(s, "abd")));
  let b : bits(8) = 0xAB;
  assert(eq_anything(b, 0xAB));
  assert(not_bool(eq_anything(b, 0xAC)));
  let p : (string, string) = ("a", "b");
  assert(eq_anything(p, ("a", "b")));
  assert(not_bool(eq_anything(p, ("a", "c"))));
  let o : option(int) = Some(3);
  assert(eq_anything(o, Some(3)));
  assert(not_bool(eq_anything(o, None())));
}
