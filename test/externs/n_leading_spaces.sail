default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the n_leading_spaces primitive
function main() -> unit = {
  assert(n_leading_spaces("") == 0);
  assert(n_leading_spaces("abc") == 0);
  assert(n_leading_spaces(" abc") == 1);
  assert(n_leading_spaces("   abc") == 3);
  assert(n_leading_spaces("  ") == 2);
  assert(n_leading_spaces("a  ") == 0);
}
