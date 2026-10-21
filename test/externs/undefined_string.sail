default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the undefined_string primitive
function main() -> unit = {
  let s : string = undefined_string();
  assert(string_length(s) >= 0);
}
