default Order dec

$include <prelude.sail>

// Test for the undefined_list primitive
function main() -> unit = {
  let xs : list(int) = undefined_list(0);
  match xs {
    [||] => (),
    _ => (),
  }
}
