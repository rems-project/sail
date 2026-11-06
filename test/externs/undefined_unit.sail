default Order dec

$include <prelude.sail>

// Test for the undefined_unit primitive
function main() -> unit = {
  let u : unit = undefined_unit();
  match u {
    () => (),
  }
}
