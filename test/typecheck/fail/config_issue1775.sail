default Order dec

$include <prelude.sail>

function main() -> unit = {
  let x : bool = config foo.bar;
  let y : bool = config foo;
  print_endline("Test");
}
