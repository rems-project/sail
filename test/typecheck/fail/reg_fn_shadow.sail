default Order dec

$include <prelude.sail>

register foo : int = 4

function foo() -> nat = 5

function main() -> unit = {
  print_endline(dec_str(foo));
  print_endline(dec_str(foo()));
}
