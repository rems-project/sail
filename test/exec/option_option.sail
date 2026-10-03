default Order dec

$include <prelude.sail>
$include <string.sail>

function main() -> unit = {
  match Some(Some(0b00)) {
    Some(Some(_)) => print_endline("Some Some"),
    Some(None())  => print_endline("Some None"),
    None()        => print_endline("None"),
  };
  ()
}
