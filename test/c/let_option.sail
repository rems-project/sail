default Order dec

$include <prelude.sail>
$include <string.sail>
$include <mapping.sail>

overload operator ^ = {concat_str}

let x : option(bits(32)) = None()
let y : option(bits(128)) = None()

function main() -> unit = {
    match x {
      Some(x) => print_endline("x is " ^ bits_str(x)),
      _ => print_endline("x is None()"),
    };
}
