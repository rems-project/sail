default Order dec

$include <prelude.sail>

overload operator == = {eq_string}

$property
function prop(() : unit) -> bool = {
  let x = "Hello, ";
  let y = "World!";
  concat_str(x, y) == "Hello, World!"
}