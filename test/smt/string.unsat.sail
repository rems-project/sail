default Order dec

$include <prelude.sail>

val "concat_str" : (string, string) -> string

val "eq_string" : (string, string) -> bool

overload operator == = {eq_string}

$property
function prop(() : unit) -> bool = {
  let x = "Hello, ";
  let y = "World!";
  concat_str(x, y) == "Hello, World!"
}