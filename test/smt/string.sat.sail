default Order dec

$include <prelude.sail>

val "concat_str" : (string, string) -> string

val "eq_string" : (string, string) -> bool

overload operator == = {eq_string}

$counterexample
function prop(x : string) -> bool = {
  let y = ", World!";
  not_bool(concat_str(x, y) == "Hello, World!")
}