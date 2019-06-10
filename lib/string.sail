$ifndef _STRING
$define _STRING

$include <arith.sail>

val eq_string = {lem: "eq", coq: "generic_eq", _: "eq_string"} : (string, string) -> bool

overload operator == = {eq_string}

val "print_endline" : string -> unit

$endif
