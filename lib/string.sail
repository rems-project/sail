$ifndef _STRING
$define _STRING

val eq_string = {lem: "eq", coq: "generic_eq", _: "eq_string"} : (string, string) -> bool

overload operator == = {eq_string}

val "print_endline" : string -> unit

val concat_str = {lem: "stringAppend", _: "concat_str"} : (string, string) -> string

$endif
