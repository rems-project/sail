default Order dec

$include <prelude.sail>

val "concat_str" : (string, string) -> string

infixl 1 ++

overload operator ++ = {concat_str}

val "print_endline" : string -> unit

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val DecStr = "decimal_string_of_bits" : forall 'n. bits('n) -> string

function main(() : unit) -> unit = {
  foreach (i from 0 to 5) {
    let x = "Hello";
    let y = "World";
    let z = 0b1111_0000_111;
    let w = 0xFF;
    print_endline(x ++ y ++ BitStr(z) ++ " " ++ BitStr(w))
  }
}
