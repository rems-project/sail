default Order dec

$include <prelude.sail>

val "eq_string" : (string, string) -> bool

overload operator == = {eq_string}

register R : bool

val "print_endline" : string -> unit

function IMPDEF(str : string) -> bool = {
  if str == "A" then {
    return(R)
  } else if str == "B" then {
    true
  } else {
    false
  }
}

function main(() : unit) -> unit = {
  R = true;
  if IMPDEF("A") then {
    print_endline("true")
  } else {
    print_endline("false")
  }
}