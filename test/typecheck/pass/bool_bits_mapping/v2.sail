default Order dec

$include <prelude.sail>

mapping bool_bool : bool <-> bool = {
  true   <-> false,
  false  <-> true
}

val "print_endline" : string -> unit

function main((): unit) -> unit = {
  if bool_bool(true) then {
    print_endline("true")
  } else {
    print_endline("false")
  };
  if bool_bool(false) then {
    print_endline("true")
  } else {
    print_endline("false")
  }
}