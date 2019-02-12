default Order dec

$include <prelude.sail>

mapping bool_bits : bool <-> bits(1) = {
  true   <-> 0b1,
  false  <-> 0b0
}

val "print_endline" : string -> unit

function main((): unit) -> unit = {
  if bool_bits(0b1) then {
    print_endline("ok")
  } else {
    print_endline("fail")
  };
  if bool_bits(true) == 0b1 then {
    print_endline("ok")
  } else {
    print_endline("fail")
  }
}