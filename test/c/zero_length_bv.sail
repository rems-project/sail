default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

function main((): unit) -> unit = {
  let x: bits(0) = [];
  if x == sail_zeros(0) then {
    print_endline("ok")
  };
  let x: vector(0, dec, string) = [];
  ()
}
