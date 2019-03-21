default Order dec

$include <flow.sail>
$include <exception_basic.sail>

val "print_endline" : string -> unit

register R : bool

function main((): unit) -> unit = {
  R = false;
  let 'x = 3180327502475943573495720457203572045720485720458724;
  y : range(0, 'x) = 1;
  if R then {
    assert(constraint('x <= 2));
    y = 2;
    let z = y;
    let x = 2;
    ()
  } else {
    print_endline("ok")
  }
}
