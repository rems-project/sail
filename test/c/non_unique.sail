default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

function f(_: int) -> unit = ()
function g(_: bits(1)) -> unit = ()

function main(() : unit) -> unit = {
  let y : int = {
    let x : int = 3;
    x
  };
  {
    let x : bits(1) = 0b0;
    g(x)
  };
  print_endline("ok");
}