default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  let xs: list(int) = [||];
  var ys: list(int) = [|1|];
  ys = xs;
  print_endline("ok")
}
