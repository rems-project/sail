default Order dec

$option -undefined_gen

$include <prelude.sail>

$[undefined_gen skip]
struct S = {
  f1 : {0, 1}
}

val undefined_S : unit -> S

function undefined_S() = struct { f1 = 0 }

function main() -> unit = {
  let _ : S = undefined;
  print_endline("ok");
}
