default Order dec

$option -undefined_gen

$include <prelude.sail>

struct S = {
  f1 : {0, 1}
}

function main() -> unit = {
  print_endline("ok");
}
