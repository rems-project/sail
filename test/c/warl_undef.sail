default Order dec

$option -undefined_gen

$include <prelude.sail>
$include <generic_equality.sail>

val "print_endline" : string -> unit

struct WARL_range = {
  rangelist : list(int),
}

let x : WARL_range = struct {
  rangelist = [|0, 1|]
}

function main () : unit -> unit = {
  let z: WARL_range = undefined;
  print_endline("ok")
}
