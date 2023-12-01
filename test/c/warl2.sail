default Order dec

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
  let z: WARL_range = x;
  print_endline("ok")
}
