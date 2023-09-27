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
  let y = x;
  assert(x == y);
  assert(x == x);
  let z = y;
  assert(z.rangelist != [||]);
  print_endline("ok")
}
