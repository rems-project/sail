default Order dec

$include <prelude.sail>

$option --const-prop-mutrec probe

register R : bool = false

val probe : bool -> bool

val bounce : bool -> bool

function probe b =
  if b then
    bounce(false)
  else {
    let _ = { R = true; () };
    R
  }

function bounce b = probe(b)

val main : unit -> unit

function main() = {
  let _ = probe(false);
  if R then {
    print_endline("ok")
  }
}
