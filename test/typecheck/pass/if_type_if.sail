default Order dec

$include <prelude.sail>

register R : bool

val only32 : int(32) -> unit

val main : unit -> unit

function main() = {
  let b = R;
  let x = if b then 32 else 64;
  if b then {
    only32(x)
  }
}
