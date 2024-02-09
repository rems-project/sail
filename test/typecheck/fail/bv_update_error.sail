default Order dec

$include <prelude.sail>

bitfield b : bits(32) = {
  FIELD : 7 .. 0
}

val main : unit -> unit

function main() = {
  let v = Mk_b(0x0000_0000);
  let _ = [v with FIEL = 0xFF];
  ()
}
