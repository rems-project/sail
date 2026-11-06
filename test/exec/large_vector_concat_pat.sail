default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  let x : bits(70) = 0xFFFF_FFFF_FFFF_FFFF @ 0b000000;
  match x {
    0b1 @ x : bits(68) @ 0b0 => print_bits("ok ", x),
    _ => print_endline("fail"),
  }
}
