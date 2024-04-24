default Order dec

$include <prelude.sail>

bitfield foo : bits(8) = {
  f1 : 3 .. 0,
  f2 : 7 .. 4,
}

val main : unit -> unit

function main() = {
  let x = [Mk_foo(0x00) with f1 = 0xA, f2 = 0xB, ];
  ()
}