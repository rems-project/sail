default Order dec

$include <prelude.sail>

union phantom('n: Int) = {
  Bits: bits('n),
}

val id : forall ('a: Type). 'a -> 'a

function id(x) = x

val main : unit -> unit

function main() = {
  let _ = id(Bits(0x0000_0000) : phantom(32));
  ()
}
