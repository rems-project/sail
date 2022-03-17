default Order dec

$include <prelude.sail>

struct phantom('n: Int) = {
  bits: bits('n),
}

val id : forall ('a: Type). 'a -> 'a

function id(x) = x

val main : unit -> unit

function main() = {
  let _ = id(struct { bits = 0x0000_0000 } : phantom(32));
  ()
}
