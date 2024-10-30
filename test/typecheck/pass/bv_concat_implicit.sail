default Order dec

$include <prelude.sail>

val zeros : forall 'n. implicit('n) -> bits('n)

val main : unit -> unit

function main() = {
  let x : bits(5) = zeros() @ 0b1;
  let y : bits(5) = 0b1 @ zeros();
  let z : bits(5) = 0b1 @ zeros() @ 0b00;
}
