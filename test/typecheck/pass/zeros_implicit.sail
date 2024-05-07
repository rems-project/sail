default Order dec

$include <prelude.sail>

val zeros_implicit : forall 'n, 'n >= 0. implicit('n) -> bits('n)

function zeros_implicit (n) = sail_zeros(n)

overload zeros = {sail_zeros, zeros_implicit}

val main : unit -> unit

function main() = {
  let _ : bits(32) = zeros();
  let _ : bits(64) = zeros(64);
  ()
}
