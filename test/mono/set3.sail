default Order dec
$include <prelude.sail>

val _assume : bool -> unit
function _assume(_) = ()

/* An example where we need to case split (because of the sail_zeros
of a non-parameter length), and we need to remember which branch we're
in to type check the bitvector access. */

val topbit : forall 'n, 'n in {8,16}. bits('n) -> bits('n)

function topbit(v) = {
  [v['n - 1]] @ sail_zeros('n - 1);
}

val run : unit -> unit

function run () = {
  assert(topbit(0x08) == 0x00);
  assert(topbit(0x80) == 0x80);
  assert(topbit(0x1080) == 0x0000);
  assert(topbit(0x8010) == 0x8000);
}
