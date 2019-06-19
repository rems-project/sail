default Order dec

$include <vector_dec.sail>

val main : unit -> unit effect {escape}

function main () = {
  foreach (i from 0 to 32 by 1 in inc) {
    assert(count_leading_zeros(sail_shiftright(0xDEADBEEF, i)) == i);
  }
}
