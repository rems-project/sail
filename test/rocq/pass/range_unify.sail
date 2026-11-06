default Order dec
$include <prelude.sail>

// Example from RISC-V where poor unification confused the Rocq backend (it saw ('n - 1) + 1 for
// the x argument and inserted an unnecessary cast).

val lowest_index_of : forall 'n, 'n >= 0. (bits('n), bits(1)) -> option(range(0, 'n - 1))

val least_significant_zero : forall 'n, 'n >= 0. (bits('n)) -> option(range(0, 'n - 1))
function least_significant_zero(x) =
  lowest_index_of(x, 0b0)

