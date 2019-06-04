default Order dec

$include <prelude.sail>
$include "test/arch.sail"

/* Default memory model is as weak as possible, so this is not true */
$counterexample
function prop() -> bool = {
  let _ = arch_load(0b00, 0b01);
  let _ = arch_store(0b10, 0b00);
  X(0b01) == X(0b10)
}
