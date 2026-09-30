default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __barrier primitive
function main() -> unit = {
  __barrier(Barrier_Sync());
  __barrier(Barrier_RISCV_rw_rw());
}
