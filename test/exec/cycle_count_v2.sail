default Order dec

$define CONCURRENCY_INTERFACE_V2

$include <prelude.sail>
$include <concurrency_interface.sail>
$include <concurrency_interface/exception.sail>

// Separated from the main interface v2 test because we intend to move it out to
// the Arm model.

val id_bits64 : bits(64) -> bits(64)

function id_bits64 bv = bv

val unit_true : unit -> bool
function unit_true () = true

val unit_false : unit -> bool
function unit_false () = true

val unit_zero : unit -> int
function unit_zero () = 0

instantiation sail_mem_read with
  'addr_size = 64,
  'addr_space = unit,
  'mem_acc = unit,
  mem_acc_is_explicit = unit_true,
  mem_acc_is_ifetch = unit_false,
  mem_acc_is_ttw = unit_false,
  mem_acc_is_relaxed = unit_true,
  mem_acc_is_rel_acq_rcpc = unit_false,
  mem_acc_is_rel_acq_rcsc = unit_false,
  mem_acc_is_standalone = unit_true,
  mem_acc_is_exclusive = unit_false,
  mem_acc_is_atomic_rmw = unit_false,
  'abort = bits(8),
  'CHERI = true,
  'cap_size_log = 3



instantiation sail_mem_write with
  'addr_size = 64,
  'addr_space = unit,
  'mem_acc = unit,
  mem_acc_is_explicit = unit_true,
  mem_acc_is_ifetch = unit_false,
  mem_acc_is_ttw = unit_false,
  mem_acc_is_relaxed = unit_true,
  mem_acc_is_rel_acq_rcpc = unit_false,
  mem_acc_is_rel_acq_rcsc = unit_false,
  mem_acc_is_standalone = unit_true,
  mem_acc_is_exclusive = unit_false,
  mem_acc_is_atomic_rmw = unit_false,
  'abort = bits(8),
  'CHERI = true,
  'cap_size_log = 3

enum my_barrier = Barrier1 | Barrier2

instantiation sail_barrier with 'barrier = my_barrier

instantiation sail_take_exception with 'exn = int
instantiation sail_return_exception

register R1 : bits(64)
register R2 : bits(64)

val main : unit -> unit

function main() = {
    /* Cycle count primitives */
    sail_end_cycle();
    let c = sail_get_cycle_count();
    print_int("c = ", c);
}
