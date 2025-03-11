default Order dec

$define CONCURRENCY_INTERFACE_V3

$include <prelude.sail>
$include <concurrency_interface.sail>
$include <concurrency_interface/exception.sail>

val id_bits64 : bits(64) -> bits(64)

function id_bits64 bv = bv

val unit_true : unit -> bool
function unit_true () = true

val unit_false : unit -> bool
function unit_false () = true

val unit_zero : unit -> int
function unit_zero () = 0

instantiation sail_mem_read with
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
  CHERI = unit_false,
  cap_size = unit_zero



instantiation sail_mem_write with
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
  CHERI = unit_false,
  cap_size = unit_zero

enum my_barrier = Barrier1 | Barrier2

instantiation sail_barrier with 'barrier = my_barrier

register R1 : bits(64)
register R2 : bits(64)

val main : unit -> unit

function main() = {
    let w_req : Mem_write_request(8, 1, 64, unit, unit) = struct {
        access_kind = (),
        address = 0x0000_0000_0060_0000,
        address_space = (),
        size = 8,
        num_tag = 1,
        value = [0xAB, 0xCD, 0x12, 0x34, 0xFF, 0xFF, 0x56, 0x78],
        tags = [true]
    };
    match sail_mem_write(w_req) {
        Ok(_) => (),
        Err(abort) => {
            print_bits("abort = ", abort)
        }
    };
    let r_req : Mem_read_request(8, 0, 64, unit, unit) = struct {
        access_kind = (),
        address = 0x0000_0000_0060_0000,
        address_space = (),
        size = 8,
        num_tag = 0
    };
    match sail_mem_read(r_req) {
        Ok((value, _)) => {
            print_bits("read memory (no tag read) = ", from_bytes(value))
        },
        _ => print_endline("invalid read"),
    };
    sail_barrier(Barrier1);
    let r_req : Mem_read_request(8, 1, 64, unit, unit) = struct {
        access_kind = (),
        address = 0x0000_0000_0060_0000,
        address_space = (),
        size = 8,
        num_tag = 1,
    };
    match sail_mem_read(r_req) {
        Ok((value, v)) if v[0] => {
            print_bits("read memory (true tag) = ", from_bytes(value))
        },
        _ => print_endline("invalid read"),
    };

    /* Cycle count primitives */
    sail_end_cycle();
    let c = sail_get_cycle_count();
    print_int("c = ", c);

    /* Instruction and branch announce events */
    sail_instr_announce(0xABCD_1234);
    sail_branch_announce(64, 0x0000_0000_0000_4000);

    /* Isla relaxed register support */
    sail_reset_registers();
    sail_synchronize_registers();

    /* Isla mark register builtins */
    sail_mark_register(ref R1, "MARK");
    sail_mark_register_pair(ref R1, ref R2, "MARK2");

    print_bits("", __monomorphize(0xFFFF));
}
