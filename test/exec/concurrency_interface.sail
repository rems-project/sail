default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>
$include <concurrency_interface/exception.sail>

val id_bits64 : bits(64) -> bits(64)

function id_bits64 bv = bv

instantiation sail_mem_read with
  'pa = bits(64),
  'translation_summary = unit,
  'arch_ak = unit,
  'abort = bits(8),
  pa_bits = id_bits64

instantiation sail_mem_write with
  pa_bits = id_bits64

enum my_barrier = Barrier1 | Barrier2

instantiation sail_barrier with 'barrier = my_barrier

register R1 : bits(64)
register R2 : bits(64)

val main : unit -> unit

function main() = {
    let w_req : Mem_write_request(8, 64, bits(64), unit, unit) = struct {
        access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
        va = None(),
        pa = 0x0000_0000_0060_0000,
        translation = (),
        size = 8,
        value = Some(0xABCD_1234_FFFF_5678),
        tag = Some(true),
    };
    match sail_mem_write(w_req) {
        Ok(_) => (),
        Err(abort) => {
            print_bits("abort = ", abort)
        }
    };
    let r_req : Mem_read_request(8, 64, bits(64), unit, unit) = struct {
        access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
        va = None(),
        pa = 0x0000_0000_0060_0000,
        translation = (),
        size = 8,
        tag = false,
    };
    match sail_mem_read(r_req) {
        Ok((value, None())) => {
            print_bits("read memory (no tag read) = ", value)
        },
        _ => print_endline("invalid read"),
    };
    sail_barrier(Barrier1);
    let r_req : Mem_read_request(8, 64, bits(64), unit, unit) = struct {
        access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
        va = None(),
        pa = 0x0000_0000_0060_0000,
        translation = (),
        size = 8,
        tag = true,
    };
    match sail_mem_read(r_req) {
        Ok((value, Some(true))) => {
            print_bits("read memory (true tag) = ", value)
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
