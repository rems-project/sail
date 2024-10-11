default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

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
    print_endline("ok");
}
