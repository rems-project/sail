default Order dec
$include <prelude.sail>
$include <concurrency_interface.sail>

/* Casting test extracted from the simple-arm model */

type TranslationInfo = unit
type arm_acc_type = unit
type Fault = unit

val pa_bits : bits(56) -> bits(64)

function pa_bits(bv) = sail_zero_extend(bv, 64)
val rMem : bits(64) -> bits(64)

/* When checking whether the req passed to sail_mem_read needs a cast, it has to expand this alias. */

type MemReadReq('n), 'n > 0 = Mem_read_request('n, 64, bits(56), option(TranslationInfo), arm_acc_type)

instantiation sail_mem_read with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

function rMem(addr) = {
  let req : MemReadReq(8) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = truncate(addr, 56),
    translation = None(),
    size = 8,
    tag = false
  };
  match sail_mem_read(req) {
    Ok((value, _)) => value,
    Err(_) => exit(),
  }
}
