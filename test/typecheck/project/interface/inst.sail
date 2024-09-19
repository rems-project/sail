default Order dec

$include <concurrency_interface.sail>

val identity : unit -> bits(64)

instantiation sail_mem_write with
  'pa = unit,
  'translation_summary = unit,
  'arch_ak = unit,
  'abort = unit,
  pa_bits = identity
