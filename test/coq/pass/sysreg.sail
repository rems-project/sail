default Order dec
$include <prelude.sail>
$include <concurrency_interface/read_write.sail>
$include <concurrency_interface/sysreg.sail>

// Instantiate the memory read interface so that the Coq backend uses the
// concurrency interface
function pa_bits(x : bits(64)) -> bits(64) = x

instantiation sail_mem_read with
  'pa = bits(64),
  'translation_summary = unit,
  'arch_ak = unit,
  'abort = unit,
  pa_bits = pa_bits

instantiation sail_sys_reg_read with 'id = (bits(2), bits(3))
instantiation sail_sys_reg_write with 'id = (bits(2), bits(3))

register ABC : bits(64)

function test() -> unit = {
  let x = sail_sys_reg_read((0b01, 0b101), ref ABC);
  sail_sys_reg_write((0b01, 0b101), ref ABC, x | 0x0000000000000001);
}
