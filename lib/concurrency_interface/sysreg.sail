$sail_internal

$ifndef _CONCURRENCY_INTERFACE_SYSREG
$define _CONCURRENCY_INTERFACE_SYSREG

$include <concurrency_interface/common.sail>

outcome sail_sys_reg_write : forall 'a. ('id, register('a), 'a) -> unit
with
  'id : Type
= {
  impl emulator_or_isla(_id, reg, value) = *reg = value
}

outcome sail_sys_reg_read : forall 'a. ('id, register('a)) -> 'a
with
  'id : Type
= {
  impl emulator_or_isla(_id, reg) = *reg
}

$endif
