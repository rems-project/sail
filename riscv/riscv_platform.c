#include "sail.h"
#include "rts.h"
#include "riscv_prelude.h"
#include "riscv_platform_impl.h"

/* This file contains the definitions of the C externs of Sail model. */

bool plat_enable_dirty_update(unit u)
{ return rv_enable_dirty_update; }

bool plat_enable_misaligned_access(unit u)
{ return rv_enable_misaligned; }

mach_bits plat_ram_base(unit u)
{ return rv_ram_base; }

mach_bits plat_ram_size(unit u)
{ return rv_ram_size; }

mach_bits plat_rom_base(unit u)
{ return rv_rom_base; }

mach_bits plat_rom_size(unit u)
{ return rv_rom_size; }

mach_bits plat_clint_base(unit u)
{ return rv_clint_base; }

mach_bits plat_clint_size(unit u)
{ return rv_clint_size; }

unit load_reservation(mach_bits addr)
{ return UNIT; }

bool match_reservation(mach_bits addr)
{ return false; }

unit cancel_reservation(unit u)
{ return UNIT; }

unit plat_term_write(mach_bits c)
{ return UNIT; }

void plat_insns_per_tick(sail_int *rop, unit u)
{ }

mach_bits plat_htif_tohost(unit u)
{
  return rv_htif_tohost;
}

unit memea(mach_bits len, sail_int n)
{
  return UNIT;
}
