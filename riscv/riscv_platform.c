#include "sail.h"
#include "rts.h"
#include "riscv_prelude.h"

bool plat_enable_dirty_update(unit u)
{ return false; }

bool plat_enable_misaligned_access(unit u)
{ return false; }

mach_bits plat_ram_base(unit u)
{ return 0; }

mach_bits plat_ram_size(unit u)
{ return 0; }

mach_bits plat_rom_base(unit u)
{ return 0; }

mach_bits plat_rom_size(unit u)
{ return 0; }

mach_bits plat_clint_base(unit u)
{ return 0; }

mach_bits plat_clint_size(unit u)
{ return 0; }

bool within_phys_mem(mach_bits addr, sail_int len)
{ return 0; }

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
{ return 0; }
