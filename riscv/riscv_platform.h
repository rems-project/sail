#pragma once
#include "sail.h"

bool plat_enable_dirty_update(unit);
bool plat_enable_misaligned_access(unit);

mach_bits plat_ram_base(unit);
mach_bits plat_ram_size(unit);
bool within_phys_mem(mach_bits, sail_int);

mach_bits plat_rom_base(unit);
mach_bits plat_rom_size(unit);

mach_bits plat_clint_base(unit);
mach_bits plat_clint_size(unit);

unit load_reservation(mach_bits);
bool match_reservation(mach_bits);
unit cancel_reservation(unit);

void plat_insns_per_tick(sail_int *rop, unit);

unit plat_term_write(mach_bits);
mach_bits plat_htif_tohost(unit);

unit memea(mach_bits, sail_int);

