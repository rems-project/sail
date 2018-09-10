#include "riscv_platform_impl.h"

/* Settings of the platform implementation, with common defaults. */

bool rv_enable_dirty_update = false;
bool rv_enable_misaligned   = false;

uint64_t rv_ram_base = UINT64_C(0x80000000);
uint64_t rv_ram_size = UINT64_C(0x80000000);

uint64_t rv_rom_base = UINT64_C(0x1000);
uint64_t rv_rom_size = UINT64_C(0x100);

uint64_t rv_clint_base = UINT64_C(0x2000000);
uint64_t rv_clint_size = UINT64_C(0xc0000);

uint64_t rv_htif_tohost = UINT64_C(0x80001000);
