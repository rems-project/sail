#pragma once

#include <stdbool.h>
#include <stdint.h>

/* Settings of the platform implementation. */

extern bool rv_enable_dirty_update;
extern bool rv_enable_misaligned;

extern uint64_t rv_ram_base;
extern uint64_t rv_ram_size;

extern uint64_t rv_rom_base;
extern uint64_t rv_rom_size;

extern uint64_t rv_clint_base;
extern uint64_t rv_clint_size;

extern uint64_t rv_htif_tohost;
