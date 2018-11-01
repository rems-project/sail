#pragma once

#include<string.h>
#include<stdbool.h>
#include<stdint.h>

void load_elf(char *filename, bool *is32bit_p, uint64_t *entry);
int  lookup_sym(const char *filename, const char *symname, uint64_t *value);
