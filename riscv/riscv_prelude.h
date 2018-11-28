#pragma once
#include "sail.h"
#include "rts.h"

unit print_string(sail_string prefix, sail_string msg);

unit print_instr(sail_string s);
unit print_reg(sail_string s);
unit print_mem_access(sail_string s);
unit print_platform(sail_string s);
