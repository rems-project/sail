#include "riscv_prelude.h"

unit print_string(sail_string prefix, sail_string msg)
{
  printf("%s%s\n", prefix, msg);
  return UNIT;
}

