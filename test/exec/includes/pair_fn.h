#ifndef PAIR_HEADER
#define PAIR_HEADER

#include <inttypes.h>
#include "sail.h"
#include "../cabbrev.h"

#ifdef __cplusplus
extern "C" {
#endif

my_pair_in_c mk_pair(unit u)
{
  my_pair_in_c p;
  p.first = 0;
  p.second = 3;
  return p;
}

#ifdef __cplusplus
}
#endif

#endif
