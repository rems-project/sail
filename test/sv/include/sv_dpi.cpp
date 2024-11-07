#include "svdpi.h"
#include "Vsail_toplevel__Dpi.h"

svBitVecVal sv_dpi_foo(const svLogicVecVal* param0, const svLogicVecVal* param1)
{
  return param0->aval + param1->aval;
}
