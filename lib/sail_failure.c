#include "sail_failure.h"

void sail_match_failure(sail_string msg)
{
  fprintf(stderr, "Pattern match failure in %s\n", msg);
  exit(EXIT_FAILURE);
}

unit sail_assert(bool b, sail_string msg)
{
  if (b) return UNIT;
  fprintf(stderr, "Assertion failed: %s\n", msg);
  exit(EXIT_FAILURE);
}
