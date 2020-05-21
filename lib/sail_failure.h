#ifndef SAIL_FAILURE_H
#define SAIL_FAILURE_H

#include "sail.h"

/*
 * This function should be called whenever a pattern match failure
 * occurs. Pattern match failures are always fatal.
 */
void sail_match_failure(sail_string msg);

/*
 * sail_assert implements the assert construct in Sail. If any
 * assertion fails we immediately exit the model.
 */
unit sail_assert(bool b, sail_string msg);

#endif
