#ifndef __SAIL_FAILURE__
#define __SAIL_FAILURE__

/*
 * Called when some builtin hits an unexpected case, such as overflow
 * when using 64- or 128-bit integers.
 */
void sail_failure(char *message);

/*
 * Called for pattern match failures
 */
void sail_match_failure(char *message);

#endif
