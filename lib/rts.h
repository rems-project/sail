#pragma once

#include<inttypes.h>
#include<stdlib.h>
#include<stdio.h>

#include"sail.h"

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

/* ***** Memory builtins ***** */

// These memory builtins are intended to match the semantics for the
// __ReadRAM and __WriteRAM functions in ASL.

unit write_ram(const mpz_t addr_size,     // Either 32 or 64
	       const mpz_t data_size_mpz, // Number of bytes
	       const sail_bits hex_ram,       // Currently unused
	       const sail_bits addr_bv,
	       const sail_bits data);

void read_ram(sail_bits *data,
	      const mpz_t addr_size,
	      const mpz_t data_size_mpz,
	      const sail_bits hex_ram,
	      const sail_bits addr_bv);

void load_image(char *);

/* ***** Tracing ***** */

static int64_t g_trace_depth;
static bool g_trace_enabled;

/*
 * Bind these functions in Sail to enable and disable tracing:
 *
 * val "enable_tracing" : unit -> unit
 * val "disable_tracing" : unit -> unit
 *
 * Compile with sail -c -c_trace.
 */
unit enable_tracing(const unit);
unit disable_tracing(const unit);

/*
 * Tracing is implemented by void trace_TYPE functions, each of which
 * takes the Sail value to print as the first argument, and prints it
 * directly to stderr with no linebreaks.
 *
 * For types that don't have printing function we have trace_unknown,
 * which simply prints '?'. trace_argsep, trace_argend, and
 * trace_retend are used for formatting function arguments. They won't
 * overlap with user defined types because the type names used for
 * TYPE are zencoded. trace_start(NAME) and trace_end() are called
 * before printing the function arguments and return value
 * respectively.
*/
void trace_sail_int(const sail_int);
void trace_bool(const bool);
  
void trace_unknown(void);
void trace_argsep(void);
void trace_argend(void);
void trace_retend(void);
void trace_start(char *);
void trace_end(void);

static uint64_t g_elf_entry;

/*
 * setup_rts and cleanup_rts are responsible for calling setup_library
 * and cleanup_library in sail.h.
 */
void setup_rts(void);
void cleanup_rts(void);
