#pragma once

#include<inttypes.h>
#include<stdlib.h>
#include<stdio.h>
#include<stdbool.h>

#ifndef USE_INT128
#include<gmp.h>
#endif

/*
 * Called by the RTS to initialise and clear any library state.
 */
void setup_library(void);
void cleanup_library(void);

/*
 * The Sail compiler expects functions to follow a specific naming
 * convention for allocation, deallocation, and (deep)-copying. These
 * macros implement this naming convention.
 */
#define CREATE(type) create_ ## type
#define RECREATE(type) recreate_ ## type
#define CREATE_OF(type1, type2) create_ ## type1 ## _of_ ## type2
#define RECREATE_OF(type1, type2) recreate_ ## type1 ## _of_ ## type2
#define CONVERT_OF(type1, type2) convert_ ## type1 ## _of_ ## type2
#define COPY(type) copy_ ## type
#define KILL(type) kill_ ## type
#define UNDEFINED(type) undefined_ ## type

#define SAIL_BUILTIN_TYPE(type)\
  void create_ ## type(type *);\
  void recreate_ ## type(type *);\
  void copy_ ## type(type *, const type);\
  void kill_ ## type(type *);

/* ***** Sail unit type ***** */

typedef int unit;

#define UNIT 0

unit UNDEFINED(unit)(const unit);
bool eq_unit(const unit, const unit);
  
/* ***** Sail booleans ***** */

/*
 * and_bool and or_bool are special-cased by the compiler to ensure
 * short-circuiting evaluation.
 */
bool not(const bool);
bool eq_bool(const bool, const bool);
bool UNDEFINED(bool)(const unit);

/* ***** Sail strings ***** */

/*
 * Sail strings are just C strings.
 */
typedef char *sail_string;

SAIL_BUILTIN_TYPE(sail_string);

void dec_str(sail_string *str, const mpz_t n);
void hex_str(sail_string *str, const mpz_t n);

bool eq_string(const sail_string, const sail_string);

/* ***** Sail integers ***** */

typedef int64_t mach_int;

/*
 * Integers can be either stack-allocated as 128-bit integers if
 * __int128 is available, or use GMP arbitrary precision
 * integers. This affects the function signatures, so use a macro to
 * paper over the differences.
 */
#ifndef USE_INT128

typedef mpz_t sail_int;

#define SAIL_INT_FUNCTION(fname, rtype, ...) void fname(rtype*, __VA_ARGS__)

SAIL_BUILTIN_TYPE(sail_int);

void CREATE_OF(sail_int, mach_int)(sail_int *, const mach_int);
void RECREATE_OF(sail_int, mach_int)(sail_int *, const mach_int);

void CREATE_OF(sail_int, sail_string)(sail_int *, const sail_string);
void RECREATE_OF(sail_int, sail_string)(mpz_t *, const sail_string);

mach_int CONVERT_OF(mach_int, sail_int)(const sail_int);
void CONVERT_OF(sail_int, mach_int)(sail_int *, const mach_int);
  
#else

typedef __int128 sail_int;
#define SAIL_INT_FUNCTION(fname, rtype, ...) rtype fname(__VA_ARGS__)

#endif

/*
 * Comparison operators for integers
 */
bool eq_int(const sail_int, const sail_int);

bool lt(const sail_int, const sail_int);
bool gt(const sail_int, const sail_int);
bool lteq(const sail_int, const sail_int);
bool gteq(const sail_int, const sail_int);

/*
 * Left and right shift for integers
 */
SAIL_INT_FUNCTION(shl_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(shr_int, sail_int, const sail_int, const sail_int);

/*
 * undefined_int and undefined_range can't use the UNDEFINED(TYPE)
 * macro, because they're slightly magical. They take extra parameters
 * to ensure that no undefined int can violate any type-guaranteed
 * constraints.
 */
SAIL_INT_FUNCTION(undefined_int, sail_int, const int);
SAIL_INT_FUNCTION(undefined_range, sail_int, const sail_int, const sail_int);

/*
 * Arithmetic operations in integers. We include functions for both
 * truncating towards zero, and rounding towards -infinity (floor) as
 * fdiv/fmod and tdiv/tmod respectively.
 */
SAIL_INT_FUNCTION(add_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tdiv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tmod_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fdiv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fmod_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(max_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(min_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(neg_int, sail_int, const sail_int);
SAIL_INT_FUNCTION(abs_int, sail_int, const sail_int);

SAIL_INT_FUNCTION(pow2, sail_int, const sail_int);

/* ***** Sail bitvectors ***** */

typedef uint64_t mach_bits;

bool eq_bit(const mach_bits a, const mach_bits b);

typedef struct {
  mp_bitcnt_t len;
  mpz_t *bits;
} sail_bits;

SAIL_BUILTIN_TYPE(sail_bits);

void CREATE_OF(sail_bits, mach_bits)(sail_bits *,
				     const mach_bits op,
				     const mach_bits len,
				     const bool direction);

void RECREATE_OF(sail_bits, mach_bits)(sail_bits *,
				       const mach_bits op,
				       const mach_bits len,
				       const bool direction);

mach_bits CONVERT_OF(mach_bits, sail_bits)(const sail_bits);

void UNDEFINED(sail_bits)(sail_bits *, const sail_int len, const mach_bits bit);
mach_bits UNDEFINED(mach_bits)(const unit);

/* 
 * Wrapper around >> operator to avoid UB when shift amount is greater
 * than or equal to 64.
 */
mach_bits safe_rshift(const mach_bits, const mach_bits);

/*
 * Used internally to construct large bitvector literals.
 */
void append_64(sail_bits *rop, const sail_bits op, const mach_bits chunk);

void add_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void sub_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2);

void add_bits_int(sail_bits *rop, const sail_bits op1, const mpz_t op2);
void sub_bits_int(sail_bits *rop, const sail_bits op1, const mpz_t op2);

void zeros(sail_bits *rop, const sail_int op);
void zero_extend(sail_bits *rop, const sail_bits op, const sail_int len);

void length_sail_bits(sail_int *rop, const sail_bits op);

bool eq_bits(const sail_bits op1, const sail_bits op2);

void vector_subrange_sail_bits(sail_bits *rop,
			       const sail_bits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz);

void truncate(sail_bits *rop, const sail_bits op, const sail_int len);

mach_bits bitvector_access(const sail_bits op, const sail_int n_mpz);

void sail_unsigned(sail_int *rop, const sail_bits op);
void sail_signed(sail_int *rop, const sail_bits op);

/* ***** Sail reals ***** */

/* ***** Printing ***** */

/* 
 * Utility function not callable from Sail!
 */
void fprint_bits(const sail_string pre,
		 const sail_bits op,
		 const sail_string post,
		 FILE *stream);

unit print_bits(const sail_string str, const sail_bits op);
unit prerr_bits(const sail_string str, const sail_bits op);

unit print(const sail_string str);
unit print_endline(const sail_string str);

unit prerr(const sail_string str);
unit prerr_endline(const sail_string str);

unit print_int(const sail_string str, const sail_int op);
unit prerr_int(const sail_string str, const sail_int op);
