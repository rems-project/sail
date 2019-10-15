#ifndef __SAIL_LIB__
#define __SAIL_LIB__

/*
 * Only use libraries here that work with -ffreestanding and -nostdlib
 */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

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
#define EQUAL(type) eq_ ## type

/*
 * This is only needed for types that are not just simple C types that
 * live on the stack, and need some kind of setup and teardown
 * routines, as Sail won't use these otherwise.
 */
#define SAIL_BUILTIN_TYPE(type)\
  void create_ ## type(type *);\
  void recreate_ ## type(type *);\
  void copy_ ## type(type *, const type);\
  void kill_ ## type(type *);

/* ********************************************************************** */
/* Sail unit type                                                         */
/* ********************************************************************** */

typedef int unit;

#define UNIT 0

static inline unit UNDEFINED(unit)(const unit u)
{
     return UNIT;
}

static inline bool EQUAL(unit)(const unit u1, const unit u2)
{
     return true;
}

/* ********************************************************************** */
/* Sail booleans                                                          */
/* ********************************************************************** */

/*
 * and_bool and or_bool are special-cased by the compiler to ensure
 * proper short-circuiting evaluation.
 */

static inline bool not(const bool b)
{
     return !b;
}

static inline bool EQUAL(bool)(const bool a, const bool b)
{
     return a == b;
}

static inline bool UNDEFINED(bool)(const unit u)
{
     return false;
}

/* ********************************************************************** */
/* Sail strings                                                           */
/* ********************************************************************** */

/*
 * Sail strings are just C strings.
 */
typedef char *sail_string;

SAIL_BUILTIN_TYPE(sail_string)

void undefined_string(sail_string *str, const unit u);

bool eq_string(const sail_string, const sail_string);
bool EQUAL(sail_string)(const sail_string, const sail_string);

void concat_str(sail_string *stro, const sail_string str1, const sail_string str2);
bool string_startswith(sail_string s, sail_string prefix);

unit sail_assert(bool, sail_string);

/* ********************************************************************** */
/* Sail integers                                                          */
/* ********************************************************************** */

/* First, we define a type for machine-precision integers, int64_t */

typedef int64_t mach_int;
#define MACH_INT_MAX INT64_MAX
#define MACH_INT_MIN INT64_MIN

static inline bool EQUAL(mach_int)(const mach_int a, const mach_int b)
{
     return a == b;
}

/*
 * For arbitrary precision types, we define a type sail_int. Currently
 * sail_int can either be using GMP arbitrary-precision integers
 * (default) or using __int128 or int64_t which is potentially unsound
 * but MUCH faster. the SAIL_INT_FUNCTION macro allows defining
 * function prototypes that work for either case.
 */
#if defined(SAIL_INT64) || defined(SAIL_INT64)
#ifdef SAIL_INT64
typedef int64_t sail_int;
#define SAIL_INT_MAX INT64_MAX
#define SAIL_INT_MIN INT64_MIN
#else
typedef __int128 sail_int;
#define SAIL_INT_MAX INT128_MAX
#define SAIL_INT_MIN INT128_MIN
#endif
#define SAIL_INT_FUNCTION(fname, ...) sail_int fname(__VA_ARGS__)
#else
typedef mpz_t sail_int;
#define SAIL_INT_FUNCTION(fname, ...) void fname(sail_int*, __VA_ARGS__)
#endif

SAIL_INT_FUNCTION(CREATE_OF(sail_int, mach_int), const mach_int);
SAIL_INT_FUNCTION(CREATE_OF(sail_int, sail_string, const sail_string);
mach_int CREATE_OF(mach_int, sail_int)(const sail_int);

SAIL_INT_FUNCTION(CONVERT_OF(sail_int, mach_int), const mach_int);
SAIL_INT_FUNCTION(CONVERT_OF(sail_int, sail_string), const sail_string);
mach_int CONVERT_OF(mach_int, sail_int)(const sail_int);

/*
 * Comparison operators for integers
 */
bool eq_int(const sail_int, const sail_int);
bool EQUAL(sail_int)(const sail_int, const sail_int);

bool lt(const sail_int, const sail_int);
bool gt(const sail_int, const sail_int);
bool lteq(const sail_int, const sail_int);
bool gteq(const sail_int, const sail_int);

/*
 * Left and right shift for integers
 */
mach_int shl_mach_int(const mach_int, const mach_int);
mach_int shr_mach_int(const mach_int, const mach_int);
SAIL_INT_FUNCTION(shl_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(shr_int, const sail_int, const sail_int);

/*
 * undefined_int and undefined_range can't use the UNDEFINED(TYPE)
 * macro, because they're slightly magical. They take extra parameters
 * to ensure that no undefined integer can violate any type-guaranteed
 * constraints.
 */
SAIL_INT_FUNCTION(undefined_int, const int);
SAIL_INT_FUNCTION(undefined_range, const sail_int, const sail_int);

/*
 * Arithmetic operations in integers. We include functions for both
 * truncating towards zero, and rounding towards -infinity (floor) as
 * fdiv/fmod and tdiv/tmod respectively. Plus euclidian division
 * ediv/emod.
 */
SAIL_INT_FUNCTION(add_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_nat, const sail_int, const sail_int);
SAIL_INT_FUNCTION(mult_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(ediv_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(emod_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tdiv_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tmod_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fdiv_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fmod_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(max_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(min_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(neg_int, const sail_int);
SAIL_INT_FUNCTION(abs_int, const sail_int);
SAIL_INT_FUNCTION(pow_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(pow2, sail_int, const sail_int);

/* ********************************************************************** */
/* Sail bitvectors                                                        */
/* ********************************************************************** */

/*
 * Sail bitvectors are divided into three types:
 * - (f)ixed, statically known bitvectors fbits
 * - (s)mall bitvectors of an unknown width, but guaranteed to be less than 64-bits, sbits
 * - Arbitrarily (l)arge bitvectors of an unknown width, lbits
 *
 * These types form a total order where each can be losslessly
 * converted upwards into the other.
 */

typedef uint64_t fbits;

/*
 * For backwards compatability with older Sail C libraries
 */
typedef uint64_t mach_bits;

typedef struct {
     uint64_t len;
     uint64_t bits;
} sbits;

#ifdef SAIL_BITS64
typedef sbits lbits;
#define SAIL_BITS_FUNCTION(fname, ...) lbits fname(__VA_ARGS__)
#else
typedef struct {
  mp_bitcnt_t len;
  mpz_t *bits;
} lbits;
#define SAIL_BITS_FUNCTION(fname, ...) void fname(lbits*, __VA_ARGS__)
SAIL_BUILTIN_TYPE(lbits);
#endif

SAIL_BITS_FUNCTION(CREATE_OF(lbits, fbits), const fbits, const uint64_t, const bool);
SAIL_BITS_FUNCTION(RECREATE_OF(lbits, fbits), const fbits, const uint64_t, const bool);
SAIL_BITS_FUNCTION(CREATE_OF(lbits, sbits), const fbits, const bool);
SAIL_BITS_FUNCTION(RECREATE_OF(lbits, sbits), const fbits, const bool);

#endif
