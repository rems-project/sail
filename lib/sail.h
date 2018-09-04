#pragma once

#include<inttypes.h>
#include<stdlib.h>
#include<stdio.h>
#include<stdbool.h>

#ifndef USE_INT128
#include<gmp.h>
#endif

#include<time.h>

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
#define EQUAL(type) eq_ ## type

#define SAIL_BUILTIN_TYPE(type)\
  void create_ ## type(type *);\
  void recreate_ ## type(type *);\
  void copy_ ## type(type *, const type);\
  void kill_ ## type(type *);

/* ***** Sail unit type ***** */

typedef int unit;

#define UNIT 0

unit UNDEFINED(unit)(const unit);
bool EQUAL(unit)(const unit, const unit);

unit skip(const unit);

/* ***** Sail booleans ***** */

/*
 * and_bool and or_bool are special-cased by the compiler to ensure
 * short-circuiting evaluation.
 */
bool not(const bool);
bool EQUAL(bool)(const bool, const bool);
bool UNDEFINED(bool)(const unit);

/* ***** Sail strings ***** */

/*
 * Sail strings are just C strings.
 */
typedef char *sail_string;

SAIL_BUILTIN_TYPE(sail_string);

void dec_str(sail_string *str, const mpz_t n);
void hex_str(sail_string *str, const mpz_t n);

void undefined_string(sail_string *str, const unit u);

bool eq_string(const sail_string, const sail_string);
bool EQUAL(sail_string)(const sail_string, const sail_string);

void concat_str(sail_string *stro, const sail_string str1, const sail_string str2);
bool string_startswith(sail_string s, sail_string prefix);

/* ***** Sail integers ***** */

typedef int64_t mach_int;

bool EQUAL(mach_int)(const mach_int, const mach_int);

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

mach_int CREATE_OF(mach_int, sail_int)(const sail_int);

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
bool EQUAL(sail_int)(const sail_int, const sail_int);

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
SAIL_INT_FUNCTION(sub_nat, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(mult_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tdiv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tmod_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fdiv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fmod_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(max_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(min_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(neg_int, sail_int, const sail_int);
SAIL_INT_FUNCTION(abs_int, sail_int, const sail_int);

SAIL_INT_FUNCTION(pow_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(pow2, sail_int, const sail_int);

/* ***** Sail bitvectors ***** */

typedef uint64_t mach_bits;

bool eq_bit(const mach_bits a, const mach_bits b);

bool EQUAL(mach_bits)(const mach_bits, const mach_bits);

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

mach_bits CONVERT_OF(mach_bits, sail_bits)(const sail_bits, const bool);
void CONVERT_OF(sail_bits, mach_bits)(sail_bits *, const mach_bits, const uint64_t, const bool);

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

void and_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void or_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void xor_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void not_bits(sail_bits *rop, const sail_bits op);

void mults_vec(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void mult_vec(sail_bits *rop, const sail_bits op1, const sail_bits op2);

void zeros(sail_bits *rop, const sail_int op);

void zero_extend(sail_bits *rop, const sail_bits op, const sail_int len);
void sign_extend(sail_bits *rop, const sail_bits op, const sail_int len);

void length_sail_bits(sail_int *rop, const sail_bits op);

bool eq_bits(const sail_bits op1, const sail_bits op2);
bool EQUAL(sail_bits)(const sail_bits op1, const sail_bits op2);
bool neq_bits(const sail_bits op1, const sail_bits op2);

void vector_subrange_sail_bits(sail_bits *rop,
			       const sail_bits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz);

void sail_truncate(sail_bits *rop, const sail_bits op, const sail_int len);

mach_bits bitvector_access(const sail_bits op, const sail_int n_mpz);

void sail_unsigned(sail_int *rop, const sail_bits op);
void sail_signed(sail_int *rop, const sail_bits op);

void append(sail_bits *rop, const sail_bits op1, const sail_bits op2);

void replicate_bits(sail_bits *rop, const sail_bits op1, const sail_int op2);
mach_bits fast_replicate_bits(const mach_bits shift, const mach_bits v, const mach_int times);

void get_slice_int(sail_bits *rop, const sail_int len_mpz, const sail_int n, const sail_int start_mpz);

void set_slice_int(sail_int *rop,
		   const sail_int len_mpz,
		   const sail_int n,
		   const sail_int start_mpz,
		   const sail_bits slice);

void vector_update_subrange_sail_bits(sail_bits *rop,
				      const sail_bits op,
				      const sail_int n_mpz,
				      const sail_int m_mpz,
				      const sail_bits slice);

void slice(sail_bits *rop, const sail_bits op, const sail_int start_mpz, const sail_int len_mpz);

void set_slice(sail_bits *rop,
	       const sail_int len_mpz,
	       const sail_int slen_mpz,
	       const sail_bits op,
	       const sail_int start_mpz,
	       const sail_bits slice);


void shift_bits_left(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void shift_bits_right(sail_bits *rop, const sail_bits op1, const sail_bits op2);
void shift_bits_right_arith(sail_bits *rop, const sail_bits op1, const sail_bits op2);

void shiftl(sail_bits *rop, const sail_bits op1, const sail_int op2);
void shiftr(sail_bits *rop, const sail_bits op1, const sail_int op2);

void reverse_endianness(sail_bits*, sail_bits);

/* ***** Sail reals ***** */

typedef mpq_t real;

SAIL_BUILTIN_TYPE(real);

void CREATE_OF(real, sail_string)(real *rop, const sail_string op);

void UNDEFINED(real)(real *rop, unit u);

void neg_real(real *rop, const real op);

void mult_real(real *rop, const real op1, const real op2);
void sub_real(real *rop, const real op1, const real op2);
void add_real(real *rop, const real op1, const real op2);
void div_real(real *rop, const real op1, const real op2);

void sqrt_real(real *rop, const real op);
void abs_real(real *rop, const real op);

void round_up(sail_int *rop, const real op);
void round_down(sail_int *rop, const real op);

void to_real(real *rop, const sail_int op);

bool EQUAL(real)(const real op1, const real op2);

bool lt_real(const real op1, const real op2);
bool gt_real(const real op1, const real op2);
bool lteq_real(const real op1, const real op2);
bool gteq_real(const real op1, const real op2);

void real_power(real *rop, const real base, const sail_int exp);

unit print_real(const sail_string, const real);
unit prerr_real(const sail_string, const real);

void random_real(real *rop, unit);

/* ***** String utilities ***** */

void string_length(sail_int *len, sail_string s);
void string_drop(sail_string *dst, sail_string s, sail_int len);

/* ***** Printing ***** */

void string_of_int(sail_string *str, const sail_int i);
void string_of_sail_bits(sail_string *str, const sail_bits op);
void string_of_mach_bits(sail_string *str, const mach_bits op);

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

unit sail_putchar(const sail_int op);

/* ***** Misc ***** */

void get_time_ns(sail_int*, const unit);
