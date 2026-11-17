/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/****************************************************************************/

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include<assert.h>
#include<inttypes.h>
#include<stdbool.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<time.h>

#include"sail.h"

#ifdef __cplusplus
extern "C" {
#endif

// zero bits from high index, same semantics as bzhi intrinsic
uint64_t bzhi_u64(uint64_t bits, uint64_t len)
{
  return bits & (UINT64_MAX >> (64 - len));
}

/* Count leading or trailing zeros of a non-zero value, and byte swap. */
static inline int sail_clz64(uint64_t x)
{
#ifdef SAIL_HAVE_BUILTINS
  return __builtin_clzll(x);
#else
  int n = 0;
  if (!(x >> 32)) n += 32, x <<= 32;
  if (!(x >> 48)) n += 16, x <<= 16;
  if (!(x >> 56)) n += 8, x <<= 8;
  if (!(x >> 60)) n += 4, x <<= 4;
  if (!(x >> 62)) n += 2, x <<= 2;
  if (!(x >> 63)) n += 1;
  return n;
#endif
}

static inline int sail_ctz64(uint64_t x)
{
#ifdef SAIL_HAVE_BUILTINS
  return __builtin_ctzll(x);
#else
  int n = 0;
  if (!(x & 0xffffffff)) n += 32, x >>= 32;
  if (!(x & 0xffff)) n += 16, x >>= 16;
  if (!(x & 0xff)) n += 8, x >>= 8;
  if (!(x & 0xf)) n += 4, x >>= 4;
  if (!(x & 0x3)) n += 2, x >>= 2;
  if (!(x & 0x1)) n += 1;
  return n;
#endif
}

static inline uint64_t sail_bswap64(uint64_t x)
{
#ifdef SAIL_HAVE_BUILTINS
  return __builtin_bswap64(x);
#else
  x = ((x & UINT64_C(0x00ff00ff00ff00ff)) << 8) | ((x >> 8) & UINT64_C(0x00ff00ff00ff00ff));
  x = ((x & UINT64_C(0x0000ffff0000ffff)) << 16) | ((x >> 16) & UINT64_C(0x0000ffff0000ffff));
  return (x << 32) | (x >> 32);
#endif
}

/*
 * Temporary mpzs for use in functions below. To avoid conflicts, only
 * use in functions that do not call other functions in this file.
 */
static mpz_t sail_lib_tmp1, sail_lib_tmp2, sail_lib_tmp3;
static real sail_lib_tmp_real;

static void sail_mpz_pool_clear(void);

#define FLOAT_PRECISION 255

void setup_library(void)
{
  srand(0x0);
  mpz_init(sail_lib_tmp1);
  mpz_init(sail_lib_tmp2);
  mpz_init(sail_lib_tmp3);
  mpq_init(sail_lib_tmp_real);
  mpf_set_default_prec(FLOAT_PRECISION);
}

void cleanup_library(void)
{
  mpz_clear(sail_lib_tmp1);
  mpz_clear(sail_lib_tmp2);
  mpz_clear(sail_lib_tmp3);
  mpq_clear(sail_lib_tmp_real);
  sail_mpz_pool_clear();
}

bool EQUAL(unit)(const unit a, const unit b)
{
  return true;
}

unit UNDEFINED(unit)(const unit u)
{
  return UNIT;
}

unit skip(const unit u)
{
  return UNIT;
}

/* ***** Sail bit type ***** */

bool eq_bit(const fbits a, const fbits b)
{
  return a == b;
}

/* ***** Sail booleans ***** */

bool EQUAL(bool)(const bool a, const bool b) {
  return a == b;
}

bool UNDEFINED(bool)(const unit u) {
  return false;
}

/* ***** Sail strings ***** */

void CREATE(sail_string)(sail_string *str)
{
  char *istr = (char *) sail_malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void RECREATE(sail_string)(sail_string *str)
{
  sail_free(*str);
  char *istr = (char *) sail_malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void COPY(sail_string)(sail_string *str1, const_sail_string str2)
{
  size_t len = strlen(str2);
  *str1 = (sail_string)realloc(*str1, len + 1);
  *str1 = strcpy(*str1, str2);
}

void KILL(sail_string)(sail_string *str)
{
  sail_free(*str);
}

bool eq_string(const_sail_string str1, const_sail_string str2)
{
  return strcmp(str1, str2) == 0;
}

bool EQUAL(sail_string)(const_sail_string str1, const_sail_string str2)
{
  return strcmp(str1, str2) == 0;
}

void undefined_string(sail_string *str, const unit u) {}

void concat_str(sail_string *stro, const_sail_string str1, const_sail_string str2)
{
  sail_string in1;
  sail_string in2;
  size_t in1_len = strlen(str1);
  size_t in2_len = strlen(str2);
  bool in1_free = false;
  bool in2_free = false;

  if (*stro == str1) {
    in1 = (sail_string)sail_malloc(in1_len + 1);
    strcpy(in1, str1);
    in1_free = true;
  } else {
    in1 = (sail_string)str1;
  }

  if (*stro == str2) {
    in2 = (sail_string)sail_malloc(in2_len + 1);
    strcpy(in2, str2);
    in2_free = true;
  } else {
    in2 = (sail_string)str2;
  }

  *stro = (sail_string)realloc(*stro, in1_len + in2_len + 1);
  (*stro)[0] = '\0';
  strcat(*stro, in1);
  strcat(*stro, in2);

  if (in1_free) sail_free(in1);
  if (in2_free) sail_free(in2);
}

bool string_startswith(const_sail_string s, const_sail_string prefix)
{
  return strstr(s, prefix) == s;
}

void string_length(sail_int *len, const_sail_string s)
{
  sail_int_set_small(len, (int64_t)strlen(s));
}

void string_drop(sail_string *dst, const_sail_string s, sail_int ns)
{
  size_t len = strlen(s);
  mach_int n = CREATE_OF(mach_int, sail_int)(ns);
  if (len >= n) {
    *dst = (sail_string)realloc(*dst, (len - n) + 1);
    memcpy(*dst, s + n, len - n);
    (*dst)[len - n] = '\0';
  } else {
    *dst = (sail_string)realloc(*dst, 1);
    **dst = '\0';
  }
}

void string_take(sail_string *dst, const_sail_string s, sail_int ns)
{
  size_t len = strlen(s);
  mach_int n = CREATE_OF(mach_int, sail_int)(ns);
  mach_int to_copy;
  if (len <= n) {
    to_copy = len;
  } else {
    to_copy = n;
  }
  *dst = (sail_string)realloc(*dst, to_copy + 1);
  memcpy(*dst, s, to_copy);
  (*dst)[to_copy] = '\0';
}

/* ***** Sail integers ***** */

bool EQUAL(mach_int)(const mach_int op1, const mach_int op2)
{
  return op1 == op2;
}

/*
 * A pool of initialized mpz_t values for the big field of sail_int
 * and lbits. Values switch between small and big often, so this
 * keeps malloc and mpz_init off that path.
 */
#define SAIL_MPZ_POOL_SIZE 128
static mpz_ptr sail_mpz_pool[SAIL_MPZ_POOL_SIZE];
static int sail_mpz_pool_count = 0;

mpz_ptr sail_mpz_alloc(void)
{
  if (sail_mpz_pool_count > 0) {
    return sail_mpz_pool[--sail_mpz_pool_count];
  }
  mpz_ptr z = (mpz_ptr)sail_malloc(sizeof(mpz_t));
  mpz_init(z);
  return z;
}

void sail_mpz_release(mpz_ptr z)
{
  if (sail_mpz_pool_count < SAIL_MPZ_POOL_SIZE) {
    sail_mpz_pool[sail_mpz_pool_count++] = z;
  } else {
    mpz_clear(z);
    sail_free(z);
  }
}

static void sail_mpz_pool_clear(void)
{
  while (sail_mpz_pool_count > 0) {
    mpz_ptr z = sail_mpz_pool[--sail_mpz_pool_count];
    mpz_clear(z);
    sail_free(z);
  }
}

static inline bool mpz_fits_int64(const mpz_t op)
{
  size_t n = mpz_size(op);
  if (n == 0) return true;
  if (n > 1) return false;
  uint64_t l = mpz_getlimbn(op, 0);
  return mpz_sgn(op) > 0 ? l <= (uint64_t)INT64_MAX : l <= (uint64_t)INT64_MAX + 1;
}

/* Only valid if mpz_fits_int64(op). */
static inline int64_t mpz_get_int64(const mpz_t op)
{
  if (mpz_size(op) == 0) return 0;
  uint64_t l = mpz_getlimbn(op, 0);
  return mpz_sgn(op) > 0 ? (int64_t)l : (int64_t)(-l);
}

static inline void mpz_set_int64(mpz_t rop, const int64_t op)
{
  mpz_set_si(rop, op);
}

void sail_int_set_mpz(sail_int *rop, const mpz_t op)
{
  if (mpz_fits_int64(op)) {
    sail_int_set_small(rop, mpz_get_int64(op));
  } else {
    if (rop->big == NULL) rop->big = sail_mpz_alloc();
    mpz_set(rop->big, op);
  }
}

/*
 * Set rop from a scratch mpz_t, and leave unspecified data in op.
 * This avoids a copy when the result is big.
 */
static void sail_int_take_mpz(sail_int *rop, mpz_t op)
{
  if (mpz_fits_int64(op)) {
    sail_int_set_small(rop, mpz_get_int64(op));
  } else {
    if (rop->big == NULL) rop->big = sail_mpz_alloc();
    mpz_swap(rop->big, op);
  }
}

void sail_int_get_mpz(mpz_t rop, const sail_int op)
{
  if (op.big == NULL) {
    mpz_set_int64(rop, op.val);
  } else {
    mpz_set(rop, op.big);
  }
}

void sail_int_copy_slow(sail_int *rop, const sail_int op)
{
  if (rop->big == op.big) return;
  if (rop->big == NULL) rop->big = sail_mpz_alloc();
  mpz_set(rop->big, op.big);
}

int sail_int_cmp_slow(const sail_int op1, const sail_int op2)
{
  sail_mpz_view v1, v2;
  int c = mpz_cmp(sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  return (c > 0) - (c < 0);
}

void CREATE_OF(sail_int, sail_string)(sail_int *rop, const_sail_string str)
{
  CREATE(sail_int)(rop);
  CONVERT_OF(sail_int, sail_string)(rop, str);
}

void CONVERT_OF(sail_int, sail_string)(sail_int *rop, const_sail_string str)
{
  mpz_set_str(sail_lib_tmp1, str, 10);
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void RECREATE_OF(sail_int, sail_string)(sail_int *rop, const_sail_string str)
{
  CONVERT_OF(sail_int, sail_string)(rop, str);
}

void dec_str(sail_string *str, const sail_int n)
{
  sail_mpz_view v;
  sail_free(*str);
  gmp_asprintf(str, "%Zd", sail_int_view(&v, n));
}

static void hex_str_fmt(sail_string *str, const sail_int n, const char *neg_fmt, const char *pos_fmt)
{
  sail_mpz_view v;
  mpz_srcptr z = sail_int_view(&v, n);
  sail_free(*str);

  if (mpz_sgn(z) < 0) {
    mpz_t abs;
    mpz_init(abs);
    mpz_abs(abs, z);
    gmp_asprintf(str, neg_fmt, abs);
    mpz_clear(abs);
  } else {
    gmp_asprintf(str, pos_fmt, z);
  }
}

void hex_str(sail_string *str, const sail_int n)
{
  hex_str_fmt(str, n, "-0x%Zx", "0x%Zx");
}

void hex_str_upper(sail_string *str, const sail_int n)
{
  hex_str_fmt(str, n, "-0x%ZX", "0x%ZX");
}

void shl_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  uint64_t shift = sail_int_get_ui(op2);
  if (op1.big == NULL && shift < 63) {
    int64_t r = (int64_t)((uint64_t)op1.val << shift);
    if ((r >> shift) == op1.val) {
      sail_int_set_small(rop, r);
      return;
    }
  }
  sail_mpz_view v;
  mpz_mul_2exp(sail_lib_tmp1, sail_int_view(&v, op1), shift);
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

mach_int shl_mach_int(const mach_int op1, const mach_int op2)
{
  return op1 << op2;
}

void shr_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  uint64_t shift = sail_int_get_ui(op2);
  if (op1.big == NULL) {
    /* Floor division by 2^shift, which is an arithmetic shift. */
    sail_int_set_small(rop, shift >= 64 ? (op1.val < 0 ? -1 : 0) : op1.val >> shift);
    return;
  }
  mpz_fdiv_q_2exp(sail_lib_tmp1, op1.big, shift);
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

mach_int shr_mach_int(const mach_int op1, const mach_int op2)
{
  return op1 >> op2;
}

void undefined_int(sail_int *rop, const int n)
{
  /* The value is (uint64_t)n, so a negative n gives a big value. */
  uint64_t u = (uint64_t)n;
  if (u <= (uint64_t)INT64_MAX) {
    sail_int_set_small(rop, (int64_t)u);
  } else {
    mpz_set_ui(sail_lib_tmp1, u);
    sail_int_take_mpz(rop, sail_lib_tmp1);
  }
}

void undefined_nat(sail_int *rop, const unit u)
{
  sail_int_set_small(rop, 0);
}

void undefined_range(sail_int *rop, const sail_int l, const sail_int u)
{
  COPY(sail_int)(rop, l);
}

void add_int_slow(sail_int *rop, const sail_int op1, const sail_int op2)
{
  sail_mpz_view v1, v2;
  mpz_add(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void sub_int_slow(sail_int *rop, const sail_int op1, const sail_int op2)
{
  sail_mpz_view v1, v2;
  mpz_sub(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void mult_int_slow(sail_int *rop, const sail_int op1, const sail_int op2)
{
  sail_mpz_view v1, v2;
  mpz_mul(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

/*
 * Small fast paths for division. They are not used for a zero divisor
 * (to keep the GMP behaviour) or for INT64_MIN / -1 (which overflows).
 */
static inline bool sail_div_fast(const sail_int op1, const sail_int op2)
{
  return op1.big == NULL && op2.big == NULL && op2.val != 0 && !(op1.val == INT64_MIN && op2.val == -1);
}

void ediv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (sail_div_fast(op1, op2)) {
    int64_t q = op1.val / op2.val;
    int64_t r = op1.val % op2.val;
    if (r < 0) q = op2.val > 0 ? q - 1 : q + 1;
    sail_int_set_small(rop, q);
    return;
  }
  /* GMP doesn't have Euclidean division but we can emulate it using
     flooring and ceiling division. */
  sail_mpz_view v1, v2;
  mpz_srcptr a = sail_int_view(&v1, op1), b = sail_int_view(&v2, op2);
  if (mpz_sgn(b) >= 0) {
    mpz_fdiv_q(sail_lib_tmp1, a, b);
  } else {
    mpz_cdiv_q(sail_lib_tmp1, a, b);
  }
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void emod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (sail_div_fast(op1, op2)) {
    int64_t r = op1.val % op2.val;
    if (r < 0) r = op2.val > 0 ? r + op2.val : r - op2.val;
    sail_int_set_small(rop, r);
    return;
  }
  /* The documentation isn't that explicit but I think this is
     Euclidean mod. */
  sail_mpz_view v1, v2;
  mpz_mod(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void tdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (sail_div_fast(op1, op2)) {
    sail_int_set_small(rop, op1.val / op2.val);
    return;
  }
  sail_mpz_view v1, v2;
  mpz_tdiv_q(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void tmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (sail_div_fast(op1, op2)) {
    sail_int_set_small(rop, op1.val % op2.val);
    return;
  }
  sail_mpz_view v1, v2;
  mpz_tdiv_r(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void fdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (sail_div_fast(op1, op2)) {
    int64_t q = op1.val / op2.val;
    int64_t r = op1.val % op2.val;
    if (r != 0 && ((r < 0) != (op2.val < 0))) q--;
    sail_int_set_small(rop, q);
    return;
  }
  sail_mpz_view v1, v2;
  mpz_fdiv_q(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void fmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (sail_div_fast(op1, op2)) {
    int64_t r = op1.val % op2.val;
    if (r != 0 && ((r < 0) != (op2.val < 0))) r += op2.val;
    sail_int_set_small(rop, r);
    return;
  }
  sail_mpz_view v1, v2;
  mpz_fdiv_r(sail_lib_tmp1, sail_int_view(&v1, op1), sail_int_view(&v2, op2));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void neg_int(sail_int *rop, const sail_int op)
{
  if (op.big == NULL && op.val != INT64_MIN) {
    sail_int_set_small(rop, -op.val);
    return;
  }
  sail_mpz_view v;
  mpz_neg(sail_lib_tmp1, sail_int_view(&v, op));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void abs_int(sail_int *rop, const sail_int op)
{
  if (op.big == NULL && op.val != INT64_MIN) {
    sail_int_set_small(rop, op.val < 0 ? -op.val : op.val);
    return;
  }
  sail_mpz_view v;
  mpz_abs(sail_lib_tmp1, sail_int_view(&v, op));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void pow_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  uint64_t n = sail_int_get_ui(op2);
  sail_mpz_view v;
  mpz_pow_ui(sail_lib_tmp1, sail_int_view(&v, op1), n);
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void pow2(sail_int *rop, const sail_int exp)
{
  /* Assume exponent is never more than 2^64... */
  uint64_t exp_ui = sail_int_get_ui(exp);
  if (exp_ui < 63) {
    sail_int_set_small(rop, INT64_C(1) << exp_ui);
    return;
  }
  mpz_set_ui(sail_lib_tmp1, 0);
  mpz_setbit(sail_lib_tmp1, exp_ui);
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

/* ***** Sail bitvectors ***** */

bool EQUAL(fbits)(const fbits op1, const fbits op2)
{
  return op1 == op2;
}

bool EQUAL(ref_fbits)(const fbits *op1, const fbits *op2)
{
  return *op1 == *op2;
}

/*
 * Set rop to a value with len > 64, and return the mpz_t to write the
 * value into. The mpz_t has unspecified contents.
 */
static inline mpz_ptr sail_lbits_make_big(lbits *rop, const uint64_t len)
{
  if (rop->len <= 64) rop->big = sail_mpz_alloc();
  rop->len = len;
  return rop->big;
}

void sail_lbits_set_mpz(lbits *rop, const mp_bitcnt_t len, const mpz_t op)
{
  if (len <= 64) {
    /* The low 64 bits of the two's complement value. */
    uint64_t w = mpz_getlimbn(op, 0);
    if (mpz_sgn(op) < 0) w = -w;
    sail_lbits_set_small(rop, len, w & sail_mask64(len));
  } else {
    mpz_ptr z = sail_lbits_make_big(rop, len);
    mpz_fdiv_r_2exp(z, op, len);
  }
}

/*
 * Set rop to the low len bits of a scratch mpz_t, and leave unspecified
 * data in op. This avoids a copy when the result is big.
 */
static void sail_lbits_take_mpz(lbits *rop, const mp_bitcnt_t len, mpz_t op)
{
  if (len <= 64) {
    sail_lbits_set_mpz(rop, len, op);
  } else {
    mpz_fdiv_r_2exp(op, op, len);
    mpz_ptr z = sail_lbits_make_big(rop, len);
    mpz_swap(z, op);
  }
}

void sail_lbits_get_mpz(mpz_t rop, const lbits op)
{
  if (op.len <= 64) {
    mpz_set_ui(rop, op.word);
  } else {
    mpz_set(rop, op.big);
  }
}

void sail_lbits_set_u64_slow(lbits *rop, const uint64_t len, const uint64_t op)
{
  mpz_ptr z = sail_lbits_make_big(rop, len);
  mpz_set_ui(z, op);
}

void sail_lbits_copy_slow(lbits *rop, const lbits op)
{
  if (rop->len > 64 && rop->big == op.big) return;
  mpz_ptr z = sail_lbits_make_big(rop, op.len);
  mpz_set(z, op.big);
}

void UNDEFINED(lbits)(lbits *rop, const sail_int len)
{
  zeros(rop, len);
}

fbits UNDEFINED(fbits)(const unit u) { return 0; }

sbits undefined_sbits(void)
{
  sbits rop;
  rop.bits = UINT64_C(0);
  rop.len = UINT64_C(0);
  return rop;
}

fbits safe_rshift(const fbits x, const fbits n)
{
  if (n >= 64) {
    return 0ul;
  } else {
    return x >> n;
  }
}

void normalize_lbits(lbits *rop)
{
  if (rop->len <= 64) {
    rop->word &= sail_mask64(rop->len);
  } else {
    mpz_fdiv_r_2exp(rop->big, rop->big, rop->len);
  }
}

void append_64(lbits *rop, const lbits op, const fbits chunk)
{
  uint64_t len = rop->len + 64ul;
  sail_mpz_view v;
  mpz_mul_2exp(sail_lib_tmp1, sail_lbits_view(&v, op), 64ul);
  mpz_add_ui(sail_lib_tmp1, sail_lib_tmp1, chunk);
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
}

void add_bits(lbits *rop, const lbits op1, const lbits op2)
{
  if (op1.len <= 64 && op2.len <= 64) {
    sail_lbits_set_small(rop, op1.len, (op1.word + op2.word) & sail_mask64(op1.len));
    return;
  }
  sail_mpz_view v1, v2;
  mpz_add(sail_lib_tmp1, sail_lbits_view(&v1, op1), sail_lbits_view(&v2, op2));
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void sub_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  if (op1.len <= 64) {
    sail_lbits_set_small(rop, op1.len, (op1.word - op2.word) & sail_mask64(op1.len));
    return;
  }
  sail_mpz_view v1, v2;
  mpz_sub(sail_lib_tmp1, sail_lbits_view(&v1, op1), sail_lbits_view(&v2, op2));
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void add_bits_int(lbits *rop, const lbits op1, const sail_int op2)
{
  if (op1.len <= 64 && op2.big == NULL) {
    sail_lbits_set_small(rop, op1.len, (op1.word + (uint64_t)op2.val) & sail_mask64(op1.len));
    return;
  }
  sail_mpz_view v1, v2;
  mpz_add(sail_lib_tmp1, sail_lbits_view(&v1, op1), sail_int_view(&v2, op2));
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void sub_bits_int(lbits *rop, const lbits op1, const sail_int op2)
{
  if (op1.len <= 64 && op2.big == NULL) {
    sail_lbits_set_small(rop, op1.len, (op1.word - (uint64_t)op2.val) & sail_mask64(op1.len));
    return;
  }
  sail_mpz_view v1, v2;
  mpz_sub(sail_lib_tmp1, sail_lbits_view(&v1, op1), sail_int_view(&v2, op2));
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void and_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  if (op1.len <= 64) {
    sail_lbits_set_small(rop, op1.len, op1.word & op2.word);
    return;
  }
  mpz_and(sail_lib_tmp1, op1.big, op2.big);
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void or_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  if (op1.len <= 64) {
    sail_lbits_set_small(rop, op1.len, op1.word | op2.word);
    return;
  }
  mpz_ior(sail_lib_tmp1, op1.big, op2.big);
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void xor_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  if (op1.len <= 64) {
    sail_lbits_set_small(rop, op1.len, op1.word ^ op2.word);
    return;
  }
  mpz_xor(sail_lib_tmp1, op1.big, op2.big);
  sail_lbits_take_mpz(rop, op1.len, sail_lib_tmp1);
}

void not_bits(lbits *rop, const lbits op)
{
  if (op.len <= 64) {
    sail_lbits_set_small(rop, op.len, ~op.word & sail_mask64(op.len));
    return;
  }
  /* ~x mod 2^len is (2^len - 1) - x. */
  mpz_set_ui(sail_lib_tmp1, 0);
  mpz_setbit(sail_lib_tmp1, op.len);
  mpz_sub_ui(sail_lib_tmp1, sail_lib_tmp1, 1);
  mpz_sub(sail_lib_tmp1, sail_lib_tmp1, op.big);
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

/* The signed value of bits, as an mpz_t. */
static void sail_lbits_signed_mpz(mpz_t rop, const lbits op)
{
  sail_lbits_get_mpz(rop, op);
  if (op.len > 0 && mpz_tstbit(rop, op.len - 1)) {
    mpz_set_ui(sail_lib_tmp3, 0);
    mpz_setbit(sail_lib_tmp3, op.len);
    mpz_sub(rop, rop, sail_lib_tmp3);
  }
}

void mults_vec(lbits *rop, const lbits op1, const lbits op2)
{
  uint64_t len = op1.len * 2;
  if (len <= 64 && op1.len > 0) {
    /* Sign extend each operand to 64 bits; the product fits in len bits. */
    unsigned sh = 64 - op1.len;
    int64_t a = (int64_t)(op1.word << sh) >> sh;
    int64_t b = (int64_t)(op2.word << sh) >> sh;
    sail_lbits_set_small(rop, len, (uint64_t)(a * b) & sail_mask64(len));
    return;
  }
  mpz_t op1_int, op2_int;
  mpz_init(op1_int);
  mpz_init(op2_int);
  sail_lbits_signed_mpz(op1_int, op1);
  sail_lbits_signed_mpz(op2_int, op2);
  mpz_mul(sail_lib_tmp1, op1_int, op2_int);
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
  mpz_clear(op1_int);
  mpz_clear(op2_int);
}

void mult_vec(lbits *rop, const lbits op1, const lbits op2)
{
  uint64_t len = op1.len * 2;
  if (len <= 64) {
    sail_lbits_set_small(rop, len, (op1.word * op2.word) & sail_mask64(len));
    return;
  }
  sail_mpz_view v1, v2;
  mpz_mul(sail_lib_tmp1, sail_lbits_view(&v1, op1), sail_lbits_view(&v2, op2));
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
}

void zeros(lbits *rop, const sail_int op)
{
  uint64_t len = sail_int_get_ui(op);
  if (len <= 64) {
    sail_lbits_set_small(rop, len, 0);
  } else {
    mpz_set_ui(sail_lbits_make_big(rop, len), 0);
  }
}

void zero_extend(lbits *rop, const lbits op, const sail_int len)
{
  uint64_t rlen = sail_int_get_ui(len);
  assert(op.len <= rlen);
  if (rlen <= 64) {
    sail_lbits_set_small(rop, rlen, op.word);
  } else if (op.len <= 64) {
    mpz_set_ui(sail_lbits_make_big(rop, rlen), op.word);
  } else if (rop->len > 64 && rop->big == op.big) {
    rop->len = rlen;
  } else {
    mpz_set(sail_lbits_make_big(rop, rlen), op.big);
  }
}

fbits fast_zero_extend(const sbits op, const uint64_t n)
{
  return op.bits;
}

void sign_extend(lbits *rop, const lbits op, const sail_int len)
{
  uint64_t rlen = sail_int_get_ui(len);
  assert(op.len <= rlen);
  if (rlen <= 64) {
    uint64_t w = op.word;
    if (op.len > 0 && op.len < 64 && (w >> (op.len - 1)) & 1) {
      w |= sail_mask64(rlen) & ~sail_mask64(op.len);
    }
    sail_lbits_set_small(rop, rlen, w);
    return;
  }
  sail_lbits_signed_mpz(sail_lib_tmp1, op);
  sail_lbits_take_mpz(rop, rlen, sail_lib_tmp1);
}

fbits fast_sign_extend(const fbits op, const uint64_t n, const uint64_t m)
{
  uint64_t rop = op;
  if (op & (UINT64_C(1) << (n - 1))) {
    for (uint64_t i = m - 1; i >= n; i--) {
      rop = rop | (UINT64_C(1) << i);
    }
    return rop;
  } else {
    return rop;
  }
}

fbits fast_sign_extend2(const sbits op, const uint64_t m)
{
  uint64_t rop = op.bits;
  if (op.bits & (UINT64_C(1) << (op.len - 1))) {
    for (uint64_t i = m - 1; i >= op.len; i--) {
      rop = rop | (UINT64_C(1) << i);
    }
    return rop;
  } else {
    return rop;
  }
}

void length_lbits(sail_int *rop, const lbits op)
{
  sail_int_set_small(rop, (int64_t)op.len);
}

void count_leading_zeros(sail_int *rop, const lbits op)
{
  if (op.len <= 64) {
    sail_int_set_small(rop, op.word == 0 ? (int64_t)op.len : (int64_t)op.len - (64 - sail_clz64(op.word)));
  } else if (mpz_sgn(op.big) == 0) {
    sail_int_set_small(rop, (int64_t)op.len);
  } else {
    size_t bits = mpz_sizeinbase(op.big, 2);
    sail_int_set_small(rop, (int64_t)(op.len - bits));
  }
}

void count_trailing_zeros(sail_int *rop, const lbits op)
{
  if (op.len <= 64) {
    sail_int_set_small(rop, op.word == 0 ? (int64_t)op.len : sail_ctz64(op.word));
  } else if (mpz_sgn(op.big) == 0) {
    sail_int_set_small(rop, (int64_t)op.len);
  } else {
    sail_int_set_small(rop, (int64_t)mpz_scan1(op.big, 0));
  }
}

bool eq_bits_slow(const lbits op1, const lbits op2)
{
  sail_mpz_view v1, v2;
  return mpz_cmp(sail_lbits_view(&v1, op1), sail_lbits_view(&v2, op2)) == 0;
}

/*
 * Get bits [m, m + len) of op, where len <= 64.
 */
static inline uint64_t sail_lbits_extract(const lbits op, const uint64_t m, const uint64_t len)
{
  if (op.len <= 64) {
    return safe_rshift(op.word, m) & sail_mask64(len);
  }
  /* Read at most two limbs. */
  uint64_t limb = m / 64, off = m % 64;
  size_t n = mpz_size(op.big);
  uint64_t lo = limb < n ? mpz_getlimbn(op.big, limb) : 0;
  uint64_t hi = limb + 1 < n ? mpz_getlimbn(op.big, limb + 1) : 0;
  uint64_t w = off == 0 ? lo : (lo >> off) | (hi << (64 - off));
  return w & sail_mask64(len);
}

/*
 * Set rop to bits [m, m + len) of op, for any len.
 */
static void sail_lbits_subrange(lbits *rop, const lbits op, const uint64_t m, const uint64_t len)
{
  if (len <= 64) {
    sail_lbits_set_small(rop, len, sail_lbits_extract(op, m, len));
    return;
  }
  sail_mpz_view v;
  mpz_fdiv_q_2exp(sail_lib_tmp1, sail_lbits_view(&v, op), m);
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
}

void vector_subrange_lbits(lbits *rop,
                           const lbits op,
                           const sail_int n_mpz,
                           const sail_int m_mpz)
{
  uint64_t n = sail_int_get_ui(n_mpz);
  uint64_t m = sail_int_get_ui(m_mpz);
  sail_lbits_subrange(rop, op, m, n - (m - 1ul));
}

void vector_subrange_inc_lbits(lbits *rop,
			       const lbits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz)
{
  uint64_t n = sail_int_get_ui(n_mpz);
  uint64_t m = sail_int_get_ui(m_mpz);
  sail_lbits_subrange(rop, op, (op.len - 1) - m, m - (n - 1ul));
}

void sail_truncate(lbits *rop, const lbits op, const sail_int len)
{
  uint64_t rlen = sail_int_get_ui(len);
  assert(op.len >= rlen);
  sail_lbits_subrange(rop, op, 0, rlen);
}

void sail_truncateLSB(lbits *rop, const lbits op, const sail_int len)
{
  uint64_t rlen = sail_int_get_ui(len);
  assert(op.len >= rlen);
  // similar to vector_subrange_lbits above -- right shift LSBs away
  sail_lbits_subrange(rop, op, op.len - rlen, rlen);
}

static inline fbits sail_lbits_tstbit(const lbits op, const uint64_t n)
{
  if (op.len <= 64) return n >= 64 ? 0 : (op.word >> n) & 1;
  return (fbits)mpz_tstbit(op.big, n);
}

fbits bitvector_access(const lbits op, const sail_int n_mpz)
{
  return sail_lbits_tstbit(op, sail_int_get_ui(n_mpz));
}

fbits bitvector_access_inc(const lbits op, const sail_int n_mpz)
{
  return sail_lbits_tstbit(op, (op.len - 1) - sail_int_get_ui(n_mpz));
}

fbits update_fbits(const fbits op, const uint64_t n, const fbits bit)
{
     if ((bit & 1) == 1) {
          return op | (bit << n);
     } else {
          return op & ~(bit << n);
     }
}

void sail_unsigned(sail_int *rop, const lbits op)
{
  /* Normal form of bv_t is always positive so just return the bits. */
  if (op.len <= 64 && op.word <= (uint64_t)INT64_MAX) {
    sail_int_set_small(rop, (int64_t)op.word);
    return;
  }
  sail_lbits_get_mpz(sail_lib_tmp1, op);
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void sail_signed(sail_int *rop, const lbits op)
{
  if (op.len == 0) {
    sail_int_set_small(rop, 0);
  } else if (op.len <= 64) {
    unsigned sh = 64 - op.len;
    sail_int_set_small(rop, (int64_t)(op.word << sh) >> sh);
  } else {
    sail_lbits_signed_mpz(sail_lib_tmp1, op);
    sail_int_take_mpz(rop, sail_lib_tmp1);
  }
}

mach_int fast_unsigned(const fbits op)
{
  return (mach_int) op;
}

mach_int fast_signed(const fbits op, const uint64_t n)
{
  if (op & (UINT64_C(1) << (n - 1))) {
    uint64_t rop = op & ~(UINT64_C(1) << (n - 1));
    return (mach_int) (rop - (UINT64_C(1) << (n - 1)));
  } else {
    return (mach_int) op;
  }
}

void append(lbits *rop, const lbits op1, const lbits op2)
{
  uint64_t len = op1.len + op2.len;
  if (len <= 64) {
    sail_lbits_set_small(rop, len, op2.len >= 64 ? op2.word : (op1.word << op2.len) | op2.word);
    return;
  }
  sail_mpz_view v1, v2;
  mpz_mul_2exp(sail_lib_tmp1, sail_lbits_view(&v1, op1), op2.len);
  mpz_ior(sail_lib_tmp1, sail_lib_tmp1, sail_lbits_view(&v2, op2));
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
}

sbits append_sf(const sbits op1, const fbits op2, const uint64_t len)
{
  sbits rop;
  rop.bits = (op1.bits << len) | op2;
  rop.len = op1.len + len;
  return rop;
}

sbits append_fs(const fbits op1, const uint64_t len, const sbits op2)
{
  sbits rop;
  rop.bits = (op1 << op2.len) | op2.bits;
  rop.len = len + op2.len;
  return rop;
}

sbits append_ss(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = (op1.bits << op2.len) | op2.bits;
  rop.len = op1.len + op2.len;
  return rop;
}

void replicate_bits(lbits *rop, const lbits op1, const sail_int op2)
{
  uint64_t times = sail_int_get_ui(op2);
  uint64_t len = op1.len * times;
  if (len <= 64) {
    uint64_t w = 0;
    for (uint64_t i = 0; i < times; i++) {
      w = (op1.len >= 64 ? 0 : w << op1.len) | op1.word;
    }
    sail_lbits_set_small(rop, len, w);
    return;
  }
  sail_mpz_view v;
  mpz_srcptr z = sail_lbits_view(&v, op1);
  mpz_set_ui(sail_lib_tmp1, 0);
  for (uint64_t i = 0; i < times; i++) {
    mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, op1.len);
    mpz_ior(sail_lib_tmp1, sail_lib_tmp1, z);
  }
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
}

uint64_t fast_replicate_bits(const uint64_t shift, const uint64_t v, const int64_t times)
{
  uint64_t r = v;
  for (int i = 1; i < times; ++i) {
    r |= (r << shift);
  }
  return r;
}

// Takes a slice of the (two's complement) binary representation of
// integer n, starting at bit start, and of length len. With the
// argument in the following order:
//
// get_slice_int(len, n, start)
//
// For example:
//
// get_slice_int(8, 1680, 4) =
//
//                    11           0
//                    V            V
// get_slice_int(8, 0b0110_1001_0000, 4) = 0b0110_1001
//                    <-------^
//                    (8 bit) 4
//
void get_slice_int(lbits *rop, const sail_int len_mpz, const sail_int n, const sail_int start_mpz)
{
  uint64_t start = sail_int_get_ui(start_mpz);
  uint64_t len = sail_int_get_ui(len_mpz);

  if (len <= 64 && n.big == NULL) {
    int64_t shifted = start >= 64 ? (n.val < 0 ? -1 : 0) : n.val >> start;
    sail_lbits_set_small(rop, len, (uint64_t)shifted & sail_mask64(len));
    return;
  }
  /* Floor division by 2^start, then mod 2^len, uses two's complement. */
  sail_mpz_view v;
  mpz_fdiv_q_2exp(sail_lib_tmp1, sail_int_view(&v, n), start);
  sail_lbits_take_mpz(rop, len, sail_lib_tmp1);
}

// Set slice uses the same indexing scheme as get_slice_int, but it
// puts a bitvector slice into an integer rather than returning it.
void set_slice_int(sail_int *rop,
		   const sail_int len_mpz,
		   const sail_int n,
		   const sail_int start_mpz,
		   const lbits slice)
{
  uint64_t start = sail_int_get_ui(start_mpz);

  if (n.big == NULL && slice.len <= 63 && start + slice.len <= 63) {
    uint64_t mask = sail_mask64(slice.len) << start;
    uint64_t r = ((uint64_t)n.val & ~mask) | (slice.word << start);
    sail_int_set_small(rop, (int64_t)r);
    return;
  }

  sail_int_get_mpz(sail_lib_tmp1, n);
  for (uint64_t i = 0; i < slice.len; i++) {
    if (sail_lbits_tstbit(slice, i)) {
      mpz_setbit(sail_lib_tmp1, i + start);
    } else {
      mpz_clrbit(sail_lib_tmp1, i + start);
    }
  }
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

/*
 * Set rop to op with bits [start, start + slice_len) replaced by the
 * low bits of slice.
 */
static void sail_lbits_insert(lbits *rop, const lbits op, const uint64_t start, const uint64_t slice_len, const lbits slice)
{
  if (op.len <= 64) {
    uint64_t mask = start >= 64 ? 0 : sail_mask64(slice_len) << start;
    uint64_t s = start >= 64 ? 0 : sail_lbits_low64(slice) << start;
    sail_lbits_set_small(rop, op.len, ((op.word & ~mask) | (s & mask)) & sail_mask64(op.len));
    return;
  }

  sail_lbits_get_mpz(sail_lib_tmp1, op);
  if (slice_len <= 64) {
    uint64_t s = sail_lbits_extract(slice, 0, slice_len);
    for (uint64_t i = 0; i < slice_len; i++) {
      if ((s >> i) & 1) {
        mpz_setbit(sail_lib_tmp1, i + start);
      } else {
        mpz_clrbit(sail_lib_tmp1, i + start);
      }
    }
  } else {
    /* Clear the bits, then add the shifted slice. */
    sail_mpz_view v;
    mpz_set_ui(sail_lib_tmp2, 0);
    mpz_setbit(sail_lib_tmp2, slice_len);
    mpz_sub_ui(sail_lib_tmp2, sail_lib_tmp2, 1);
    mpz_mul_2exp(sail_lib_tmp2, sail_lib_tmp2, start);
    mpz_com(sail_lib_tmp2, sail_lib_tmp2);
    mpz_and(sail_lib_tmp1, sail_lib_tmp1, sail_lib_tmp2);
    mpz_fdiv_r_2exp(sail_lib_tmp2, sail_lbits_view(&v, slice), slice_len);
    mpz_mul_2exp(sail_lib_tmp2, sail_lib_tmp2, start);
    mpz_ior(sail_lib_tmp1, sail_lib_tmp1, sail_lib_tmp2);
  }
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

void update_lbits(lbits *rop, const lbits op, const sail_int n_mpz, const uint64_t bit)
{
  uint64_t n = sail_int_get_ui(n_mpz);
  lbits b;
  b.len = 1;
  b.word = bit != 0;
  sail_lbits_insert(rop, op, n, 1, b);
}

void update_lbits_inc(lbits *rop, const lbits op, const sail_int n_mpz, const uint64_t bit)
{
  uint64_t n = sail_int_get_ui(n_mpz);
  lbits b;
  b.len = 1;
  b.word = bit != 0;
  sail_lbits_insert(rop, op, (op.len - 1) - n, 1, b);
}

void vector_update_subrange_lbits(lbits *rop,
				 const lbits op,
				 const sail_int n_mpz,
				 const sail_int m_mpz,
				 const lbits slice)
{
  uint64_t n = sail_int_get_ui(n_mpz);
  uint64_t m = sail_int_get_ui(m_mpz);
  sail_lbits_insert(rop, op, m, n - (m - 1ul), slice);
}

void vector_update_subrange_inc_lbits(lbits *rop,
                                      const lbits op,
                                      const sail_int n_mpz,
                                      const sail_int m_mpz,
                                      const lbits slice)
{
  uint64_t n = sail_int_get_ui(n_mpz);
  uint64_t m = sail_int_get_ui(m_mpz);

  sail_lbits_get_mpz(sail_lib_tmp1, op);
  for (uint64_t i = 0; i < m - (n - 1ul); i++) {
    uint64_t out_bit = ((op.len - 1) - m) + i;
    if (sail_lbits_tstbit(slice, (slice.len - 1) - i)) {
      mpz_setbit(sail_lib_tmp1, out_bit);
    } else {
      mpz_clrbit(sail_lib_tmp1, out_bit);
    }
  }
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

fbits fast_update_subrange(const fbits op,
			   const mach_int n,
			   const mach_int m,
			   const fbits slice)
{
  fbits rop = op;
  for (mach_int i = 0; i < n - (m - UINT64_C(1)); i++) {
    uint64_t bit = UINT64_C(1) << ((uint64_t) i);
    if (slice & bit) {
      rop |= (bit << m);
    } else {
      rop &= ~(bit << m);
    }
  }
  return rop;
}

void slice(lbits *rop, const lbits op, const sail_int start_mpz, const sail_int len_mpz)
{
  assert(sail_int_get_ui(start_mpz) + sail_int_get_ui(len_mpz) <= op.len);
  uint64_t start = sail_int_get_ui(start_mpz);
  uint64_t len = sail_int_get_ui(len_mpz);
  sail_lbits_subrange(rop, op, start, len);
}

void slice_inc(lbits *rop, const lbits op, const sail_int start_mpz, const sail_int len_mpz)
{
  assert(sail_int_get_ui(start_mpz) + sail_int_get_ui(len_mpz) <= op.len);
  uint64_t start = sail_int_get_ui(start_mpz);
  uint64_t len = sail_int_get_ui(len_mpz);
  /* Bit i of the result (from the high end) is bit ((op.len - 1) - start) - i of op. */
  sail_lbits_subrange(rop, op, op.len - start - len, len);
}

sbits sslice(const fbits op, const mach_int start, const mach_int len)
{
  sbits rop;
  rop.bits = bzhi_u64(op >> start, len);
  rop.len = len;
  return rop;
}

void set_slice(lbits *rop,
	       const sail_int len_mpz,
	       const sail_int slen_mpz,
	       const lbits op,
	       const sail_int start_mpz,
	       const lbits slice)
{
  uint64_t start = sail_int_get_ui(start_mpz);
  sail_lbits_insert(rop, op, start, slice.len, slice);
}

static void sail_lbits_shl(lbits *rop, const lbits op, const uint64_t shift)
{
  if (op.len <= 64) {
    sail_lbits_set_small(rop, op.len, shift >= 64 ? 0 : (op.word << shift) & sail_mask64(op.len));
    return;
  }
  mpz_mul_2exp(sail_lib_tmp1, op.big, shift);
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

static void sail_lbits_shr(lbits *rop, const lbits op, const uint64_t shift)
{
  if (op.len <= 64) {
    sail_lbits_set_small(rop, op.len, safe_rshift(op.word, shift));
    return;
  }
  mpz_tdiv_q_2exp(sail_lib_tmp1, op.big, shift);
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

static void sail_lbits_sar(lbits *rop, const lbits op, const uint64_t shift)
{
  if (op.len <= 64) {
    if (op.len == 0) {
      sail_lbits_set_small(rop, 0, 0);
      return;
    }
    unsigned sh = 64 - op.len;
    int64_t s = (int64_t)(op.word << sh) >> sh;
    s = shift >= 64 ? (s < 0 ? -1 : 0) : s >> shift;
    sail_lbits_set_small(rop, op.len, (uint64_t)s & sail_mask64(op.len));
    return;
  }
  sail_lbits_signed_mpz(sail_lib_tmp1, op);
  mpz_fdiv_q_2exp(sail_lib_tmp1, sail_lib_tmp1, shift);
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

void shift_bits_left(lbits *rop, const lbits op1, const lbits op2)
{
  sail_lbits_shl(rop, op1, sail_lbits_low64(op2));
}

void shift_bits_right(lbits *rop, const lbits op1, const lbits op2)
{
  sail_lbits_shr(rop, op1, sail_lbits_low64(op2));
}

void shift_bits_right_arith(lbits *rop, const lbits op1, const lbits op2)
{
  sail_lbits_sar(rop, op1, sail_lbits_low64(op2));
}

void arith_shiftr(lbits *rop, const lbits op1, const sail_int op2)
{
  sail_lbits_sar(rop, op1, sail_int_get_ui(op2));
}

void shiftl(lbits *rop, const lbits op1, const sail_int op2)
{
  sail_lbits_shl(rop, op1, sail_int_get_ui(op2));
}

void shiftr(lbits *rop, const lbits op1, const sail_int op2)
{
  sail_lbits_shr(rop, op1, sail_int_get_ui(op2));
}

void reverse_endianness(lbits *rop, const lbits op)
{
  if (op.len <= 64) {
    uint64_t x = op.word;
    uint64_t r;
    if (op.len == 64) {
      r = sail_bswap64(x);
    } else if (op.len == 32) {
      r = sail_bswap64(x) >> 32;
    } else if (op.len == 16) {
      r = sail_bswap64(x) >> 48;
    } else if (op.len == 8) {
      r = x;
    } else {
      r = 0;
      for (uint64_t byte = 0; byte < op.len; byte += 8) {
        r = (r << 8) | ((x >> byte) & 0xff);
      }
      r &= sail_mask64(op.len);
    }
    sail_lbits_set_small(rop, op.len, r);
    return;
  }
  /* For other numbers of bytes we reverse the bytes. */
  mpz_set_ui(sail_lib_tmp1, 0);
  for (mp_bitcnt_t byte = 0; byte < op.len; byte += 8) {
    mpz_tdiv_q_2exp(sail_lib_tmp2, op.big, byte);
    mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, 8);
    mpz_add_ui(sail_lib_tmp1, sail_lib_tmp1, mpz_get_ui(sail_lib_tmp2) & 0xff);
  }
  sail_lbits_take_mpz(rop, op.len, sail_lib_tmp1);
}

bool eq_sbits(const sbits op1, const sbits op2)
{
  return op1.bits == op2.bits;
}

bool neq_sbits(const sbits op1, const sbits op2)
{
  return op1.bits != op2.bits;
}

sbits not_sbits(const sbits op)
{
  sbits rop;
  rop.bits = (~op.bits) & bzhi_u64(UINT64_MAX, op.len);
  rop.len = op.len;
  return rop;
}

sbits xor_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = op1.bits ^ op2.bits;
  rop.len = op1.len;
  return rop;
}

sbits or_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = op1.bits | op2.bits;
  rop.len = op1.len;
  return rop;
}

sbits and_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = op1.bits & op2.bits;
  rop.len = op1.len;
  return rop;
}

sbits add_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = (op1.bits + op2.bits) & bzhi_u64(UINT64_MAX, op1.len);
  rop.len = op1.len;
  return rop;
}

sbits sub_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = (op1.bits - op2.bits) & bzhi_u64(UINT64_MAX, op1.len);
  rop.len = op1.len;
  return rop;
}

/* ***** Sail Reals ***** */

void CREATE(real)(real *rop)
{
  mpq_init(*rop);
}

void RECREATE(real)(real *rop)
{
  mpq_set_ui(*rop, 0, 1);
}

void KILL(real)(real *rop)
{
  mpq_clear(*rop);
}

void COPY(real)(real *rop, const real op)
{
  mpq_set(*rop, op);
}

void UNDEFINED(real)(real *rop, unit u)
{
  mpq_set_ui(*rop, 0, 1);
}

void neg_real(real *rop, const real op)
{
  mpq_neg(*rop, op);
}

void mult_real(real *rop, const real op1, const real op2) {
  mpq_mul(*rop, op1, op2);
}

void sub_real(real *rop, const real op1, const real op2)
{
  mpq_sub(*rop, op1, op2);
}

void add_real(real *rop, const real op1, const real op2)
{
  mpq_add(*rop, op1, op2);
}

void div_real(real *rop, const real op1, const real op2)
{
  mpq_div(*rop, op1, op2);
}

#define SQRT_PRECISION 30

/*
 * sqrt_real first checks whether the numerator and denominator are both
 * perfect squares (i.e. their square roots are integers), then it
 * will return the exact square root. If that's not the case we use the
 * Babylonian method to calculate the square root to SQRT_PRECISION decimal
 * places.
 */
void sqrt_real(mpq_t *rop, const mpq_t op)
{
  mpq_t tmp;
  mpz_t tmp_z;
  mpq_t p; /* previous estimate, p */
  mpq_t n; /* next estimate, n */

  mpq_init(tmp);
  mpz_init(tmp_z);
  mpq_init(p);
  mpq_init(n);

  /* calculate an initial guess using mpz_sqrt */
  mpz_sqrt(tmp_z, mpq_numref(op));
  mpq_set_num(p, tmp_z);
  mpz_sqrt(tmp_z, mpq_denref(op));
  mpq_set_den(p, tmp_z);

  /* Check if op is a square */
  mpq_mul(tmp, p, p);
  if (mpq_cmp(tmp, op) == 0) {
    mpq_set(*rop, p);

    mpq_clear(tmp);
    mpz_clear(tmp_z);
    mpq_clear(p);
    mpq_clear(n);
    return;
  }


  /* initialise convergence based on SQRT_PRECISION */
  /* convergence is the precision (in decimal places) we want to reach as a fraction 1/(10^precision) */
  mpq_t convergence;
  mpq_init(convergence);
  mpz_set_ui(tmp_z, 10);
  mpz_pow_ui(tmp_z, tmp_z, SQRT_PRECISION);
  mpz_set_ui(mpq_numref(convergence), 1);
  mpq_set_den(convergence, tmp_z);
  /* if op < 1 then we switch to checking relative precision for convergence */
  if (mpq_cmp_ui(op, 1, 1) < 0) {
      mpq_mul(convergence, op, convergence);
  }

  while (true) {
    // n = (p + op / p) / 2
    mpq_div(tmp, op, p);
    mpq_add(tmp, tmp, p);
    mpq_div_2exp(n, tmp, 1);

    /* calculate the difference between n and p */
    mpq_sub(tmp, p, n);
    mpq_abs(tmp, tmp);

    /* if the difference is small enough, return */
    if (mpq_cmp(tmp, convergence) < 0) {
      mpq_set(*rop, n);
      break;
    }

    mpq_swap(n, p);
  }

  mpq_clear(tmp);
  mpz_clear(tmp_z);
  mpq_clear(p);
  mpq_clear(n);
  mpq_clear(convergence);
}

void abs_real(real *rop, const real op)
{
  mpq_abs(*rop, op);
}

void round_up(sail_int *rop, const real op)
{
  mpz_cdiv_q(sail_lib_tmp1, mpq_numref(op), mpq_denref(op));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void round_down(sail_int *rop, const real op)
{
  mpz_fdiv_q(sail_lib_tmp1, mpq_numref(op), mpq_denref(op));
  sail_int_take_mpz(rop, sail_lib_tmp1);
}

void to_real(real *rop, const sail_int op)
{
  sail_mpz_view v;
  mpq_set_z(*rop, sail_int_view(&v, op));
  mpq_canonicalize(*rop);
}

void frac_to_real(real *rop, const sail_int num, const sail_int den)
{
  sail_int_get_mpz(mpq_numref(*rop), num);
  sail_int_get_mpz(mpq_denref(*rop), den);
  mpq_canonicalize(*rop);
}

bool EQUAL(real)(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) == 0;
}

bool lt_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) < 0;
}

bool gt_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) > 0;
}

bool lteq_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) <= 0;
}

bool gteq_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) >= 0;
}

void real_power(real *rop, const real base, const sail_int exp)
{
  int64_t exp_si = CONVERT_OF(mach_int, sail_int)(exp);

  mpz_set_ui(mpq_numref(*rop), 1);
  mpz_set_ui(mpq_denref(*rop), 1);

  real b;
  mpq_init(b);
  mpq_set(b, base);
  int64_t pexp = llabs(exp_si);
  while (pexp != 0) {
    // invariant: rop * b^pexp == base^abs(exp)
    if (pexp & 1) { // b^(e+1) = b * b^e
      mpq_mul(*rop, *rop, b);
      pexp -= 1;
    } else { // b^(2e) = (b*b)^e
      mpq_mul(b, b, b);
      pexp >>= 1;
    }
  }
  if (exp_si < 0) {
    mpq_inv(*rop, *rop);
  }
  mpq_clear(b);
}

void CREATE_OF(real, sail_string)(real *rop, const_sail_string op)
{
  int decimal;
  int total;

  mpq_init(*rop);
  if (gmp_sscanf(op, "%Zd.%n%Zd%n", sail_lib_tmp1, &decimal, sail_lib_tmp2, &total) == 2) {
    int len = total - decimal;
    mpz_ui_pow_ui(sail_lib_tmp3, 10, len);
    mpz_set(mpq_numref(*rop), sail_lib_tmp2);
    mpz_set(mpq_denref(*rop), sail_lib_tmp3);
    mpq_canonicalize(*rop);
    mpz_set(mpq_numref(sail_lib_tmp_real), sail_lib_tmp1);
    mpz_set_ui(mpq_denref(sail_lib_tmp_real), 1);
    mpq_add(*rop, *rop, sail_lib_tmp_real);
  } else if (gmp_sscanf(op, "%Zd/%Zd", sail_lib_tmp1, sail_lib_tmp2, &total) == 2) {
    mpz_set(mpq_numref(*rop), sail_lib_tmp1);
    mpz_set(mpq_denref(*rop), sail_lib_tmp2);
    mpq_canonicalize(*rop);
  } else if (gmp_sscanf(op, "%Zd", sail_lib_tmp1, &total) == 1) {
    mpz_set(mpq_numref(*rop), sail_lib_tmp1);
    mpz_set_ui(mpq_denref(*rop), 1);
    mpq_canonicalize(*rop);
  } else {
    fprintf(stderr, "Failed to parse rational number\n");
  }
}

void CONVERT_OF(real, sail_string)(real *rop, const_sail_string op)
{
  int decimal;
  int total;

  if (gmp_sscanf(op, "%Zd.%n%Zd%n", sail_lib_tmp1, &decimal, sail_lib_tmp2, &total) == 2) {
    int len = total - decimal;
    mpz_ui_pow_ui(sail_lib_tmp3, 10, len);
    mpz_set(mpq_numref(*rop), sail_lib_tmp2);
    mpz_set(mpq_denref(*rop), sail_lib_tmp3);
    mpq_canonicalize(*rop);
    mpz_set(mpq_numref(sail_lib_tmp_real), sail_lib_tmp1);
    mpz_set_ui(mpq_denref(sail_lib_tmp_real), 1);
    mpq_add(*rop, *rop, sail_lib_tmp_real);
  } else if (gmp_sscanf(op, "%Zd/%Zd", sail_lib_tmp1, sail_lib_tmp2, &total) == 2) {
    mpz_set(mpq_numref(*rop), sail_lib_tmp1);
    mpz_set(mpq_denref(*rop), sail_lib_tmp2);
    mpq_canonicalize(*rop);
  } else if (gmp_sscanf(op, "%Zd", sail_lib_tmp1, &total) == 1) {
    mpz_set(mpq_numref(*rop), sail_lib_tmp1);
    mpz_set_ui(mpq_denref(*rop), 1);
    mpq_canonicalize(*rop);
  } else {
    fprintf(stderr, "Failed to parse rational number\n");
  }
}

unit print_real(const_sail_string str, const real op)
{
  gmp_printf("%s%Qd\n", str, op);
  return UNIT;
}

unit prerr_real(const_sail_string str, const real op)
{
  gmp_fprintf(stderr, "%s%Qd\n", str, op);
  return UNIT;
}

void random_real(real *rop, const unit u)
{
  if (rand() & 1) {
    mpz_set_si(mpq_numref(*rop), rand());
  } else {
    mpz_set_si(mpq_numref(*rop), -rand());
  }
  mpz_set_si(mpq_denref(*rop), rand());
  mpq_canonicalize(*rop);
}

/* ***** Printing functions ***** */

void string_of_int(sail_string *str, const sail_int i)
{
  dec_str(str, i);
}

/* asprintf is a GNU extension, but it should exist on BSD */
void string_of_fbits(sail_string *str, const fbits op)
{
  sail_free(*str);
  int bytes = asprintf(str, "0x%" PRIx64, op);
  if (bytes == -1) {
    fprintf(stderr, "Could not print bits 0x%" PRIx64 "\n", op);
  }
}

void string_of_lbits(sail_string *str, const lbits op)
{
  sail_free(*str);
  sail_mpz_view v;
  mpz_srcptr z = sail_lbits_view(&v, op);
  if ((op.len % 4) == 0) {
    gmp_asprintf(str, "0x%*0ZX", op.len / 4, z);
  } else {
    *str = (char *) sail_malloc((op.len + 3) * sizeof(char));
    (*str)[0] = '0';
    (*str)[1] = 'b';
    for (int i = 1; i <= op.len; ++i) {
      (*str)[i + 1] = mpz_tstbit(z, op.len - i) + 0x30;
    }
    (*str)[op.len + 2] = '\0';
  }
}

void decimal_string_of_fbits(sail_string *str, const fbits op)
{
  sail_free(*str);
  int bytes = asprintf(str, "%" PRId64, op);
  if (bytes == -1) {
    fprintf(stderr, "Could not print bits %" PRId64 "\n", op);
  }
}

void decimal_string_of_lbits(sail_string *str, const lbits op)
{
  sail_mpz_view v;
  sail_free(*str);
  gmp_asprintf(str, "%Zd", sail_lbits_view(&v, op));
}

void parse_dec_bits(lbits *res, const sail_int n, const_sail_string dec)
{
    if (!valid_dec_bits(n, dec)) {
        goto failure;
    }

    mpz_t value;
    mpz_init(value);
    
    if (mpz_set_str(value, dec, 10) == 0) {
        sail_lbits_set_mpz(res, sail_int_get_ui(n), value);
        mpz_clear(value);
        return;
    }
    mpz_clear(value);

failure:
    zeros(res, n);
}

bool valid_dec_bits(const sail_int n, const_sail_string dec)
{
    size_t len = strlen(dec);

    if (len < 1) {
        return false;
    }

    for (size_t i = 0; i < len; i++) {
        if (!('0' <= dec[i] && dec[i] <= '9')) {
            return false;
        }
    }

    mpz_t value;
    mpz_init(value);

    if (mpz_set_str(value, dec, 10) != 0) {
        mpz_clear(value);
        return false;
    }

    size_t bit_width = mpz_sizeinbase(value, 2);

    bool valid = (bit_width <= sail_int_get_ui(n));

    mpz_clear(value);
    return valid;
}

void parse_hex_bits(lbits *res, const sail_int n, const_sail_string hex)
{
  if (!valid_hex_bits(n, hex)) {
    goto failure;
  }

  mpz_t value;
  mpz_init(value);
  if (mpz_set_str(value, hex + 2, 16) == 0) {
    sail_lbits_set_mpz(res, sail_int_get_ui(n), value);
    mpz_clear(value);
    return;
  }
  mpz_clear(value);

  // On failure, we return a zero bitvector of the correct width
failure:
  zeros(res, n);
}

bool valid_hex_bits(const sail_int n, const_sail_string hex) {
  // The string must be prefixed by '0x'
  if (strncmp(hex, "0x", 2) != 0) {
    return false;
  }

  size_t len = strlen(hex);

  // There must be at least one character after the '0x'
  if (len < 3) {
    return false;
  }

  // Ignore any leading zeros
  int non_zero = 2;
  while (hex[non_zero] == '0' && non_zero < len - 1) {
    non_zero++;
  }

  // Check how many bits we need for the first-non-zero (fnz) character.
  int fnz_width;
  char fnz = hex[non_zero];
  if (fnz == '0') {
    fnz_width = 0;
  } else if (fnz == '1') {
    fnz_width = 1;
  } else if (fnz >= '2' && fnz <= '3') {
    fnz_width = 2;
  } else if (fnz >= '4' && fnz <= '7') {
    fnz_width = 3;
  } else {
    fnz_width = 4;
  }

  // The width of the hex string is the width of the first non zero,
  // plus 4 times the remaining hex digits
  int hex_width = fnz_width + ((len - (non_zero + 1)) * 4);
  sail_int hex_width_int;
  CREATE_OF(sail_int, mach_int)(&hex_width_int, hex_width);
  if (lt(n, hex_width_int)) {
    return false;
  }

  // All the non-zero characters must be valid hex digits
  for (int i = non_zero; i < len; i++) {
    char c = hex[i];
    if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))) {
      return false;
    }
  }

  return true;
}

void fprint_bits(const_sail_string pre,
		 const lbits op,
		 const_sail_string post,
		 FILE *stream)
{
  fputs(pre, stream);

  if (op.len % 4 == 0) {
    fputs("0x", stream);
    mpz_t buf;
    mpz_init(buf);
    sail_lbits_get_mpz(buf, op);

    char *hex = (char *)sail_malloc((op.len / 4) * sizeof(char));

    for (int i = 0; i < op.len / 4; ++i) {
      char c = (char) ((0xF & mpz_get_ui(buf)) + 0x30);
      hex[i] = (c < 0x3A) ? c : c + 0x7;
      mpz_fdiv_q_2exp(buf, buf, 4);
    }

    for (int i = op.len / 4; i > 0; --i) {
      fputc(hex[i - 1], stream);
    }

    sail_free(hex);
    mpz_clear(buf);
  } else {
    fputs("0b", stream);
    for (int i = op.len; i > 0; --i) {
      fputc((int)sail_lbits_tstbit(op, i - 1) + 0x30, stream);
    }
  }

  fputs(post, stream);
}

unit print_bits(const_sail_string str, const lbits op)
{
  fprint_bits(str, op, "\n", stdout);
  return UNIT;
}

unit prerr_bits(const_sail_string str, const lbits op)
{
  fprint_bits(str, op, "\n", stderr);
  return UNIT;
}

unit print(const_sail_string str)
{
  printf("%s", str);
  return UNIT;
}

unit print_endline(const_sail_string str)
{
  printf("%s\n", str);
  return UNIT;
}

unit prerr(const_sail_string str)
{
  fprintf(stderr, "%s", str);
  return UNIT;
}

unit prerr_endline(const_sail_string str)
{
  fprintf(stderr, "%s\n", str);
  return UNIT;
}

unit print_int(const_sail_string str, const sail_int op)
{
  sail_mpz_view v;
  fputs(str, stdout);
  mpz_out_str(stdout, 10, sail_int_view(&v, op));
  putchar('\n');
  return UNIT;
}

unit fast_print_int(const_sail_string str, const int64_t op)
{
  printf("%s%" PRId64 "\n", str, op);
  return UNIT;
}

unit prerr_int(const_sail_string str, const sail_int op)
{
  sail_mpz_view v;
  fputs(str, stderr);
  mpz_out_str(stderr, 10, sail_int_view(&v, op));
  fputs("\n", stderr);
  return UNIT;
}

unit sail_putchar(const sail_int op)
{
  char c = (char) sail_int_get_ui(op);
  putchar(c);
  fflush(stdout);
  return UNIT;
}

void get_time_ns(sail_int *rop, const unit u)
{
  struct timespec t;
  clock_gettime(CLOCK_REALTIME, &t);
  sail_int_set_small(rop, (int64_t)t.tv_sec * 1000000000 + t.tv_nsec);
}

// ARM specific optimisations

void arm_align(lbits *rop, const lbits x_bv, const sail_int y_mpz)
{
  uint64_t x = sail_lbits_low64(x_bv);
  uint64_t y = sail_int_get_ui(y_mpz);
  uint64_t z = y * (x / y);
  mp_bitcnt_t n = x_bv.len;
  sail_lbits_set_u64(rop, n, safe_rshift(UINT64_MAX, 64l - (n - 1)) & z);
}

// Monomorphisation
void make_the_value(sail_int *rop, const sail_int op)
{
  COPY(sail_int)(rop, op);
}

void size_itself_int(sail_int *rop, const sail_int op)
{
  COPY(sail_int)(rop, op);
}

#ifdef __cplusplus
}
#endif
