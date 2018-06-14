#include<inttypes.h>
#include<stdbool.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

#include"sail.h"

/*
 * Temporary mpzs for use in functions below. To avoid conflicts, only
 * use in functions that do not call other functions in this file.
 */
static sail_int sail_lib_tmp1, sail_lib_tmp2;

#define FLOAT_PRECISION 255

void setup_library(void)
{
  mpz_init(sail_lib_tmp1);
  mpz_init(sail_lib_tmp2);
  mpf_set_default_prec(FLOAT_PRECISION);
}

void cleanup_library(void)
{
  mpz_clear(sail_lib_tmp1);
  mpz_clear(sail_lib_tmp2);
}

/* ***** Sail bit type ***** */

bool eq_bit(const mach_bits a, const mach_bits b)
{
  return a == b;
}

/* ***** Sail booleans ***** */

bool not(const bool b) {
  return !b;
}

bool eq_bool(const bool a, const bool b) {
  return a == b;
}

bool UNDEFINED(bool)(const unit u) {
  return false;
}

/* ***** Sail strings ***** */

void CREATE(sail_string)(sail_string *str) {
  char *istr = (char *) malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void RECREATE(sail_string)(sail_string *str) {
  free(*str);
  char *istr = (char *) malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void COPY(sail_string)(sail_string *str1, const sail_string str2) {
  size_t len = strlen(str2);
  *str1 = realloc(*str1, len + 1);
  *str1 = strcpy(*str1, str2);
}

void KILL(sail_string)(sail_string *str) {
  free(*str);
}

void dec_str(sail_string *str, const mpz_t n) {
  free(*str);
  gmp_asprintf(str, "%Zd", n);
}

void hex_str(sail_string *str, const mpz_t n) {
  free(*str);
  gmp_asprintf(str, "0x%Zx", n);
}

bool eq_string(const sail_string str1, const sail_string str2) {
  return strcmp(str1, str2) == 0;
}

/* ***** Sail integers ***** */

#ifndef USE_INT128

inline
void COPY(sail_int)(sail_int *rop, const sail_int op)
{
  mpz_set(*rop, op);
}

inline
void CREATE(sail_int)(sail_int *rop)
{
  mpz_init(*rop);
}

inline
void RECREATE(sail_int)(sail_int *rop)
{
  mpz_set_ui(*rop, 0);
}

inline
void KILL(sail_int)(sail_int *rop)
{
  mpz_clear(*rop);
}

inline
void CREATE_OF(sail_int, mach_int)(sail_int *rop, mach_int op)
{
  mpz_init_set_si(*rop, op);
}

inline
void RECREATE_OF(sail_int, mach_int)(sail_int *rop, mach_int op)
{
  mpz_set_si(*rop, op);
}

inline
void CREATE_OF(sail_int, sail_string)(sail_int *rop, sail_string str)
{
  mpz_init_set_str(*rop, str, 10);
}

inline
void RECREATE_OF(sail_int, sail_string)(mpz_t *rop, sail_string str)
{
  mpz_set_str(*rop, str, 10);
}

inline
mach_int CONVERT_OF(mach_int, sail_int)(const sail_int op)
{
  return mpz_get_si(op);
}

inline
void CONVERT_OF(sail_int, mach_int)(sail_int *rop, const mach_int op)
{
  mpz_set_si(*rop, op);
}

inline
bool eq_int(const sail_int op1, const sail_int op2)
{
  return !abs(mpz_cmp(op1, op2));
}

inline
bool lt(const sail_int op1, const sail_int op2)
{
  return mpz_cmp(op1, op2) < 0;
}

inline
bool gt(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) > 0;
}

inline
bool lteq(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) <= 0;
}

inline
bool gteq(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) >= 0;
}

inline
void shl_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_mul_2exp(*rop, op1, mpz_get_ui(op2));
}

inline
void shr_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_q_2exp(*rop, op1, mpz_get_ui(op2));
}

inline
void undefined_int(sail_int *rop, const int n)
{
  mpz_set_ui(*rop, (uint64_t) n);
}

inline
void undefined_range(sail_int *rop, const sail_int l, const sail_int u)
{
  mpz_set(*rop, l);
}

inline
void add_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_add(*rop, op1, op2);
}

inline
void sub_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_sub(*rop, op1, op2);
}

inline
void mult_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_mul(*rop, op1, op2);
}

inline
void tdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_tdiv_q(*rop, op1, op2);
}

inline
void tmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_tdiv_r(*rop, op1, op2);
}

inline
void fdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_q(*rop, op1, op2);
}

inline
void fmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_r(*rop, op1, op2);
}

void max_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (lt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

void min_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (gt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

inline
void neg_int(sail_int *rop, const sail_int op)
{
  mpz_neg(*rop, op);
}

inline
void abs_int(sail_int *rop, const sail_int op)
{
  mpz_abs(*rop, op);
}

void pow2(sail_int *rop, const sail_int exp) {
  /* Assume exponent is never more than 2^64... */
  uint64_t exp_ui = mpz_get_ui(exp);
  mpz_t base;
  mpz_init_set_ui(base, 2ul);
  mpz_pow_ui(*rop, base, exp_ui);
  mpz_clear(base);
}

#endif

/* ***** Sail bitvectors ***** */

void CREATE(sail_bits)(sail_bits *rop)
{
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = 0;
  mpz_init(*rop->bits);
}

void RECREATE(sail_bits)(sail_bits *rop)
{
  rop->len = 0;
  mpz_set_ui(*rop->bits, 0);
}

void COPY(sail_bits)(sail_bits *rop, const sail_bits op)
{
  rop->len = op.len;
  mpz_set(*rop->bits, *op.bits);
}

void KILL(sail_bits)(sail_bits *rop)
{
  mpz_clear(*rop->bits);
  free(rop->bits);
}

void CREATE_OF(sail_bits, mach_bits)(sail_bits *rop, const uint64_t op, const uint64_t len, const bool direction)
{
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = len;
  mpz_init_set_ui(*rop->bits, op);
}

void RECREATE_OF(sail_bits, mach_bits)(sail_bits *rop, const uint64_t op, const uint64_t len, const bool direction)
{
  rop->len = len;
  mpz_set_ui(*rop->bits, op);
}

mach_bits CONVERT_OF(mach_bits, sail_bits)(const sail_bits op)
{
  return mpz_get_ui(*op.bits);
}

void UNDEFINED(sail_bits)(sail_bits *rop, const sail_int len, const mach_bits bit)
{
  zeros(rop, len);
}

mach_bits UNDEFINED(mach_bits)(const unit u) { return 0; }

mach_bits safe_rshift(const mach_bits x, const mach_bits n)
{
  if (n >= 64) {
    return 0ul;
  } else {
    return x >> n;
  }
}

void normalize_sail_bits(sail_bits *rop) {
  /* TODO optimisation: keep a set of masks of various sizes handy */
  mpz_set_ui(sail_lib_tmp1, 1);
  mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, rop->len);
  mpz_sub_ui(sail_lib_tmp1, sail_lib_tmp1, 1);
  mpz_and(*rop->bits, *rop->bits, sail_lib_tmp1);
}

void append_64(sail_bits *rop, const sail_bits op, const mach_bits chunk)
{
  rop->len = rop->len + 64ul;
  mpz_mul_2exp(*rop->bits, *op.bits, 64ul);
  mpz_add_ui(*rop->bits, *rop->bits, chunk);
}

void add_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, *op2.bits);
  normalize_sail_bits(rop);
}

void sub_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, *op2.bits);
  normalize_sail_bits(rop);
}

void add_bits_int(sail_bits *rop, const sail_bits op1, const mpz_t op2)
{
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, op2);
  normalize_sail_bits(rop);
}

void sub_bits_int(sail_bits *rop, const sail_bits op1, const mpz_t op2)
{
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, op2);
  normalize_sail_bits(rop);
}

void zeros(sail_bits *rop, const sail_int op)
{
  rop->len = mpz_get_ui(op);
  mpz_set_ui(*rop->bits, 0);
}

void zero_extend(sail_bits *rop, const sail_bits op, const sail_int len)
{
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
}

void length_sail_bits(sail_int *rop, const sail_bits op)
{
  mpz_set_ui(*rop, op.len);
}

bool eq_bits(const sail_bits op1, const sail_bits op2)
{
  for (mp_bitcnt_t i = 0; i < op1.len; i++) {
    if (mpz_tstbit(*op1.bits, i) != mpz_tstbit(*op2.bits, i)) return false;
  }
  return true;
}

void vector_subrange_sail_bits(sail_bits *rop,
			       const sail_bits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  rop->len = n - (m - 1ul);
  mpz_fdiv_q_2exp(*rop->bits, *op.bits, m);
  normalize_sail_bits(rop);
}

void truncate(sail_bits *rop, const sail_bits op, const sail_int len)
{
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
  normalize_sail_bits(rop);
}

mach_bits bitvector_access(const sail_bits op, const sail_int n_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  return (mach_bits) mpz_tstbit(*op.bits, n);
}

void sail_unsigned(sail_int *rop, const sail_bits op)
{
  /* Normal form of bv_t is always positive so just return the bits. */
  mpz_set(*rop, *op.bits);
}

void sail_signed(sail_int *rop, const sail_bits op)
{
  if (op.len == 0) {
    mpz_set_ui(*rop, 0);
  } else {
    mp_bitcnt_t sign_bit = op.len - 1;
    mpz_set(*rop, *op.bits);
    if (mpz_tstbit(*op.bits, sign_bit) != 0) {
      /* If sign bit is unset then we are done,
         otherwise clear sign_bit and subtract 2**sign_bit */
      mpz_set_ui(sail_lib_tmp1, 1);
      mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, sign_bit); /* 2**sign_bit */
      mpz_combit(*rop, sign_bit); /* clear sign_bit */
      mpz_sub(*rop, *rop, sail_lib_tmp1);
    }
  }
}

/* ***** Printing functions ***** */

void fprint_bits(const sail_string pre,
		 const sail_bits op,
		 const sail_string post,
		 FILE *stream)
{
  fputs(pre, stream);

  if (op.len % 4 == 0) {
    fputs("0x", stream);
    mpz_t buf;
    mpz_init_set(buf, *op.bits);

    char *hex = malloc((op.len / 4) * sizeof(char));

    for (int i = 0; i < op.len / 4; ++i) {
      char c = (char) ((0xF & mpz_get_ui(buf)) + 0x30);
      hex[i] = (c < 0x3A) ? c : c + 0x7;
      mpz_fdiv_q_2exp(buf, buf, 4);
    }

    for (int i = op.len / 4; i > 0; --i) {
      fputc(hex[i - 1], stream);
    }

    free(hex);
    mpz_clear(buf);
  } else {
    fputs("0b", stream);
    for (int i = op.len; i > 0; --i) {
      fputc(mpz_tstbit(*op.bits, i - 1) + 0x30, stream);
    }
  }

  fputs(post, stream);
}

unit print_bits(const sail_string str, const sail_bits op)
{
  fprint_bits(str, op, "\n", stdout);
  return UNIT;
}

unit prerr_bits(const sail_string str, const sail_bits op)
{
  fprint_bits(str, op, "\n", stderr);
  return UNIT;
}

unit print(const sail_string str)
{
  printf("%s", str);
  return UNIT;
}

unit print_endline(const sail_string str)
{
  printf("%s\n", str);
  return UNIT;
}

unit prerr(const sail_string str)
{
  fprintf(stderr, "%s", str);
  return UNIT;
}

unit prerr_endline(const sail_string str)
{
  fprintf(stderr, "%s\n", str);
  return UNIT;
}

unit print_int(const sail_string str, const sail_int op)
{
  fputs(str, stdout);
  mpz_out_str(stdout, 10, op);
  putchar('\n');
  return UNIT;
}

unit prerr_int(const sail_string str, const sail_int op)
{
  fputs(str, stderr);
  mpz_out_str(stderr, 10, op);
  fputs("\n", stderr);
  return UNIT;
}
