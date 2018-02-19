#ifndef SAIL_LIB
#define SAIL_LIB

#include<stdio.h>
#include<inttypes.h>
#include<stdlib.h>
#include<stdbool.h>
#include<string.h>
#include<gmp.h>

typedef int unit;

#define UNIT 0

typedef struct {
  mp_bitcnt_t len;
  mpz_t *bits;
} bv_t;

typedef char *sail_string;

// This function should be called whenever a pattern match failure
// occurs. Pattern match failures are always fatal.
void sail_match_failure(void) {
  fprintf(stderr, "Pattern match failure\n");
  exit(1);
}

bool not(const bool b) {
  return !b;
}

int undefined_bit(unit u) { return 0; }

// ***** Sail strings *****
void init_sail_string(sail_string *str) {
  char *istr = (char *) malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void set_sail_string(sail_string *str1, const sail_string str2) {
  size_t len = strlen(str2);
  *str1 = realloc(*str1, len + 1);
  *str1 = strcpy(*str1, str2);
}

void clear_sail_string(sail_string *str) {
  free(*str);
}

unit print_endline(sail_string str) {
  printf("%s\n", str);
  return UNIT;
}

unit print_int(const sail_string str, const mpz_t op) {
  fputs(str, stdout);
  mpz_out_str(stdout, 10, op);
  putchar('\n');
  return UNIT;
}

unit print_int64(const sail_string str, const int64_t op) {
  printf("%s%" PRId64 "\n", str, op);
  return UNIT;
}

// ***** Arbitrary precision integers *****

// We wrap around the GMP functions so they follow a consistent naming
// scheme that is shared with the other builtin sail types.

void set_mpz_t(mpz_t *rop, const mpz_t op) {
  mpz_set(*rop, op);
}

void init_mpz_t(mpz_t *op) {
  mpz_init(*op);
}

void clear_mpz_t(mpz_t *op) {
  mpz_clear(*op);
}

void init_mpz_t_of_int64_t(mpz_t *rop, int64_t op) {
  mpz_init_set_si(*rop, op);
}

void init_mpz_t_of_sail_string(mpz_t *rop, sail_string str) {
  mpz_init_set_str(*rop, str, 10);
}

// ***** Sail builtins for integers *****

bool eq_int(const mpz_t op1, const mpz_t op2) {
  return !abs(mpz_cmp(op1, op2));
}

bool lt(const mpz_t op1, const mpz_t op2) {
  return mpz_cmp(op1, op2) < 0;
}

bool gt(const mpz_t op1, const mpz_t op2) {
  return mpz_cmp(op1, op2) > 0;
}

void undefined_int(mpz_t *rop, const unit u) {
  mpz_set_ui(*rop, 0ul);
}

void add_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_add(*rop, op1, op2);
}

void sub_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_sub(*rop, op1, op2);
}

void neg_int(mpz_t *rop, const mpz_t op) {
  mpz_neg(*rop, op);
}

void abs_int(mpz_t *rop, const mpz_t op) {
  mpz_abs(*rop, op);
}

// ***** Sail bitvectors *****

void init_bv_t(bv_t *rop) {
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = 0;
  mpz_init(*rop->bits);
}

void init_bv_t_of_uint64_t(bv_t *rop, const uint64_t op, const uint64_t len, const bool direction) {
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = len;
  mpz_init_set_ui(*rop->bits, op);
}

void set_bv_t(bv_t *rop, const bv_t op) {
  rop->len = op.len;
  mpz_set(*rop->bits, *op.bits);
}

void append_64(bv_t *rop, bv_t op, const uint64_t chunk) {
  rop->len = rop->len + 64ul;
  mpz_mul_2exp(*rop->bits, *op.bits, 64ul);
  mpz_add_ui(*rop->bits, *rop->bits, chunk);
}

uint64_t convert_uint64_t_of_bv_t(const bv_t op) {
  return mpz_get_ui(*op.bits);
}

void zeros(bv_t *rop, const mpz_t op) {
  rop->len = mpz_get_ui(op);
  mpz_set_ui(*rop->bits, 0ul);
}

void zero_extend(bv_t *rop, const bv_t op, const mpz_t len) {
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
}

void clear_bv_t(bv_t *rop) {
  mpz_clear(*rop->bits);
  free(rop->bits);
}

void undefined_bv_t(bv_t *rop, mpz_t len, int bit) {
  zeros(rop, len);
}

void mask(bv_t *rop) {
  if (mpz_sizeinbase(*rop->bits, 2) > rop->len) {
    mpz_t m;
    mpz_init(m);
    mpz_ui_pow_ui(m, 2ul, rop->len);
    mpz_sub_ui(m, m, 1ul);
    mpz_and(*rop->bits, *rop->bits, m);
    mpz_clear(m);
  }
}

void add_bits(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, *op2.bits);
  mpz_clrbit(*rop->bits, op1.len);
}

uint64_t add_bits_32(const uint64_t op1, const uint64_t op2) {
  return (op1 + op2) & 0x00000000FFFFFFFFul;
}


bool eq_bits(const bv_t op1, const bv_t op2) {
  return mpz_cmp(*op1.bits, *op2.bits) == 0;
}

bool eq_bits_32(const uint64_t op1, const uint64_t op2) {
  return (op1 == op2);
}

void add_bits_int(bv_t *rop, const bv_t op1, const mpz_t op2) {
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, op2);
  mask(rop);
}

unit print_bits(const sail_string str, const bv_t op) {
  fputs(str, stdout);
  gmp_printf("%d'0x%ZX\n", op.len, op.bits);
}

// ***** Real number implementation *****

#define REAL_FLOAT

#ifdef REAL_FLOAT

typedef mpf_t real;

#define FLOAT_PRECISION 255

void setup_real(void) {
  mpf_set_default_prec(FLOAT_PRECISION);
}

void init_real(real *rop) {
  mpf_init(*rop);
}

void clear_real(real *rop) {
  mpf_clear(*rop);
}

#endif

#endif
