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

unit sail_assert(bool b, sail_string msg) {
  if (b) return UNIT;
  fprintf(stderr, "Assertion failed: %s\n", msg);
  exit(1);
}

unit sail_exit(const unit u) {
  fprintf(stderr, "Unexpected exit\n");
  exit(1);
}

void elf_entry(mpz_t *rop, const unit u) {
  mpz_set_ui(*rop, 0x8000ul);
}

// Sail bits are mapped to ints where bitzero = 0 and bitone = 1
bool eq_bit(const int a, const int b) {
  return a == b;
}

int undefined_bit(unit u) { return 0; }

// ***** Sail booleans *****

bool not(const bool b) {
  return !b;
}

bool and_bool(const bool a, const bool b) {
  return a && b;
}

bool or_bool(const bool a, const bool b) {
  return a || b;
}

bool eq_bool(const bool a, const bool b) {
  return a == b;
}

bool undefined_bool(const unit u) {
  return false;
}

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

bool eq_string(const sail_string str1, const sail_string str2) {
  return strcmp(str1, str2) == 0;
}

unit print_endline(sail_string str) {
  printf("%s\n", str);
  return UNIT;
}

unit prerr_endline(sail_string str) {
  fprintf(stderr, "%s\n", str);
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

unit sail_putchar(const mpz_t op) {
  char c = (char) mpz_get_ui(op);
  putchar(c);
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

int64_t convert_int64_t_of_mpz_t(const mpz_t op) {
  return mpz_get_si(op);
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

bool lteq(const mpz_t op1, const mpz_t op2) {
  return mpz_cmp(op1, op2) <= 0;
}

bool gteq(const mpz_t op1, const mpz_t op2) {
  return mpz_cmp(op1, op2) >= 0;
}

void shl_int(mpz_t *rop, const mpz_t op1, const mpz_t op2) {
  mpz_mul_2exp(*rop, op1, mpz_get_ui(op2));
}

void undefined_int(mpz_t *rop, const unit u) {
  mpz_set_ui(*rop, 0ul);
}

void undefined_range(mpz_t *rop, const mpz_t l, const mpz_t u) {
  mpz_set(*rop, l);
}

void add_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_add(*rop, op1, op2);
}

void sub_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_sub(*rop, op1, op2);
}

void mult_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_mul(*rop, op1, op2);
}

void div_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_tdiv_q(*rop, op1, op2);
}

void mod_int(mpz_t *rop, const mpz_t op1, const mpz_t op2)
{
  mpz_tdiv_r(*rop, op1, op2);
}

void max_int(mpz_t *rop, const mpz_t op1, const mpz_t op2) {
  if (lt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

void min_int(mpz_t *rop, const mpz_t op1, const mpz_t op2) {
  if (gt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

void neg_int(mpz_t *rop, const mpz_t op) {
  mpz_neg(*rop, op);
}

void abs_int(mpz_t *rop, const mpz_t op) {
  mpz_abs(*rop, op);
}

void pow2(mpz_t *rop, mpz_t exp) {
  uint64_t exp_ui = mpz_get_ui(exp);
  mpz_t base;
  mpz_init_set_ui(base, 2ul);
  mpz_pow_ui(*rop, base, exp_ui);
  mpz_clear(base);
}

// ***** Sail bitvectors *****

void length_bv_t(mpz_t *rop, const bv_t op) {
  mpz_set_ui(*rop, op.len);
}

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

void append_64(bv_t *rop, const bv_t op, const uint64_t chunk) {
  rop->len = rop->len + 64ul;
  mpz_mul_2exp(*rop->bits, *op.bits, 64ul);
  mpz_add_ui(*rop->bits, *rop->bits, chunk);
}

void append(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len + op2.len;
  mpz_mul_2exp(*rop->bits, *op1.bits, op2.len);
  mpz_add(*rop->bits, *rop->bits, *op2.bits);
}

void replicate_bits(bv_t *rop, const bv_t op1, const mpz_t op2) {
  uint64_t op2_ui = mpz_get_ui(op2);
  rop->len = op1.len * op2_ui;
  mpz_set(*rop->bits, *op1.bits);
  for (int i = 1; i < op2_ui; i++) {
    mpz_mul_2exp(*rop->bits, *rop->bits, op2_ui);
    mpz_add(*rop->bits, *rop->bits, *op1.bits);
  }
}

void slice(bv_t *rop, const bv_t op, const mpz_t i, const mpz_t len) {
  // TODO
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

void and_bits(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len;
  mpz_and(*rop->bits, *op1.bits, *op2.bits);
}

void or_bits(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len;
  mpz_ior(*rop->bits, *op1.bits, *op2.bits);
}

void not_bits(bv_t *rop, const bv_t op) {
  rop->len = op.len;
  mpz_com(*rop->bits, *op.bits);
}

void xor_bits(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len;
  mpz_xor(*rop->bits, *op1.bits, *op2.bits);
}

bool eq_bits(const bv_t op1, const bv_t op2) {
  return mpz_cmp(*op1.bits, *op2.bits) == 0;
}

void sail_uint(mpz_t *rop, const bv_t op) {
  mpz_set(*rop, *op.bits);
}

void sint(mpz_t *rop, const bv_t op) {
  if (mpz_tstbit(*op.bits, op.len - 1)) {
    mpz_set(*rop, *op.bits);
    mpz_clrbit(*rop, op.len - 1);
    mpz_t x;
    mpz_init(x);
    mpz_setbit(x, op.len - 1);
    mpz_neg(x, x);
    mpz_add(*rop, *rop, *op.bits);
    mpz_clear(x);
  } else {
    mpz_set(*rop, *op.bits);
  }
}

void add_bits(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, *op2.bits);
  mpz_clrbit(*rop->bits, op1.len);
}

void add_bits_int(bv_t *rop, const bv_t op1, const mpz_t op2) {
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, op2);
  mask(rop);
}

void sub_bits_int(bv_t *rop, const bv_t op1, const mpz_t op2) {
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, op2);
  mask(rop);
}

void get_slice_int(bv_t *rop, const mpz_t n, const mpz_t m, const mpz_t o) {
  // TODO
}

void set_slice_int(mpz_t *rop, const mpz_t n, const mpz_t m, const mpz_t o, const bv_t op) {
  // TODO
}

void vector_update_subrange_bv_t(bv_t *rop, const bv_t op, const mpz_t n, const mpz_t m, const bv_t slice) {
  // TODO
}

void vector_subrange_bv_t(bv_t *rop, const bv_t op, const mpz_t n, const mpz_t m) {
  // TODO
}

int bitvector_access(const bv_t op, const mpz_t n) {
  return 0; // TODO
}

void hex_slice (bv_t *rop, const sail_string hex, const mpz_t n, const mpz_t m) {
  // TODO
}

void set_slice (bv_t *rop, const mpz_t len, const mpz_t slen, const bv_t op, const mpz_t i, const bv_t slice) {
  // TODO
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

void set_real(real *rop, const real op) {
  mpf_set(*rop, op);
}

void undefined_real(real *rop, unit u) {
  mpf_set_ui(*rop, 0ul);
}

void neg_real(real *rop, const real op) {
  mpf_neg(*rop, op);
}

void mult_real(real *rop, const real op1, const real op2) {
  mpf_mul(*rop, op1, op2);
}

void sub_real(real *rop, const real op1, const real op2) {
  mpf_sub(*rop, op1, op2);
}

void add_real(real *rop, const real op1, const real op2) {
  mpf_add(*rop, op1, op2);
}

void div_real(real *rop, const real op1, const real op2) {
  mpf_div(*rop, op1, op2);
}

void sqrt_real(real *rop, const real op) {
  mpf_sqrt(*rop, op);
}

void abs_real(real *rop, const real op) {
  mpf_abs(*rop, op);
}

void round_up(mpz_t *rop, const real op) {
  mpf_t x;
  mpf_ceil(x, op);
  mpz_set_ui(*rop, mpf_get_ui(x));
  mpf_clear(x);
}

void round_down(mpz_t *rop, const real op) {
  mpf_t x;
  mpf_floor(x, op);
  mpz_set_ui(*rop, mpf_get_ui(x));
  mpf_clear(x);
}

void to_real(real *rop, const mpz_t op) {
  mpf_set_z(*rop, op);
}

bool eq_real(const real op1, const real op2) {
  return mpf_cmp(op1, op2) == 0;
}

bool lt_real(const real op1, const real op2) {
  return mpf_cmp(op1, op2) < 0;
}

bool gt_real(const real op1, const real op2) {
  return mpf_cmp(op1, op2) > 0;
}

bool lteq_real(const real op1, const real op2) {
  return mpf_cmp(op1, op2) <= 0;
}

bool gteq_real(const real op1, const real op2) {
  return mpf_cmp(op1, op2) >= 0;
}

void real_power(real *rop, const real base, const mpz_t exp) {
  uint64_t exp_ui = mpz_get_ui(exp);
  mpf_pow_ui(*rop, base, exp_ui);
}

void init_real_of_sail_string(real *rop, const sail_string op) {
  // FIXME
  mpf_init(*rop);
}

#endif

#endif

// ***** Memory *****

unit write_ram(const mpz_t m, const mpz_t n, const bv_t x, const bv_t y, const bv_t data) {
  return UNIT;
}

void read_ram(bv_t *data, const mpz_t m, const mpz_t n, const bv_t x, const bv_t y) {
  // TODO
}
