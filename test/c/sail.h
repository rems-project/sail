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
  mpz_set_ui(*rop, 0x400130ul);
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

unit print_bits(const sail_string str, const bv_t op) {
  fputs(str, stdout);
  gmp_printf("%d'0x%ZX\n", op.len, op.bits);
}

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
    mpz_mul_2exp(*rop->bits, *rop->bits, op1.len);
    mpz_ior(*rop->bits, *rop->bits, *op1.bits);
  }
}

void slice(bv_t *rop, const bv_t op, const mpz_t start_mpz, const mpz_t len_mpz)
{
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0ul);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(*op.bits, i + start)) mpz_setbit(*rop->bits, i);
  }
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

void truncate(bv_t *rop, const bv_t op, const mpz_t len) {
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
  mask(rop);
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

mpz_t eq_bits_test;

bool eq_bits(const bv_t op1, const bv_t op2) {
  mpz_xor(eq_bits_test, *op1.bits, *op2.bits);
  return mpz_popcount(eq_bits_test) == 0;
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
void get_slice_int(bv_t *rop, const mpz_t len_mpz, const mpz_t n, const mpz_t start_mpz)
{
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0ul);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(n, i + start)) mpz_setbit(*rop->bits, i);
  }
}

// Set slice uses the same indexing scheme as get_slice_int, but it
// puts a bitvector slice into an integer rather than returning it.
void set_slice_int(mpz_t *rop,
		   const mpz_t len_mpz,
		   const mpz_t n,
		   const mpz_t start_mpz,
		   const bv_t slice)
{
  uint64_t start = mpz_get_ui(start_mpz);

  mpz_set(*rop, n);

  for (uint64_t i = 0; i < slice.len; i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop, i + start);
    } else {
      mpz_clrbit(*rop, i + start);
    }
  }
}

void vector_update_subrange_bv_t(bv_t *rop,
				 const bv_t op,
				 const mpz_t n_mpz,
				 const mpz_t m_mpz,
				 const bv_t slice)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  mpz_set(*rop->bits, *op.bits);

  for (uint64_t i = 0; i < n - (m - 1ul); i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop->bits, i + m);
    } else {
      mpz_clrbit(*rop->bits, i + m);
    }
  }
}

void vector_subrange_bv_t(bv_t *rop, const bv_t op, const mpz_t n_mpz, const mpz_t m_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  mpz_set_ui(*rop->bits, 0ul);
  rop->len = n - (m - 1ul);

  for (uint64_t i = 0; i < rop->len; i++) {
    if (mpz_tstbit(*op.bits, i + m)) {
      mpz_setbit(*rop->bits, i);
    } else {
      mpz_clrbit(*rop->bits, i);
    }
  }
}

int bitvector_access(const bv_t op, const mpz_t n_mpz) {
  uint64_t n = mpz_get_ui(n_mpz);
  return mpz_tstbit(*op.bits, n);
}

void hex_slice (bv_t *rop, const sail_string hex, const mpz_t n, const mpz_t m) {
  fprintf(stderr, "hex_slice unimplemented");
  exit(1);
}

void set_slice (bv_t *rop,
		const mpz_t len_mpz,
		const mpz_t slen_mpz,
		const bv_t op,
		const mpz_t start_mpz,
		const bv_t slice)
{
  uint64_t start = mpz_get_ui(start_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  for (uint64_t i = 0; i < slice.len; i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop->bits, i + start);
    } else {
      mpz_clrbit(*rop->bits, i + start);
    }
  }
}

// ***** Real number implementation *****

#define REAL_FLOAT

#ifdef REAL_FLOAT

typedef mpf_t real;

#define FLOAT_PRECISION 255

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
  fprintf(stderr, "write_ram unimplemented");
  exit(1);
}

void read_ram(bv_t *data, const mpz_t m, const mpz_t n, const bv_t x, const bv_t addr_bv) {
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint32_t instr;
  switch (addr) {
    // print_char
  case 0x400110: instr = 0xd10043ffu; break;
  case 0x400114: instr = 0x39003fe0u; break;
  case 0x400118: instr = 0x39403fe0u; break;
  case 0x40011c: instr = 0x580003e1u; break;
  case 0x400120: instr = 0x39000020u; break;
  case 0x400124: instr = 0xd503201fu; break;
  case 0x400128: instr = 0x910043ffu; break;
  case 0x40012c: instr = 0xd65f03c0u; break;
    // _start
  case 0x400130: instr = 0xa9be7bfdu; break;
  case 0x400134: instr = 0x910003fdu; break;
  case 0x400138: instr = 0x94000007u; break;
  case 0x40013c: instr = 0xb9001fa0u; break;
  case 0x400140: instr = 0x52800080u; break;
  case 0x400144: instr = 0x97fffff3u; break;
  case 0x400148: instr = 0xd503201fu; break;
  case 0x40014c: instr = 0xa8c27bfdu; break;
  case 0x400150: instr = 0xd65f03c0u; break;
    // main
  case 0x400154: instr = 0xd10043ffu; break;
  case 0x400158: instr = 0xb9000fffu; break;
  case 0x40015c: instr = 0xb9000bffu; break;
  case 0x400160: instr = 0x14000007u; break;
  case 0x400164: instr = 0xb9400fe0u; break;
  case 0x400168: instr = 0x11000400u; break;
  case 0x40016c: instr = 0xb9000fe0u; break;
  case 0x400170: instr = 0xb9400be0u; break;
  case 0x400174: instr = 0x11000400u; break;
  case 0x400178: instr = 0xb9000be0u; break;
  case 0x40017c: instr = 0xb9400be0u; break;
  case 0x400180: instr = 0x710fa01fu; break;
  case 0x400184: instr = 0x54ffff0du; break;
  case 0x400188: instr = 0xb9400fe0u; break;
  case 0x40018c: instr = 0x910043ffu; break;
  case 0x400190: instr = 0xd65f03c0u; break;
  case 0x400194: instr = 0x00000000u; break;
  case 0x400198: instr = 0x13000000u; break;
  case 0x40019c: instr = 0x00000000u; break;
  }

  mpz_set_ui(*data->bits, instr);
  data->len = 32;
  print_bits("instruction = ", *data);
}

// ***** Setup and cleanup functions for library code *****

void setup_library(void) {
  mpf_set_default_prec(FLOAT_PRECISION);
  mpz_init(eq_bits_test);
}

void cleanup_library(void) {
  mpz_clear(eq_bits_test);
}
