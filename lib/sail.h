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

unit undefined_unit(const unit u) {
  return UNIT;
}

typedef struct {
  mp_bitcnt_t len;
  mpz_t *bits;
} bv_t;

typedef char *sail_string;

// This function should be called whenever a pattern match failure
// occurs. Pattern match failures are always fatal.
void sail_match_failure(sail_string msg) {
  fprintf(stderr, "Pattern match failure in %s\n", msg);
  exit(EXIT_FAILURE);
}

unit sail_assert(bool b, sail_string msg) {
  if (b) return UNIT;
  fprintf(stderr, "Assertion failed: %s\n", msg);
  exit(EXIT_FAILURE);
}

unit sail_exit(const unit u) {
  fprintf(stderr, "exit\n");
  exit(EXIT_SUCCESS);
}

void elf_entry(mpz_t *rop, const unit u) {
  mpz_set_ui(*rop, 0x400168ul);
}

// Sail bits are mapped to uint64_t where bitzero = 0ul and bitone = 1ul
bool eq_bit(const uint64_t a, const uint64_t b) {
  return a == b;
}

uint64_t undefined_bit(unit u) { return 0; }

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

void reinit_sail_string(sail_string *str) {
  free(*str);
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

void reinit_mpz_t(mpz_t *op) {
  mpz_set_ui(*op, 0);
}

void clear_mpz_t(mpz_t *op) {
  mpz_clear(*op);
}

void init_mpz_t_of_int64_t(mpz_t *rop, int64_t op) {
  mpz_init_set_si(*rop, op);
}

void reinit_mpz_t_of_int64_t(mpz_t *rop, int64_t op) {
  mpz_set_si(*rop, op);
}

void init_mpz_t_of_sail_string(mpz_t *rop, sail_string str) {
  mpz_init_set_str(*rop, str, 10);
}

void reinit_mpz_t_of_sail_string(mpz_t *rop, sail_string str) {
  mpz_set_str(*rop, str, 10);
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

unit print_bits(const sail_string str, const bv_t op)
{
  fputs(str, stdout);

  if (op.len % 4 == 0) {
    fputs("0x", stdout);
    mpz_t buf;
    mpz_init_set(buf, *op.bits);

    char *hex = malloc((op.len / 4) * sizeof(char));

    for (int i = 0; i < op.len / 4; ++i) {
      char c = (char) ((0xF & mpz_get_ui(buf)) + 0x30);
      hex[i] = (c < 0x3A) ? c : c + 0x7;
      mpz_fdiv_q_2exp(buf, buf, 4);
    }

    for (int i = op.len / 4; i > 0; --i) {
      fputc(hex[i - 1], stdout);
    }

    free(hex);
    mpz_clear(buf);
  } else {
    fputs("0b", stdout);
    for (int i = op.len; i > 0; --i) {
      fputc(mpz_tstbit(*op.bits, i - 1) + 0x30, stdout);
    }
  }

  fputs("\n", stdout);
}

void length_bv_t(mpz_t *rop, const bv_t op) {
  mpz_set_ui(*rop, op.len);
}

void init_bv_t(bv_t *rop) {
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = 0;
  mpz_init(*rop->bits);
}

void reinit_bv_t(bv_t *rop) {
  rop->len = 0;
  mpz_set_ui(*rop->bits, 0);
}

void init_bv_t_of_uint64_t(bv_t *rop, const uint64_t op, const uint64_t len, const bool direction) {
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = len;
  mpz_init_set_ui(*rop->bits, op);
}

void reinit_bv_t_of_uint64_t(bv_t *rop, const uint64_t op, const uint64_t len, const bool direction) {
  rop->len = len;
  mpz_set_ui(*rop->bits, op);
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

uint64_t fast_replicate_bits(const uint64_t shift, const uint64_t v, const int64_t times) {
  uint64_t r = 0;
  for (int i = 0; i < times; ++i) {
    r |= v << shift;
  }
  return r;
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

bool eq_bits(const bv_t op1, const bv_t op2)
{
  for (mp_bitcnt_t i = 0; i < op1.len; i++) {
    if (mpz_tstbit(*op1.bits, i) != mpz_tstbit(*op2.bits, i)) return false;
  }
  return true;
}

// These aren't very efficient, but they work. Question is how best to
// do these given GMP uses a sign bit representation?
void sail_uint(mpz_t *rop, const bv_t op) {
  mpz_set_ui(*rop, 0ul);
  for (mp_bitcnt_t i = 0; i < op.len; ++i) {
    if (mpz_tstbit(*op.bits, i)) {
      mpz_setbit(*rop, i);
    } else {
      mpz_clrbit(*rop, i);
    }
  }
}

void sint(mpz_t *rop, const bv_t op)
{
  mpz_set_ui(*rop, 0ul);
  if (mpz_tstbit(*op.bits, op.len - 1)) {
    for (mp_bitcnt_t i = 0; i < op.len; ++i) {
      if (mpz_tstbit(*op.bits, i)) {
	mpz_clrbit(*rop, i);
      } else {
	mpz_setbit(*rop, i);
      }
    };
    mpz_add_ui(*rop, *rop, 1ul);
    mpz_neg(*rop, *rop);
  } else {
    for (mp_bitcnt_t i = 0; i < op.len; ++i) {
      if (mpz_tstbit(*op.bits, i)) {
	mpz_setbit(*rop, i);
      } else {
	mpz_clrbit(*rop, i);
      }
    }
  }
}

void add_bits(bv_t *rop, const bv_t op1, const bv_t op2) {
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, *op2.bits);
}

void add_bits_int(bv_t *rop, const bv_t op1, const mpz_t op2) {
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, op2);
}

void sub_bits_int(bv_t *rop, const bv_t op1, const mpz_t op2) {
  printf("sub_bits_int\n");
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, op2);
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

// Like slice but slices from a hexadecimal string.
void hex_slice (bv_t *rop, const sail_string hex, const mpz_t len_mpz, const mpz_t start_mpz) {
  mpz_t op;
  mpz_init_set_str(op, hex, 0);
  get_slice_int(rop, len_mpz, op, start_mpz);
  mpz_clear(op);
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

void reinit_real(real *rop) {
  mpf_set_ui(*rop, 0);
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
  mpf_init(x);
  mpf_ceil(x, op);
  mpz_set_ui(*rop, mpf_get_ui(x));
  mpf_clear(x);
}

void round_down(mpz_t *rop, const real op) {
  mpf_t x;
  mpf_init(x);
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

/* ***** Sail memory builtins ***** */

/* We organise memory available to the sail model into a linked list
   of dynamically allocated MASK + 1 size blocks. The most recently
   written block is moved to the front of the list, so contiguous
   accesses should be as fast as possible. */

struct block {
  uint64_t block_id;
  uint8_t *mem;
  struct block *next;
};

struct block *sail_memory = NULL;

/* Must be one less than a power of two. */
uint64_t MASK = 0xFFFFul;

// All sail vectors are at least 64-bits, but only the bottom 8 bits
// are used in the second argument.
void write_mem(uint64_t address, uint64_t byte)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct block *prev = NULL;
  struct block *current = sail_memory;

  while (current != NULL) {
    if (current->block_id == mask) {
      current->mem[offset] = (uint8_t) byte;

      /* Move the accessed block to the front of the block list */
      if (prev != NULL) {
        prev->next = current->next;
      }
      current->next = sail_memory->next;
      sail_memory = current;

      return;
    } else {
      prev = current;
      current = current->next;
    }
  }

  /* If we couldn't find a block matching the mask, allocate a new
     one, write the byte, and put it at the front of the block
     list. */
  struct block *new_block = malloc(sizeof(struct block));
  new_block->block_id = mask;
  new_block->mem = calloc(MASK + 1, sizeof(uint8_t));
  new_block->mem[offset] = byte;
  new_block->next = sail_memory;
  sail_memory = new_block;
}

uint64_t read_mem(uint64_t address)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct block *current = sail_memory;

  while (current != NULL) {
    if (current->block_id == mask) {
      return (uint64_t) current->mem[offset];
    } else {
      current = current->next;
    }
  }

  return 0;
}

void kill_mem()
{
  while (sail_memory != NULL) {
    struct block *next = sail_memory->next;

    free(sail_memory->mem);
    free(sail_memory);

    sail_memory = next;
  }
}

// ***** ARM Memory builtins *****

// These memory builtins are intended to match the semantics for the
// __ReadRAM and __WriteRAM functions in ASL.

unit write_ram(const mpz_t addr_size,     // Either 32 or 64
	       const mpz_t data_size_mpz, // Number of bytes
	       const bv_t  hex_ram,       // Currently unused
	       const bv_t  addr_bv,
	       const bv_t  data)
{
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint64_t data_size = mpz_get_ui(data_size_mpz);

  mpz_t buf;
  mpz_init_set(buf, *data.bits);

  uint64_t byte;
  for(uint64_t i = 0; i < data_size; ++i) {
    // Take the 8 low bits of buf and write to addr.
    byte = mpz_get_ui(buf) & 0xFF;
    write_mem(addr + i, byte);

    // Then shift buf 8 bits right, and increment addr.
    mpz_fdiv_q_2exp(buf, buf, 8);
  }

  mpz_clear(buf);
  return UNIT;
}

void read_ram(bv_t *data,
	      const mpz_t addr_size,
	      const mpz_t data_size_mpz,
	      const bv_t hex_ram,
	      const bv_t addr_bv)
{
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint64_t data_size = mpz_get_ui(data_size_mpz);

  mpz_set_ui(*data->bits, 0);
  data->len = data_size * 8;

  mpz_t byte;
  mpz_init(byte);
  for(uint64_t i = data_size; i > 0; --i) {
    mpz_set_ui(byte, read_mem(addr + (i - 1)));
    mpz_mul_2exp(*data->bits, *data->bits, 8);
    mpz_add(*data->bits, *data->bits, byte);
  }

  mpz_clear(byte);
}

void load_image(char *file) {
  FILE *fp = fopen(file, "r");

  if (!fp) {
    fprintf(stderr, "Image file %s could not be loaded\n", file);
    exit(EXIT_FAILURE);
  }

  char *addr = NULL;
  char *data = NULL;
  size_t len = 0;

  while (true) {
    ssize_t addr_len = getline(&addr, &len, fp);
    if (addr_len == -1) break;
    ssize_t data_len = getline(&data, &len, fp);
    if (data_len == -1) break;

    write_mem((uint64_t) atoll(addr), (uint64_t) atoll(data));
  }

  free(addr);
  free(data);
  fclose(fp);
}

void load_instr(uint64_t addr, uint32_t instr) {
  write_mem(addr    , instr       & 0xFF);
  write_mem(addr + 1, instr >> 8  & 0xFF);
  write_mem(addr + 2, instr >> 16 & 0xFF);
  write_mem(addr + 3, instr >> 24 & 0xFF);
}

// ***** Setup and cleanup functions for library code *****

void setup_library(void) {
  mpf_set_default_prec(FLOAT_PRECISION);
  mpz_init(eq_bits_test);
}

void cleanup_library(void) {
  mpz_clear(eq_bits_test);
  kill_mem();
}
