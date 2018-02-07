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
  mpz_t bits;
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

// ***** Multiple precision integers *****

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

#endif
