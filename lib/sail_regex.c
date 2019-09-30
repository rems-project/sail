#include<stdio.h>
#include<string.h>

#include"sail_regex.h"

bool string_match(sail_string regex_str, sail_string str)
{
  regex_t r;
  int err = regcomp(&r, regex_str, REG_ICASE | REG_EXTENDED);

  if (err) {
    size_t length = regerror(err, &r, NULL, 0);
    char *buffer = malloc(length);
    regerror(err, &r, buffer, length);
    fprintf(stderr, "Failed to compile regular expression: %s\n", buffer);
    free(buffer);
    exit(1);
  }

  err = regexec(&r, str, 0, NULL, 0);
  regfree(&r);

  if (err == REG_ESPACE) {
    fprintf(stderr, "regexec failed with REG_ESPACE");
    exit(1);
  } else if (err == REG_NOMATCH) {
    return false;
  } else {
    return true;
  }
}

/**************************************************************************
 * __split for string append patterns (lib/mapping.sail)                  *
 **************************************************************************/

/* sail_match types are allocated by __split, and copying afterwards
   is handled by refcounting, so CREATE for sail_match just sets the
   pointer to the underlying match structure to NULL. This ensures
   that CREATE followed immediately by COPY does no allocation. */
void CREATE(sail_match)(sail_match *m)
{
  *m = NULL;
}

void KILL(sail_match)(sail_match *m)
{
  if ((*m)->ref_count == 0) {
    free((*m)->str);
    free((*m)->matches);
    free(*m);
  } else {
    (*m)->ref_count--;
  }
}

void COPY(sail_match)(sail_match *m1, sail_match m2)
{
  m2->ref_count++;
  *m1 = m2;
}

void __split(sail_match *result, sail_string regex_str, sail_string str, sail_int nmatches_mpz)
{
  *result = malloc(sizeof(sail_match_t));
  (*result)->ref_count = 0;

  /* Sail string-append patterns match entire strings, so we need to add start and end anchors */
  sail_string regex_anchored;
  regex_anchored = malloc(strlen(regex_str) + 3);
  regex_anchored[0] = '^';
  int i = 0;
  while (i <= strlen(regex_str)) {
    regex_anchored[i + 1] = regex_str[i];
    ++i;
  }
  regex_anchored[i] = '$';
  regex_anchored[i + 1] = '\0';

  regex_t r;
  int err = regcomp(&r, regex_anchored, REG_ICASE | REG_EXTENDED);

  if (err) {
    size_t length = regerror(err, &r, NULL, 0);
    char *buffer = malloc(length);
    regerror(err, &r, buffer, length);
    fprintf(stderr, "Failed to compile regular expression: %s\n", buffer);
    free(buffer);
    exit(1);
  }

  size_t nmatches = mpz_get_ui(nmatches_mpz);
  (*result)->nmatches = nmatches;
  (*result)->matches = malloc(sizeof(regmatch_t) * nmatches);

  err = regexec(&r, str, nmatches, (*result)->matches, 0);
  if (err == REG_ESPACE) {
    fprintf(stderr, "regexec failed with REG_ESPACE");
    exit(1);
  } else if (err == REG_NOMATCH) {
    (*result)->matched = false;
  } else {
    (*result)->matched = true;
  };

  CREATE(sail_string)(&(*result)->str);
  COPY(sail_string)(&(*result)->str, str);

  regfree(&r);
  free(regex_anchored);
}

bool __matched(sail_match m)
{
  return m->matched;
}

void __group(sail_string *result, sail_int group_mpz, sail_match m)
{
  size_t group = mpz_get_ui(group_mpz);

  size_t start = m->matches[group].rm_so;
  size_t end = m->matches[group].rm_eo;

  *result = realloc(*result, ((end - start) + 1) * sizeof(char));

  for (size_t i = start; i < end; i++) {
    (*result)[i - start] = m->str[i];
  }
  (*result)[end - start] = '\0';
}

/**************************************************************************
 * Functions for parsing and pretty printing bitvectors                   *
 **************************************************************************/

void hex_parse(lbits *result, sail_int n, sail_string input)
{
  uint64_t len = mpz_get_ui(n);
  result->len = len;
  gmp_sscanf(input, "0x%Zx", *result->bits);
  normalize_lbits(result);
}

void hex_string(sail_string *result, lbits input)
{
  free(*result);
  gmp_asprintf(result, "0x%ZX", *input.bits);
}

void decimal_parse(lbits *result, sail_int n, sail_string input)
{
  uint64_t len = mpz_get_ui(n);
  result->len = len;
  gmp_sscanf(input, "%Zd", *result->bits);
  normalize_lbits(result);
}

void decimal_string(sail_string *result, lbits input)
{
  free(*result);
  gmp_asprintf(result, "%Zd", *input.bits);
}

void binary_parse(lbits *result, sail_int n, sail_string input)
{
  result->len = mpz_get_ui(n);

  size_t input_length = strlen(input);

  // The string must have "0b" as a prefix, so it must have a length greater than 2
  if (input_length <= 2) {
    fprintf(stderr, "Failed to parse string %s as binary (string too short)", input);
    exit(EXIT_FAILURE);
  } else if (input[0] != '0' || input[1] != 'b') {
    fprintf(stderr, "Failed to parse string %s as binary (missing \"0b\" prefix)", input);
    exit(EXIT_FAILURE);
  }

  // Copy bits from string into result
  for (int i = input_length - 1; i >= 2; --i) {
    char c = input[i];
    if (c == '0') {
      mpz_clrbit(*result->bits, i - 2);
    } else if (c == '1') {
      mpz_setbit(*result->bits, i - 2);
    } else {
      fprintf(stderr, "Failed to parse string %s as binary (unexpected character at index %d)", input, i);
      exit(EXIT_FAILURE);
    }
  }

  normalize_lbits(result);
}

void binary_string(sail_string *result, lbits input)
{
  free(*result);

  sail_string *hex;
  hex = (sail_string *) malloc(sizeof(sail_string *));
  gmp_asprintf(hex, "%ZX", *input.bits);

  int hex_len = strlen(*hex);
  char hex_f = (*hex)[0];
  unsigned int c = hex_f < 58 ? hex_f - 48 : hex_f - 55;

  // We want leading zeros of the empty bitvector to be 3 not 4, so
  // zero-length bitvectors are printed as 0b0 ensuring they are still
  // parseable as a binary string. Note that __builtin_clz is
  // undefined for c == 0.
  unsigned int leading_zeros;
  if (c == 0) {
    leading_zeros = 3;
  } else {
    leading_zeros = __builtin_clz(c) - (sizeof(unsigned int) - sizeof(char)) * 8 - 4;
  }
  *result = (sail_string) malloc((4 * hex_len + 3 - leading_zeros) * sizeof(char));

  (*result)[0] = '0';
  (*result)[1] = 'b';

  int j = 2;

  if (leading_zeros == 0) {
    if ((c & 0x8) == 0x8) {
      (*result)[j] = '1';
    } else {
      (*result)[j] = '0';
    }
    j++;
  }

  if (leading_zeros <= 1) {
    if ((c & 0x4) == 0x4) {
      (*result)[j] = '1';
    } else {
      (*result)[j] = '0';
    }
    j++;
  }

  if (leading_zeros <= 2) {
    if ((c & 0x2) == 0x2) {
      (*result)[j] = '1';
    } else {
      (*result)[j] = '0';
    }
    j++;
  }

  if (leading_zeros <= 3) {
    if ((c & 0x1) == 0x1) {
      (*result)[j] = '1';
    } else {
      (*result)[j] = '0';
    }
    j++;
  }

  for (int i = 1; i < hex_len; i++) {
    c = (*hex)[i] - '0';
    printf("CHAR: %c\n", *hex[i]);

    if (c & 0x8) {
      (*result)[i + j] = '1';
    } else {
      (*result)[i + j] = '0';
    }

    if (c & 0x4) {
      (*result)[i + j] = '1';
    } else {
      (*result)[i + j] = '0';
    }

    if (c & 0x2) {
      (*result)[i + j] = '1';
    } else {
      (*result)[i + j] = '0';
    }

    if (c & 0x1) {
      (*result)[i + j] = '1';
    } else {
      (*result)[i + j] = '0';
    }
  }

  (*result)[4 * hex_len + 2 - leading_zeros] = '\0';

  free(*hex);
  free(hex);
}
