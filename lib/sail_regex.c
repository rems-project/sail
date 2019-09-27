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
  if (err == REG_ESPACE) {
    fprintf(stderr, "regexec failed with REG_ESPACE");
    exit(1);
  } else if (err == REG_NOMATCH) {
    return false;
  } else {
    return true;
  }
}

/*
void CREATE(sail_regex)(sail_regex *r)
{
  *r = (regex_t *) malloc(sizeof(regex_t));
}

void CONVERT_OF(sail_regex, sail_string)(sail_regex *r, sail_string str)
{
  int err = regcomp(*r, str, REG_ICASE | REG_EXTENDED);
  if (err) {
    size_t length = regerror(err, *r, NULL, 0);
    char *buffer = malloc(length);
    regerror(err, *r, buffer, length);
    fprintf(stderr, "Failed to compile regular expression: %s\n", buffer);
    free(buffer);
    exit(1);
  }
}

void KILL(sail_regex)(sail_regex *r)
{
  regfree(*r);
  free(*r);
}

bool sail_regmatch(sail_regex r, sail_string str, sail_match match, int groups)
{
  int err = regexec(r, str, groups + 1, match, 0);
  if (err == REG_ESPACE) {
    fprintf(stderr, "regexec failed with REG_ESPACE");
    exit(1);
  } else if (err == REG_NOMATCH) {
    return false;
  } else {
    return true;
  }
}

bool sail_regmatch0(sail_regex r, sail_string str)
{
  int err = regexec(r, str, 0, NULL, 0);
  if (err == REG_ESPACE) {
    fprintf(stderr, "regexec failed with REG_ESPACE");
    exit(1);
  } else if (err == REG_NOMATCH) {
    return false;
  } else {
    return true;
  }
}

void sail_getmatch(sail_string *result, sail_string str, sail_match match, int groups, int group)
{
  regmatch_t m = match[group];
  size_t len = m.rm_eo - m.rm_so;
  *result = realloc(*result, len + 1);
  strncpy(*result, str + m.rm_so, len);
  (*result)[len] = '\0';
}
*/

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

  // clz will return length - 1 (i.e. 31 for the 32-bit integer 0)
  // when it's input is zero, which is actually good for us because we
  // want to print 0b0 for an empty bitvector.
  unsigned int leading_zeros = __builtin_clz(c) - (sizeof(unsigned int) - sizeof(char)) * 8 - 4;
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
