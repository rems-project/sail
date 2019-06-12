#include<stdio.h>
#include<string.h>

#include"sail_regex.h"

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
