#pragma once

#include<regex.h>

#include"sail.h"

typedef regex_t *sail_regex;

typedef regmatch_t *sail_match;

SAIL_BUILTIN_TYPE(sail_regex);

void CONVERT_OF(sail_regex, sail_string)(sail_regex *, sail_string);

bool sail_regmatch(sail_regex, sail_string, sail_match, int);
bool sail_regmatch0(sail_regex, sail_string);

void sail_getmatch(sail_string *, sail_string, sail_match, int, int);
