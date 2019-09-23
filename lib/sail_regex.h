#pragma once

#include<regex.h>

#include"sail.h"

bool string_match(sail_string, sail_string);

void hex_parse(lbits *, sail_int, sail_string);
void decimal_parse(lbits *, sail_int, sail_string);
void binary_parse(lbits *, sail_int, sail_string);

void hex_string(sail_string *, lbits);
void decimal_string(sail_string *, lbits);
void binary_string(sail_string *, lbits);
