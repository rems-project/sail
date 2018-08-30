#include "sail.h"
#include "rts.h"

void string_append(sail_string *dst, sail_string s1, sail_string s2);
bool string_startswith(sail_string s, sail_string prefix);
void string_length(sail_int *len, sail_string s);
void string_drop(sail_string *dst, sail_string s, sail_int len);
unit print_string(sail_string prefix, sail_string msg);

void add_vec(sail_bits *dst, sail_bits s1, sail_bits s2);
void add_vec_int(sail_bits *dst, sail_bits src, sail_int i);

void sub_vec(sail_bits *dst, sail_bits s1, sail_bits s2);
void sub_vec_int(sail_bits *dst, sail_bits src, sail_int i);

void not_vec(sail_bits *dst, sail_bits src);
void xor_vec(sail_bits *dst, sail_bits s1, sail_bits s2);


