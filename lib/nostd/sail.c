#include <sail_alloc.h>
#include <sail_failure.h>
#include <sail.h>

/* ********************************************************************** */
/* Sail strings                                                           */
/* ********************************************************************** */

/*
 * Implementation is /incredibly/ inefficient... but we don't use
 * strings that much anyway. A better implementation would not use
 * char* due to immutability requirements, but that would make
 * inter-operating with the C world harder.
 */

void CREATE(sail_string)(sail_string *str)
{
     char *istr = (char *) sail_malloc(1 * sizeof(char));
     istr[0] = '\0';
     *str = istr;
}

void RECREATE(sail_string)(sail_string *str)
{
     sail_free(*str);
     char *istr = (char *) sail_malloc(1 * sizeof(char));
     istr[0] = '\0';
     *str = istr;
}

size_t sail_strlen(const sail_string str)
{
     size_t i = 0;
     while (true) {
	  if (str[i] == '\0') {
	       return i;
	  }
	  i++;
     }
}

char *sail_strcpy(char *dest, const char *src)
{
     size_t i;
     for (i = 0; src[i] != '\0'; i++) {
	  dest[i] = src[i];
     }
     dest[i] = '\0';
     return dest;
}

int sail_strcmp(const char *str1, const char *str2)
{
     size_t i = 0;
     while (true) {
	  if (str1[i] == str2[i]) {
	       i++;
	  } else {
	       return str1[i] - str2[i];
	  }
     }
}

char *sail_strcat(char *dest, const char *src)
{
     size_t i = 0;
     while (dest[i] != '\0') {
	  i++;
     }
     return sail_strcpy(dest + i, src);
}

void COPY(sail_string)(sail_string *str1, const sail_string str2)
{
     size_t len = sail_strlen(str2);
     *str1 = sail_realloc(*str1, len + 1);
     *str1 = sail_strcpy(*str1, str2);
}

void KILL(sail_string)(sail_string *str)
{
     sail_free(*str);
}

bool eq_string(const sail_string str1, const sail_string str2)
{
     return sail_strcmp(str1, str2) == 0;
}

bool EQUAL(sail_string)(const sail_string str1, const sail_string str2)
{
     return sail_strcmp(str1, str2) == 0;
}

void undefined_string(sail_string *str, const unit u) {}

void concat_str(sail_string *stro, const sail_string str1, const sail_string str2)
{
     *stro = sail_realloc(*stro, sail_strlen(str1) + sail_strlen(str2) + 1);
     (*stro)[0] = '\0';
     sail_strcat(*stro, str1);
     sail_strcat(*stro, str2);
}

/* ********************************************************************** */
/* Sail integers                                                          */
/* ********************************************************************** */

sail_int CREATE_OF(sail_int, mach_int)(const mach_int op)
{
     return (sail_int) op;
}

mach_int CREATE_OF(mach_int, sail_int)(const sail_int op)
{
     if (MACH_INT_MIN <= op && op <= MACH_INT_MAX) {
          return (mach_int) op;
     } else {
          sail_failure("Lost precision when converting from sail integer to machine integer");
          return -1;
     }
}

mach_int CONVERT_OF(mach_int, sail_int)(const sail_int op)
{
     if (MACH_INT_MIN <= op && op <= MACH_INT_MAX) {
          return (mach_int) op;
     } else {
          sail_failure("Lost precision when converting from sail integer to machine integer");
          return -1;
     }
}

sail_int CONVERT_OF(sail_int, mach_int)(const mach_int op)
{
     return (sail_int) op;
}

bool eq_int(const sail_int op1, const sail_int op2)
{
     return op1 == op2;
}

bool EQUAL(sail_int)(const sail_int op1, const sail_int op2)
{
     return op1 == op2;
}

bool lt(const sail_int op1, const sail_int op2)
{
     return op1 < op2;
}

bool gt(const sail_int op1, const sail_int op2)
{
     return op1 > op2;
}

bool lteq(const sail_int op1, const sail_int op2)
{
     return op1 <= op2;
}

bool gteq(const sail_int op1, const sail_int op2)
{
     return op1 >= op2;
}

// FIXME: Add overflow checks
sail_int shl_int(const sail_int op1, const sail_int op2)
{
     return op1 << op2;
}

mach_int shl_mach_int(const mach_int op1, const mach_int op2)
{
     return op1 << op2;
}

sail_int shr_int(const sail_int op1, const sail_int op2)
{
     return op1 >> op2;
}

mach_int shr_mach_int(const mach_int op1, const mach_int op2)
{
     return op1 >> op2;
}

sail_int undefined_int(const int n)
{
     return (sail_int) n;
}

sail_int undefined_range(const sail_int lower, const sail_int upper)
{
     return lower;
}

sail_int add_int(const sail_int op1, const sail_int op2)
{
     if ((op2 > 0) && (op1 > SAIL_INT_MAX - op2)) {
          sail_failure("Sail integer addition would overflow");
          return -1;
     } else if ((op2 < 0) && (op1 < SAIL_INT_MIN - op2)) {
          sail_failure("Sail integer addition would underflow");
          return -1;
     } else {
          return op1 + op2;
     }
}

sail_int sub_int(const sail_int op1, const sail_int op2)
{
     if ((op2 < 0) && (op1 > SAIL_INT_MAX + op2)) {
          sail_failure("Sail integer subtraction would overflow");
          return -1;
     } else if ((op2 > 0) && (op1 < SAIL_INT_MIN + op2)) {
          sail_failure("Sail integer subtraction would underflow");
          return -1;
     } else {
          return op1 - op2;
     }
}

sail_int sub_nat(const sail_int op1, const sail_int op2)
{
     sail_int rop = sub_int(op1, op2);
     if (rop < 0) {
          return (sail_int) 0;
     } else {
          return rop;
     }
}

sail_int mult_int(const sail_int op1, const sail_int op2)
{
     if (op1 > SAIL_INT_MAX / op2) {
          sail_failure("Sail integer multiplication would overflow");
          return -1;
     } else if (op1 < SAIL_INT_MIN / op2) {
          sail_failure("Sail integer multiplication would underflow");
          return -1;
     } else {
          return op1 * op2;
     }
}

// FIXME: Make all division operators do the right thing with rounding
sail_int ediv_int(const sail_int op1, const sail_int op2)
{
     return op1 / op2;
}

sail_int emod_int(const sail_int op1, const sail_int op2)
{
     return op1 % op2;
}

sail_int tdiv_int(const sail_int op1, const sail_int op2)
{
     return op1 / op2;
}

sail_int tmod_int(const sail_int op1, const sail_int op2)
{
     return op1 % op2;
}

sail_int fdiv_int(const sail_int op1, const sail_int op2)
{
     return op1 / op2;
}

sail_int fmod_int(const sail_int op1, const sail_int op2)
{
     return op1 % op2;
}

sail_int max_int(const sail_int op1, const sail_int op2)
{
     if (op1 < op2) {
          return op2;
     } else {
          return op1;
     }
}

sail_int min_int(const sail_int op1, const sail_int op2)
{
     if (op1 > op2) {
          return op2;
     } else {
          return op1;
     }
}

sail_int neg_int(const sail_int op)
{
     if (op == SAIL_INT_MIN) {
          sail_failure("Sail integer negation would overflow");
          return -1;
     }
     return -op;
}

sail_int abs_int(const sail_int op)
{
     if (op < 0) {
          return neg_int(op);
     } else {
          return op;
     }
}

sail_int pow_int(sail_int base, sail_int exp)
{
     sail_int result = 1;
     while (true)
     {
          if (exp & 1) {
               result *= base;
          }
          exp >>= 1;
          if (!exp) {
               break;
          }
          base *= base;
     }
     return result;
}

sail_int pow2(const sail_int exp)
{
     return pow_int(2, exp);
}

/* ********************************************************************** */
/* Sail bitvectors                                                        */
/* ********************************************************************** */
