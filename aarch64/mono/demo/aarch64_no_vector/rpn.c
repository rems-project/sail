#ifndef __aarch64__
#include <stdio.h>
#endif

int main();
void print_char(char c);

#ifdef __aarch64__
void _start() {
  int ret = main();
  // Write EOT to TUBE to exit if running in Sail simulator
  print_char('\x04');
}
#endif

void print_char(char c) {
  #ifdef __aarch64__
  // Move a character to special TUBE memory address
  asm volatile
    ("ldr x1, =0x13000000\n"
     "strb %w[c], [x1]"
     : /* No output */
     : [c] "r" (c)
     : "x1");
  #else
  printf("%c", c);
  #endif
}

void print_string(char *str) {
  int i = 0;
  while (str[i] != 0) {
    print_char(str[i]);
    i++;
  }
}

void print_int(int n) {
  int power = 1;
  while (n / (power * 10) > 0) {
    power = power * 10;
  };

  while (power > 1) {
    int d = n / power;
    print_char(d + '0');
    n = n - (d * power);
    power = power / 10;
  }
  print_char(n + '0');
}

void evaluate(char *expr) {
  int stack[10];
  int top = -1;

  int i = 0;
  int tally = 0;
  while (expr[i] != 0) {
    char c = expr[i];
    if ('0' <= c && c <= '9') {
      int n = c - '0';
      tally = (tally * 10) + n;
    } else if (c == ' ') {
      stack[++top] = tally;
      tally = 0;
    } else if (c == '+') {
      while (top > 0) {
	stack[top - 1] = stack[top] + stack[top - 1];
	top--;
      }
    }
    i++;
  }

  print_int(stack[0]);
  print_char('\n');
}

int main() {
  print_int(321456);
  print_char('\n');
  evaluate("1 12 21 + 100 +");
  //print_string("Hello, World! (from C)\n");
  return 0;
}
