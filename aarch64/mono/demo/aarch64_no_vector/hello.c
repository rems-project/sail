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

void print_string(char *str)
{
  int i = 0;
  while (str[i] != 0)
  {
    print_char(str[i]);
    i++;
  }
}

int main()
{
  print_string("Hello, World! (from C)\n");
  return 0;
}
