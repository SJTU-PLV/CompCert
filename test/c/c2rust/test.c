#include <stdio.h>
int main() {
  int abcd[32];
  abcd[0] = 1;
  abcd[1+2] = 2;
  int n = 3;
  abcd[n] = 3;
  abcd[n+4] = 4;
  abcd[1+2+3] = 100;
  (void)abcd;
  int* a = abcd;
  int* b = abcd + 8;
  int* c = abcd + 16;
  int* d = abcd + 24;
  b[1] = 42;
  c[2] = 43;
  abcd[10] = 100;
  d[3] = 44;
  return 0;
  // printf("hello world\n");
} 