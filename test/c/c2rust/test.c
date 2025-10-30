#include <stdio.h>
// void foo(int* abcd) {
//   int* a = abcd + 0;
//   int* b = abcd + 8;
//   int* c = abcd + 16;
//   int* d = abcd + 24;
//   b[1] = 42;
//   abcd[10] = 100;
//   d[3] = 44;
// }
int main() {
  // int abcd[32];
  // abcd[0] = 1;
  // abcd[1+2] = 2;
  // int n = 3;
  // abcd[n] = 3;
  // abcd[n+4] = 4;
  // abcd[1+2+3] = 100;
  // int* a = abcd + 0;
  // int* b = abcd + 8;
  // // foo(abcd);
  // int* c = abcd + 16;
  // int* d = abcd + 24;
  // b[1] = 42;
  // c[2+n] = 43;
  // abcd[10] = 100;
  // d[3] = 44;
  int a[10] = {0};
  int* rk = a;
  rk[1] = 5;
  rk[2] = 10;
  rk[3] = rk[1] + rk[2];
  rk = rk + 1;
  rk[1] = 20;
  // int *p = rk + 2;
  // p[1] = 15;
  return 0;
} 