#include <stdio.h>
#include <stdlib.h>
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
  int *a = NULL;
  int c=1;
  scanf("%d", &c);
  if(c==1){
    a = malloc(10 * sizeof(int));
  }
  if(a!=NULL){
    a[0]=0;
    a[1] = 5;
    a[2] = 10;
    a[3] = a[1] + a[2];
    a = a + 1;
    a[1] = 20;
    free(a);
  }
  // int *p = rk + 2;
  // p[1] = 15;
  return 0;
} 