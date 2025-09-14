#include <stdio.h>
#include <stdlib.h>
int f(int x) {
  return x;
}
int main() {
  // int  *a = (int *)malloc(5 * sizeof(int));
  // for (int i=0;i<5;i++) {
  //   a[i] = i;
  // }
  // for(int i=0;i<5;i++) {
  //   printf("%d\n", a[i]);
  // }
  // f(4);
  // f(5);
  // int c=2;
  int b = f(3);
  printf("%d\n", b);
  return 0;
}