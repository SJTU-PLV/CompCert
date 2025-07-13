#include <stdio.h>
int f1(int a){
return a+1;
}
int main() {
  int a = 0;
  a = f1(a);
  printf("a = %d\n", a);
  return 0;
}