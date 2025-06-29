#include <stdio.h>

int main() {
  int a = 2;
  switch(a){
    default:
      a = 4;
    case 1:
      a = 2;
      a = 5;
      break;
    case 2:
      a = 3;
      break;
  }
  printf("a = %d\n", a);
  return 0;
}