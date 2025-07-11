#include <stdio.h>

int main() {
  int a = 0;
  switch(a){
    case 1:
      a = 2;
      a = 5;
    default:
      a = 4;
      break;
    case 2:
      a = 3;
      break;
  }
  printf("a = %d\n", a);
  return 0;
}