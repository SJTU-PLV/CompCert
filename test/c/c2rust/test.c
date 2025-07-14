#include <stdio.h>
int f1(int a){
return a+1;
}

int main() {
  int a = 5;
  if (a==0)
    a=2;
  else{
    a = f1(a);
    for(int i=1;i<=5;i++)
      printf("i=%d",i);
  }
  printf("a = %d\n", a);
  return 0;
}