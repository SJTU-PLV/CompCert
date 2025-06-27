
// #include <stdio.h>
int f(int a){
  int b = a-1;
  if(a>1){
    int c = f(b);
    return a*c;
  } else {
    return 1;
  }
}
int main() {
  int a = 5;
  // a ^= f(a);
  // printf("Factorial of %d is %d\n", a, a);
  return 0;
}