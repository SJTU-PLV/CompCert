#include <stdio.h>
#include <stdlib.h>
typedef unsigned int	u32;
struct Test {
  u32 a;
  u32 b;
};

int main() {
  struct Test* t = (struct Test*)malloc(sizeof(struct Test));
  t->a = 1;
  t->b = 2;
  printf("%d\n", t->a);
  printf("%d\n", t->b);
  free(t);
  return 0;
}