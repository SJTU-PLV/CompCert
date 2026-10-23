#include <stdio.h>

int main(void)
{
  char message[] = "mutable array";
  message[0] = 'M';
  printf("%s\n", message);
  return 0;
}
