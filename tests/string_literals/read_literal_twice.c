#include <stdio.h>

int main(void)
{
  const char *first = "shared literal";
  const char *second = "shared literal";
  printf("%s / %s\n", first, second);
  return 0;
}
