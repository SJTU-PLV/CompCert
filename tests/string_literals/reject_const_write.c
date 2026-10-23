int main(void)
{
  const char *message = "must stay read-only";
  message[0] = 'M';
  return 0;
}
