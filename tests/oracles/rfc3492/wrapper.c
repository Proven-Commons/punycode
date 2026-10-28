/*
  The RFC 3492 oracle for tests/run_tests.py: the sample
  implementation of appendix C (punycode.c, the library part,
  unchanged), driven line by line.

    e HEX,HEX,...   encode the code points, given in hex (- for none)
    d HEX           decode the bytes, given in hex

  Each answer is "OK " and the output (the Punycode string as hex
  bytes, or the code points as hex joined by ","), or "ERR " and the
  punycode_status value. The case flags are not used.
*/

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum punycode_status {
  punycode_success,
  punycode_bad_input,
  punycode_big_output,
  punycode_overflow
};
#if UINT_MAX >= (1 << 26) - 1
typedef unsigned int punycode_uint;
#else
typedef unsigned long punycode_uint;
#endif
enum punycode_status punycode_encode(punycode_uint, const punycode_uint [],
  const unsigned char [], punycode_uint *, char []);
enum punycode_status punycode_decode(punycode_uint, const char [],
  punycode_uint *, punycode_uint [], unsigned char []);

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

int main(void) {
  static char line[1 << 22];
  while (fgets(line, sizeof line, stdin)) {
    size_t n = strlen(line);
    while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
    if (n >= 2 && line[0] == 'e' && line[1] == ' ') {
      const char *p = line + 2;
      size_t cap = n, len = 0;
      punycode_uint *in = malloc((cap + 1) * sizeof *in);
      if (strcmp(p, "-") != 0) {
        while (*p) {
          in[len++] = (punycode_uint) strtoul(p, (char **) &p, 16);
          if (*p == ',') ++p;
        }
      }
      punycode_uint outlen = 16 * len + 64;
      char *out = malloc(outlen);
      enum punycode_status st = punycode_encode(len, in, NULL, &outlen, out);
      if (st == punycode_success) {
        fputs("OK ", stdout);
        for (punycode_uint j = 0; j < outlen; ++j) printf("%02x", (unsigned char) out[j]);
        putchar('\n');
      } else printf("ERR %d\n", st);
      free(in); free(out);
    } else if (n >= 2 && line[0] == 'd' && line[1] == ' ') {
      size_t hl = n - 2, bl = hl / 2;
      char *in = malloc(bl + 1);
      for (size_t j = 0; j < bl; ++j)
        in[j] = (char) (hexval(line[2 + 2 * j]) * 16 + hexval(line[3 + 2 * j]));
      punycode_uint outlen = bl + 1;
      punycode_uint *out = malloc((outlen + 1) * sizeof *out);
      enum punycode_status st = punycode_decode(bl, in, &outlen, out, NULL);
      if (st == punycode_success) {
        fputs("OK ", stdout);
        for (punycode_uint j = 0; j < outlen; ++j) printf(j ? ",%x" : "%x", (unsigned) out[j]);
        putchar('\n');
      } else printf("ERR %d\n", st);
      free(in); free(out);
    } else puts("error");
    fflush(stdout);
  }
  return 0;
}
