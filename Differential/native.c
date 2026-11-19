// Differential test of libc.a's memrchr variants on this CPU: same call, compare rax with __memrchr_sse2's.
// Build and run: bash Differential/native.sh [seed]
#define _GNU_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

typedef char *(*memrchr_fn)(const void *, int, size_t);
char *__memrchr_sse2(const void *, int, size_t);
char *__memrchr_avx2(const void *, int, size_t);
char *__memrchr_evex(const void *, int, size_t);

static const struct { const char *name; memrchr_fn fn; } V[] = {
  {"avx2", __memrchr_avx2}, {"evex", __memrchr_evex},
};
enum { NV = sizeof V / sizeof V[0] };

static uint64_t rng;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static char *map(size_t len) {
  char *p = mmap(0, len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED) { perror("mmap"); exit(2); }
  return p;
}

// One call, each variant against sse2: prints a line per disagreement, returns their number.
static int diff(const char *s, int c, size_t n) {
  char *want = __memrchr_sse2(s, c, n);
  int bad = 0;
  for (int i = 0; i < NV; i++) {
    char *got = V[i].fn(s, c, n);
    if (got == want) continue;
    bad++;
    printf("  DIFF s=%p n=%#zx c=%#x  sse2 -> s%+td  %s -> s%+td\n", (void *)s, n, c & 0xff,
           want ? want - s : -(ptrdiff_t)s, V[i].name, got ? got - s : -(ptrdiff_t)s);
  }
  return bad;
}

int main(int argc, char **argv) {
  rng = argc > 1 ? strtoull(argv[1], 0, 0) : 0x9e3779b97f4a7c15ull;
  printf("seed %#llx\n", (unsigned long long)rng);

  // 1. Small calls: random bytes, objects often ending near a page edge, guard pages on both sides.
  enum { PG = 4096, SPAN = 4 * PG, CALLS = 2000000 };
  char *g = map(SPAN + 2 * PG);
  mprotect(g, PG, PROT_NONE);
  mprotect(g + PG + SPAN, PG, PROT_NONE);
  char *buf = g + PG;
  long smallBad[NV] = {0};
  for (int t = 0; t < CALLS; t++) {
    int dense = t % 32 < 16;  // half the time a 4-letter alphabet, so that matches are dense
    if (t % 16 == 0) {
      for (int i = 0; i < SPAN; i += 8) { uint64_t r = next(); memcpy(buf + i, &r, 8); }
      if (dense) for (int i = 0; i < SPAN; i++) buf[i] &= 3;
    }
    size_t n = next() % 700;
    size_t off = next() % 3 == 0 ? (PG - n % PG + next() % 64) % (SPAN - n) : next() % (SPAN - n);
    // sse2 reads the 16 bytes before s when n = 0 (sse2Reads): keep them mapped.
    if (n == 0 && off < 16) off = 16;
    int c = (int)(next() & (dense ? 3 : 0xff));
    char *ref = __memrchr_sse2(buf + off, c, n);
    for (int i = 0; i < NV; i++) if (V[i].fn(buf + off, c, n) != ref) smallBad[i]++;
  }
  printf("small calls: %d\n", CALLS);
  for (int i = 0; i < NV; i++) printf("  %s: %ld differ from sse2\n", V[i].name, smallBad[i]);

  // 2. The blog's input (s = k*4096 + 1, n = 2^32, last byte = c), and the same shape with other start offsets and
  //    lengths around 2^32.
  size_t big = (1ull << 32) + 3 * PG;
  char *b = map(big);
  char *base = (char *)(((uintptr_t)b + PG - 1) & ~(uintptr_t)(PG - 1));
  int bigBad = 0, bigN = 0;
  printf("large calls (n near 2^32):\n");
  const size_t ns[] = {(1ull << 32) - 1, 1ull << 32, (1ull << 32) + 1, (1ull << 32) + 31};
  const size_t sofs[] = {1, 0, 7, 31, 32, 100};
  for (size_t i = 0; i < sizeof ns / sizeof *ns; i++)
    for (size_t j = 0; j < sizeof sofs / sizeof *sofs; j++) {
      char *s = base + sofs[j];
      size_t n = ns[i];
      if ((size_t)(s - b) + n > big) continue;
      s[n - 1] = 'A';
      bigN++;
      bigBad += diff(s, 'A', n) != 0;
      s[n - 1] = 0;
    }
  printf("  %d of %d large calls differ\n", bigBad, bigN);
  return 0;
}
