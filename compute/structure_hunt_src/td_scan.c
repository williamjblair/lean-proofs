/* td_scan.c — T-D deep-prefix census scanner (extends t4_scan.c).
 *
 * Same conventions as t4_scan.c: point (k, N, d), exact ratio window
 *     d in [ floor(g_k*(N+1)) + 1 , floor(g_k*(N+k)) ],  g_k = 4^(1/k)-1,
 * d >= k required (d < k counted degenerate), pure rows a = 1..18:
 *     (N+a) | prod_{i=1..k} (d+i-a),
 * decided exactly via lpf-sieve factorization of N+a plus Legendre block
 * valuations on [d+1-a, d+k-a].  Row a=0 ((N) | prod(d+i) - 4*k!) is only
 * evaluated for emitted points, by direct modular product.
 *
 * Differences from t4_scan.c:
 *   - kmax up to 6500 (gamma table extended), first-fail tracked to a=18;
 *   - emits ONLY deep survivors: points whose pure rows 1..15 all pass
 *     (first_fail_pure >= 16 or none);
 *   - histogram columns ff1..ff18 + none.
 *
 * Overflow: g_lo < 2^57 (max at k=16), x = N+k <= 3e7+6500 < 2^25, so
 * g_lo*x < 2^82 fits u128.  Row-0: N < 2^25, partial products < 2^50.
 *
 * Usage: td_scan gamma_file kmin kmax Nlo Nhi sievemax out_prefix
 * Writes: out_prefix.deep.csv  (k,N,d,a0_pass,first_fail_pure; ff 0 = none
 *         among a=1..18), out_prefix.hist, out_prefix.ambig
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef uint32_t u32;

#define KMAX 6500
#define AMAX 18

static u32 *lpf;

static void sieve(u32 limit) {
    lpf = calloc((size_t)limit + 1, sizeof(u32));
    if (!lpf) { fprintf(stderr, "sieve alloc failed\n"); exit(2); }
    for (u32 i = 2; i <= limit; i++) {
        if (lpf[i]) continue;
        for (u64 j = i; j <= limit; j += i)
            if (!lpf[j]) lpf[j] = i;
    }
}

typedef struct { u64 p[16]; int e[16]; int n; } Fact;
static void factor(u64 m, Fact *f) {
    f->n = 0;
    while (m > 1) {
        u64 p = lpf[m];
        int e = 0;
        while (m % p == 0) { m /= p; e++; }
        f->p[f->n] = p; f->e[f->n] = e; f->n++;
    }
}

static int block_covers(u64 lo, u64 hi, u64 p, int e) {
    u64 pt = p;
    u64 v = 0;
    for (;;) {
        v += hi / pt - (lo - 1) / pt;
        if (v >= (u64)e) return 1;
        if (pt > hi / p) return 0;
        pt *= p;
    }
}

static int pure_row_pass(const Fact *f, u64 lo, u64 hi) {
    for (int i = 0; i < f->n; i++)
        if (!block_covers(lo, hi, f->p[i], f->e[i])) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 8) {
        fprintf(stderr, "usage: %s gamma_file kmin kmax Nlo Nhi sievemax out_prefix\n", argv[0]);
        return 2;
    }
    const char *gamma_file = argv[1];
    const int kmin = atoi(argv[2]);
    const int kmax = atoi(argv[3]);
    const u64 Nlo = strtoull(argv[4], NULL, 10);
    const u64 Nhi = strtoull(argv[5], NULL, 10);
    const u64 sievemax = strtoull(argv[6], NULL, 10);
    const char *pref = argv[7];
    if (kmax > KMAX) { fprintf(stderr, "kmax > %d\n", KMAX); return 2; }

    static u64 glo[KMAX + 1];
    memset(glo, 0, sizeof glo);
    FILE *fg = fopen(gamma_file, "r");
    if (!fg) { perror("gamma_file"); return 2; }
    { int k; u64 g;
      while (fscanf(fg, "%d %" SCNu64, &k, &g) == 2)
          if (k >= 0 && k <= KMAX) glo[k] = g;
    }
    fclose(fg);
    for (int k = kmin; k <= kmax; k++)
        if (!glo[k]) { fprintf(stderr, "missing gamma k=%d\n", k); return 2; }

    sieve((u32)sievemax);

    char buf[512];
    snprintf(buf, sizeof buf, "%s.deep.csv", pref);
    FILE *fs = fopen(buf, "w");
    fprintf(fs, "k,N,d,a0_pass,first_fail_pure\n");
    snprintf(buf, sizeof buf, "%s.ambig", pref);
    FILE *fa = fopen(buf, "w");

    /* hist[k][a]: first failing pure row a (1..18); slot 19 = none failed */
    static u64 (*hist)[AMAX + 2];
    hist = calloc(KMAX + 1, sizeof *hist);
    u64 degenerate = 0, npoints = 0;

    Fact fc[AMAX + 1];
    int fdone[AMAX + 1];

    for (u64 N = Nlo; N <= Nhi; N++) {
        memset(fdone, 0, sizeof fdone);
        for (int k = kmin; k <= kmax; k++) {
            const u64 g = glo[k];
            u64 x1 = N + 1, x2 = N + (u64)k;
            u64 d1a = (u64)(((u128)g * x1) >> 60);
            u64 d1b = (u64)(((u128)(g + 1) * x1) >> 60);
            u64 d2a = (u64)(((u128)g * x2) >> 60);
            u64 d2b = (u64)(((u128)(g + 1) * x2) >> 60);
            if (d1a != d1b || d2a != d2b) {
                fprintf(fa, "%d %" PRIu64 "\n", k, N);
                continue;
            }
            u64 dlo = d1a + 1, dhi = d2a;
            if (dhi < (u64)k) {
                degenerate += 1;
                break;   /* g_k*(N+k)-k strictly decreasing in k */
            }
            if (dlo < (u64)k) { degenerate += (u64)k - dlo; dlo = (u64)k; }
            for (u64 d = dlo; d <= dhi; d++) {
                npoints++;
                int ff = 0;   /* first failing pure row, 0 = none in 1..18 */
                for (int a = 1; a <= AMAX; a++) {
                    if (!fdone[a]) { factor(N + (u64)a, &fc[a]); fdone[a] = 1; }
                    u64 lo = d + 1 - (u64)a, hi = d + (u64)k - (u64)a;
                    if (!pure_row_pass(&fc[a], lo, hi)) { ff = a; break; }
                }
                hist[k][ff ? ff : AMAX + 1]++;
                if (ff >= 1 && ff <= 15) continue;
                /* deep survivor: pure rows 1..15 all pass -> row 0 + emit */
                u64 pm = 1 % N, fm = 1 % N;
                for (u64 i = 1; i <= (u64)k; i++) {
                    pm = (pm * ((d + i) % N)) % N;
                    fm = (fm * (i % N)) % N;
                }
                int a0 = ((pm + 4 * N - (4 * fm) % N) % N) == 0;
                fprintf(fs, "%d,%" PRIu64 ",%" PRIu64 ",%d,%d\n",
                        k, N, d, a0, ff);
            }
        }
    }
    fclose(fs); fclose(fa);

    snprintf(buf, sizeof buf, "%s.hist", pref);
    FILE *fh = fopen(buf, "w");
    fprintf(fh, "# npoints=%" PRIu64 " degenerate_skipped=%" PRIu64
            " N=[%" PRIu64 ",%" PRIu64 "] k=[%d,%d]\n",
            npoints, degenerate, Nlo, Nhi, kmin, kmax);
    fprintf(fh, "k");
    for (int a = 1; a <= AMAX; a++) fprintf(fh, ",ff%d", a);
    fprintf(fh, ",none\n");
    for (int k = kmin; k <= kmax; k++) {
        u64 s = 0;
        for (int a = 1; a <= AMAX + 1; a++) s += hist[k][a];
        if (!s) continue;
        fprintf(fh, "%d", k);
        for (int a = 1; a <= AMAX + 1; a++)
            fprintf(fh, ",%" PRIu64, hist[k][a]);
        fprintf(fh, "\n");
    }
    fclose(fh);
    return 0;
}
