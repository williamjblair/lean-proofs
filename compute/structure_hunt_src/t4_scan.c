/* t4_scan.c — exact large-k Erdos-686 row-prefix scanner.
 *
 * Convention (matches erdos686_prefix_counterexamples.py): a point is
 * (k, N, d) with the exact ratio window
 *     (N+d+k)^k <= 4*(N+k)^k   and   4*(N+1)^k <= (N+d+1)^k
 * which (exactly, by the same monotone k-th-root argument as small k) is
 *     d in [ floor(g_k*(N+1)) + 1 , floor(g_k*(N+k)) ],  g_k = 4^(1/k)-1.
 * (task-n = N-1; task row j = script row a = j-1.)
 * Rows a = 0..16:  (N+a) | H_{k,d}(a),
 *     H(a) = prod_{i=1..k} (d+i-a) - 4*k!*[a==0]   (pure product for a>=1).
 * Pure rows are decided EXACTLY via prime factorization of N+a (lpf sieve)
 * plus Legendre-style valuations of the k-consecutive block [d+1-a, d+k-a]:
 *     v_p(block) = sum_t ( floor(hi/p^t) - floor((lo-1)/p^t) ).
 * Row a=0 is decided by direct modular product (only evaluated when pure
 * rows 1..7 all pass).
 *
 * Only points with d >= k are scanned (d < k is counted as degenerate; the
 * k-loop break uses the strict monotone decrease of g_k*(N+k) - k in k;
 * every emitted point is still verified by the exact d >= k test).
 *
 * floor(g_k*x) uses the certified bracket g_lo/2^60 < g_k < (g_lo+1)/2^60
 * (groundwork.py); ambiguous floors go to the .ambig file (expected none).
 *
 * Overflow: g_lo < 2^57, x <= 1e7+3000 -> products < 2^81 fit u128.
 * Valuations use u64 only.  Row-0 product: N < 2^24, factors < 2^21.
 *
 * Usage: t4_scan gamma_file kmin kmax Nlo Nhi sievemax out_prefix
 * Writes: out_prefix.surv.csv  (points with pure rows 1..7 all passing)
 *         out_prefix.hist      (per-k first-fail-pure histogram, a=1..8+)
 *         out_prefix.ambig
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef uint32_t u32;

static u32 *lpf;      /* lpf[x] = least prime factor (0,1 -> 0) */

static void sieve(u32 limit) {
    lpf = calloc((size_t)limit + 1, sizeof(u32));
    for (u32 i = 2; i <= limit; i++) {
        if (lpf[i]) continue;
        for (u64 j = i; j <= limit; j += i)
            if (!lpf[j]) lpf[j] = i;
    }
}

/* factor m (>=2) into prime powers via lpf sieve */
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

/* v_p(prod of block [lo,hi]) >= e ?  exact Legendre sums, early success */
static int block_covers(u64 lo, u64 hi, u64 p, int e) {
    u64 pt = p;
    u64 v = 0;
    for (;;) {
        v += hi / pt - (lo - 1) / pt;
        if (v >= (u64)e) return 1;
        if (pt > hi / p) return 0;   /* next power exceeds hi */
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

    static u64 glo[3001];
    memset(glo, 0, sizeof glo);
    FILE *fg = fopen(gamma_file, "r");
    if (!fg) { perror("gamma_file"); return 2; }
    { int k; u64 g;
      while (fscanf(fg, "%d %" SCNu64, &k, &g) == 2)
          if (k >= 0 && k <= 3000) glo[k] = g;
    }
    fclose(fg);
    for (int k = kmin; k <= kmax; k++)
        if (!glo[k]) { fprintf(stderr, "missing gamma k=%d\n", k); return 2; }

    sieve((u32)sievemax);

    char buf[512];
    snprintf(buf, sizeof buf, "%s.surv.csv", pref);
    FILE *fs = fopen(buf, "w");
    fprintf(fs, "k,N,d,a0_pass,first_fail_pure,P_N15,cap15\n");
    snprintf(buf, sizeof buf, "%s.ambig", pref);
    FILE *fa = fopen(buf, "w");

    /* hist[k][a]: first failing pure row a (1..16), 0 slot = none failed */
    static u64 hist[3001][18];
    memset(hist, 0, sizeof hist);
    u64 degenerate = 0, npoints = 0;

    Fact fc[17];
    int fdone[17];

    for (u64 N = Nlo; N <= Nhi; N++) {
        memset(fdone, 0, sizeof fdone);
        for (int k = kmin; k <= kmax; k++) {
            const u64 g = glo[k];
            /* d window */
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
                /* g_k*(N+k)-k strictly decreases in k: all larger k are
                 * degenerate too (each would fail the same exact test) */
                degenerate += 1;
                break;
            }
            if (dlo < (u64)k) { degenerate += (u64)k - dlo; dlo = (u64)k; }
            for (u64 d = dlo; d <= dhi; d++) {
                npoints++;
                int ff = 0;   /* first failing pure row, 0 = none in 1..16 */
                for (int a = 1; a <= 16; a++) {
                    if (!fdone[a]) { factor(N + (u64)a, &fc[a]); fdone[a] = 1; }
                    u64 lo = d + 1 - (u64)a, hi = d + (u64)k - (u64)a;
                    if (!pure_row_pass(&fc[a], lo, hi)) { ff = a; break; }
                }
                if (ff >= 1 && ff <= 7) { hist[k][ff]++; continue; }
                hist[k][ff ? ff : 17]++;
                /* pure rows 1..7 passed: evaluate row a=0 directly */
                u64 pm = 1 % N, fm = 1 % N;
                for (u64 i = 1; i <= (u64)k; i++) {
                    pm = (pm * ((d + i) % N)) % N;
                    fm = (fm * (i % N)) % N;
                }
                int a0 = ((pm + 4 * N - (4 * fm) % N) % N) == 0;
                /* P(N+15) and cap d+k-15 for the boundary-route stat */
                u64 m = N + 15, P = 1;
                while (m > 1) { u64 p = lpf[m]; P = p > P ? p : P;
                                while (m % p == 0) m /= p; }
                fprintf(fs, "%d,%" PRIu64 ",%" PRIu64 ",%d,%d,%" PRIu64
                        ",%" PRIu64 "\n",
                        k, N, d, a0, ff ? ff : 17, P, d + (u64)k - 15);
            }
        }
    }
    fclose(fs); fclose(fa);

    snprintf(buf, sizeof buf, "%s.hist", pref);
    FILE *fh = fopen(buf, "w");
    fprintf(fh, "# npoints=%" PRIu64 " degenerate_skipped=%" PRIu64
            " N=[%" PRIu64 ",%" PRIu64 "] k=[%d,%d]\n",
            npoints, degenerate, Nlo, Nhi, kmin, kmax);
    fprintf(fh, "k,ff1,ff2,ff3,ff4,ff5,ff6,ff7,ff8,ff9,ff10,ff11,ff12,"
                "ff13,ff14,ff15,ff16,none\n");
    for (int k = kmin; k <= kmax; k++) {
        u64 s = 0;
        for (int a = 1; a <= 17; a++) s += hist[k][a];
        if (!s) continue;
        fprintf(fh, "%d", k);
        for (int a = 1; a <= 17; a++) fprintf(fh, ",%" PRIu64, hist[k][a]);
        fprintf(fh, "\n");
    }
    fclose(fh);
    return 0;
}
