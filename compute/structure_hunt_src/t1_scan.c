/* t1_scan.c — exact small-k Erdos-686 window/row scanner.
 *
 * Point: (d, A) with d >= 221 and A in the exact ratio window, which equals
 *   A in [F-(k-2), F],  F = floor(c_k * d),  c_k = 1/(4^(1/k)-1)
 * (verified exactly in groundwork.py against the bignum window predicate).
 * F is computed from a certified bracket p_lo/2^60 < c_k < (p_lo+1)/2^60:
 * if floor(p_lo*d/2^60) != floor((p_lo+1)*d/2^60) the value of d is written
 * to the .ambig file and skipped (resolved exactly in Python afterwards).
 *
 * ROW(t), t=0,1,2:  (A+t) | FAC * G_t,  G_t = prod_{i=0}^{k-1} (d-t+i),
 * for three slack variants FAC = lambda^k (lambda=q+1), q^k, 1 (raw).
 *
 * Overflow safety: A+2 <= c_k*d + 2 <= 10.34*10^9 + 2 < 2^34 for d <= 10^9,
 * so every (u128)a*b with a,b < M < 2^34 is < 2^68 < 2^127.  lambda^k <=
 * 11^15 < 2^52 fits u64.  p_lo < c_k*2^60 < 2^64; p_lo*d < 2^94 fits u128.
 * All decision arithmetic is exact integer arithmetic.
 *
 * Usage: t1_scan k lambda p_lo d_start d_end out_prefix
 * Writes: out_prefix.counts   (half-decade bucket table)
 *         out_prefix.surv01.csv  (all {0,1}-survivors, any variant)
 *         out_prefix.ambig    (ambiguous d, expected none)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;

/* half-decade bucket: largest b with THRESH[b] <= d ; THRESH[b] = 10^(b/2) */
static u64 THRESH[20];
static int NB = 19; /* buckets 0..18 -> up to 10^9 */

static int bucket_of(u64 d) {
    int b = 0;
    while (b + 1 < NB && THRESH[b + 1] <= d) b++;
    return b;
}

int main(int argc, char **argv) {
    if (argc != 7) {
        fprintf(stderr, "usage: %s k lambda p_lo d_start d_end out_prefix\n",
                argv[0]);
        return 2;
    }
    const int k = atoi(argv[1]);
    const u64 lam = strtoull(argv[2], NULL, 10);
    const u64 p_lo = strtoull(argv[3], NULL, 10);
    const u64 d_start = strtoull(argv[4], NULL, 10);
    const u64 d_end = strtoull(argv[5], NULL, 10);
    const char *pref = argv[6];
    const u64 q = lam - 1;

    /* thresholds 10^(b/2), exact integers: floor for odd b via isqrt */
    for (int b = 0; b < NB; b++) {
        u64 p10 = 1;
        for (int i = 0; i < b / 2; i++) p10 *= 10;
        if (b % 2 == 0) THRESH[b] = p10;
        else {
            /* floor(10^(b/2)) = floor(sqrt(10^b)) computed exactly */
            u128 target = (u128)p10 * p10 * 10;
            u64 r = 1;
            while ((u128)(r + 1) * (r + 1) <= target) {
                u64 step = r;
                while ((u128)(r + step) * (r + step) > target) step /= 2;
                if (!step) break;
                r += step;
            }
            THRESH[b] = r;
        }
    }

    u64 lamk = 1, qk = 1;
    for (int i = 0; i < k; i++) { lamk *= lam; qk *= q; }

    /* counters per bucket */
    u64 cw[20]; memset(cw, 0, sizeof cw);
    u64 c0l[20], c01l[20], c012l[20];
    u64 c0q[20], c01q[20], c012q[20];
    u64 c0r[20], c01r[20], c012r[20];
    memset(c0l,0,sizeof c0l); memset(c01l,0,sizeof c01l); memset(c012l,0,sizeof c012l);
    memset(c0q,0,sizeof c0q); memset(c01q,0,sizeof c01q); memset(c012q,0,sizeof c012q);
    memset(c0r,0,sizeof c0r); memset(c01r,0,sizeof c01r); memset(c012r,0,sizeof c012r);

    char buf[512];
    snprintf(buf, sizeof buf, "%s.surv01.csv", pref);
    FILE *fs = fopen(buf, "w");
    fprintf(fs, "k,d,A,p01_lam,p01_q,p01_raw,p012_lam,p012_q,p012_raw\n");
    snprintf(buf, sizeof buf, "%s.ambig", pref);
    FILE *fa = fopen(buf, "w");

    for (u64 d = d_start; d <= d_end; d++) {
        u64 F_lo = (u64)(((u128)p_lo * d) >> 60);
        u64 F_hi = (u64)(((u128)(p_lo + 1) * d) >> 60);
        if (F_lo != F_hi) { fprintf(fa, "%" PRIu64 "\n", d); continue; }
        const u64 F = F_lo;
        const int b = bucket_of(d);
        for (u64 A = F - (u64)(k - 2); A <= F; A++) {
            cw[b]++;
            /* ROW(0) */
            u64 M = A;
            u64 g = 1;
            for (int i = 0; i < k; i++)
                g = (u64)(((u128)g * ((d + (u64)i) % M)) % M);
            int p0r = (g == 0);
            int p0l = p0r || ((u128)(lamk % M) * g) % M == 0;
            int p0q = p0r || ((u128)(qk % M) * g) % M == 0;
            c0l[b] += p0l; c0q[b] += p0q; c0r[b] += p0r;
            if (!(p0l | p0q)) continue;
            /* ROW(1) */
            M = A + 1;
            g = 1;
            for (int i = 0; i < k; i++)
                g = (u64)(((u128)g * ((d - 1 + (u64)i) % M)) % M);
            int p1r = (g == 0);
            int p1l = p1r || ((u128)(lamk % M) * g) % M == 0;
            int p1q = p1r || ((u128)(qk % M) * g) % M == 0;
            int p01l = p0l & p1l, p01q = p0q & p1q, p01r = p0r & p1r;
            c01l[b] += p01l; c01q[b] += p01q; c01r[b] += p01r;
            if (!(p01l | p01q)) continue;
            /* ROW(2) */
            M = A + 2;
            g = 1;
            for (int i = 0; i < k; i++)
                g = (u64)(((u128)g * ((d - 2 + (u64)i) % M)) % M);
            int p2r = (g == 0);
            int p2l = p2r || ((u128)(lamk % M) * g) % M == 0;
            int p2q = p2r || ((u128)(qk % M) * g) % M == 0;
            int p012l = p01l & p2l, p012q = p01q & p2q, p012r = p01r & p2r;
            c012l[b] += p012l; c012q[b] += p012q; c012r[b] += p012r;
            fprintf(fs, "%d,%" PRIu64 ",%" PRIu64 ",%d,%d,%d,%d,%d,%d\n",
                    k, d, A, p01l, p01q, p01r, p012l, p012q, p012r);
        }
    }
    fclose(fs); fclose(fa);

    snprintf(buf, sizeof buf, "%s.counts", pref);
    FILE *fc = fopen(buf, "w");
    fprintf(fc, "# k=%d lambda=%" PRIu64 " d=[%" PRIu64 ",%" PRIu64 "]\n",
            k, lam, d_start, d_end);
    fprintf(fc, "bucket,lo,window,c0_lam,c01_lam,c012_lam,"
                "c0_q,c01_q,c012_q,c0_raw,c01_raw,c012_raw\n");
    for (int i = 0; i < NB; i++) {
        if (!cw[i]) continue;
        fprintf(fc, "%d,%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64
                ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64
                ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "\n",
                i, THRESH[i], cw[i], c0l[i], c01l[i], c012l[i],
                c0q[i], c01q[i], c012q[i], c0r[i], c01r[i], c012r[i]);
    }
    fclose(fc);
    return 0;
}
