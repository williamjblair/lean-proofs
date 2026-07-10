/* Erdos 686, k=5, N=4: tight-window row scan.
 *
 * For each gap d in [d_lo, d_hi), the exact ratio window forces
 *     A := n+1  to satisfy  A <= c*d <= A+4,   c = 1/(4^(1/5)-1) = 3.12981296...
 * so A ranges over at most 5 consecutive integers.  Row divisibilities:
 *     row j (j=1..5):   A+j-1 | R_j(d) = prod_{i=1..5} (d+i-j).
 * We enumerate the <=6 window candidates (one extra for bracket safety) and
 * report every (d, A) passing rows 1..2 (LEVEL>=2), 1..3 (LEVEL>=3), etc.
 * Upper rows (D+i-1 | 4*U_i(d), D = A+d) are also recorded for hits.
 *
 * Window test uses the exact rational bracket
 *     CLO/10^18 < c < (CLO+1)/10^18,   CLO = 3129812960126669571,
 * verified against the quintic in k5_third_row_derivation.py.  Candidates in
 * the (~1e-8-wide) ambiguous margin are included (over-inclusive is safe).
 *
 * Usage: k5_tight_scan d_lo d_hi [min_level]
 * Output lines: "d A lower_mask upper_mask level"  (masks bit j-1 = row j).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef int64_t i64;

static const u64 CLO = 3129812960126669571ULL; /* floor(c*1e18) */
static const u64 DEN = 1000000000000000000ULL; /* 1e18 */

static inline u64 mulmod(u64 a, u64 b, u64 m) {
    return (u64)(((u128)a * b) % m);
}

/* R_j(d) mod m, j in 1..5, factors d+i-j for i=1..5 (all >=0 for d>=5). */
static inline int row_divides(u64 d, u64 m, int j) {
    u64 x = (d + 1 - j) % m;
    for (int i = 2; i <= 5; i++) {
        x = mulmod(x, (d + i - j) % m, m);
        /* factors are < m whenever m > d+4; keep the % for safety */
    }
    return x == 0;
}

/* upper row i (i=1..5): D+i-1 | 4*U_i(d), U_i(d)=prod_{j=1..5}(d+i-j) */
static inline int upper_row_divides(u64 d, u64 D, int i) {
    u64 m = D + i - 1;
    u64 x = 4 % m;
    for (int j = 1; j <= 5; j++) {
        x = mulmod(x, (d + i - j) % m, m);
    }
    return x == 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s d_lo d_hi [min_level]\n", argv[0]); return 1; }
    u64 d_lo = strtoull(argv[1], 0, 10);
    u64 d_hi = strtoull(argv[2], 0, 10);
    int min_level = (argc > 3) ? atoi(argv[3]) : 2;
    if (d_lo < 5) d_lo = 5;

    u64 count1 = 0, count2 = 0, count3 = 0, count4 = 0, count5 = 0;

    for (u64 d = d_lo; d < d_hi; d++) {
        /* A0 = floor(CLO*d/1e18) <= floor(c*d); floor(c*d) <= A0+1 */
        u64 A0 = (u64)(((u128)CLO * d) / DEN);
        for (u64 A = A0 - 4; A <= A0 + 1; A++) {
            /* exact window test with bracket (inclusive on ambiguity):
               A <= c d  <=  fails only if A*1e18 > (CLO+1)*d
               c d <= A+4 <= fails only if CLO*d > (A+4)*1e18          */
            if ((u128)A * DEN > (u128)(CLO + 1) * d) continue;
            if ((u128)CLO * d > (u128)(A + 4) * DEN) continue;
            if (!row_divides(d, A, 1)) continue;
            count1++;
            if (!row_divides(d, A + 1, 2)) continue;
            int level = 2;
            int lower_mask = 0x3;
            if (row_divides(d, A + 2, 3)) { level = 3; lower_mask |= 0x4;
                if (row_divides(d, A + 3, 4)) { level = 4; lower_mask |= 0x8;
                    if (row_divides(d, A + 4, 5)) { level = 5; lower_mask |= 0x10; }
                }
            } else {
                /* still record rows 4,5 individually for structure mining */
                if (row_divides(d, A + 3, 4)) lower_mask |= 0x8;
                if (row_divides(d, A + 4, 5)) lower_mask |= 0x10;
            }
            count2++;
            if (level >= 3) count3++;
            if (level >= 4) count4++;
            if (level >= 5) count5++;
            if (level >= min_level) {
                u64 D = A + d;
                int upper_mask = 0;
                for (int i = 1; i <= 5; i++)
                    if (upper_row_divides(d, D, i)) upper_mask |= (1 << (i - 1));
                printf("%llu %llu %d %d %d\n",
                       (unsigned long long)d, (unsigned long long)A,
                       lower_mask, upper_mask, level);
            }
        }
    }
    fprintf(stderr, "range [%llu,%llu): L1=%llu L2=%llu L3=%llu L4=%llu L5=%llu\n",
            (unsigned long long)d_lo, (unsigned long long)d_hi,
            (unsigned long long)count1, (unsigned long long)count2,
            (unsigned long long)count3, (unsigned long long)count4,
            (unsigned long long)count5);
    return 0;
}
