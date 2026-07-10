/* Erdos 686, k=5: scan of the BANKED (loose cone) reduced two-row problem
 *
 *   s >= 13, t >= 95, 4s < 37t, 9t < s + 832, 3 | 23s+t (<=> s == t mod 3),
 *   M = 24s + t,   M | T1(t),   M+1 | T2(t)
 *   T1(t) = t(t+72)(t+144)(t+216)(t+288)
 *   T2(t) = (t-95)(t-23)(t+49)(t+121)(t+193)
 * plus optional deeper rows
 *   T3(t) = (t-190)(t-118)(t-46)(t+26)(t+98)     [M+2]
 *   T4(t) = (t-285)(t-213)(t-141)(t-69)(t+3)     [M+3]
 *   T5(t) = (t-380)(t-308)(t-236)(t-164)(t-92)   [M+4]
 *
 * This is the exact hypothesis set of
 * k_five_exact_reduced_combined_t_product_window / ..._escape in
 * ErdosProblems/Erdos686.lean, extended by rows 3..5.
 *
 * Usage: k5_cone_scan t_lo t_hi [min_level]
 * Output: "t s M level"
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef int64_t i64;

static inline u64 mulmod(u64 a, u64 b, u64 m) {
    return (u64)(((u128)a * b) % m);
}

static const i64 ROOTS[5][5] = {
    {0, 72, 144, 216, 288},
    {-95, -23, 49, 121, 193},
    {-190, -118, -46, 26, 98},
    {-285, -213, -141, -69, 3},
    {-380, -308, -236, -164, -92},
};

static inline int T_divides(i64 t, u64 m, int j) {
    u64 x = 1;
    for (int i = 0; i < 5; i++) {
        i64 f = t + ROOTS[j - 1][i];
        u64 fm = (u64)((f % (i64)m + (i64)m) % (i64)m);
        x = mulmod(x, fm, m);
    }
    return x == 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s t_lo t_hi [min_level]\n", argv[0]); return 1; }
    i64 t_lo = atoll(argv[1]), t_hi = atoll(argv[2]);
    int min_level = (argc > 3) ? atoi(argv[3]) : 2;
    if (t_lo < 95) t_lo = 95;
    u64 c2 = 0, c3 = 0, c4 = 0, c5 = 0;
    for (i64 t = t_lo; t < t_hi; t++) {
        i64 s_min = 9 * t - 832 + 1; if (s_min < 13) s_min = 13;
        i64 s_max = (37 * t - 1) / 4;          /* 4s < 37t */
        /* s == t (mod 3) */
        i64 s0 = s_min + ((t - s_min) % 3 + 3) % 3;
        for (i64 s = s0; s <= s_max; s += 3) {
            u64 M = (u64)(24 * s + t);
            if (!T_divides(t, M, 1)) continue;
            if (!T_divides(t, M + 1, 2)) continue;
            int level = 2;
            if (T_divides(t, M + 2, 3)) { level = 3;
                if (T_divides(t, M + 3, 4)) { level = 4;
                    if (T_divides(t, M + 4, 5)) level = 5;
                }
            }
            c2++;
            if (level >= 3) c3++;
            if (level >= 4) c4++;
            if (level >= 5) c5++;
            if (level >= min_level)
                printf("%lld %lld %llu %d\n", (long long)t, (long long)s,
                       (unsigned long long)M, level);
        }
    }
    fprintf(stderr, "cone range t in [%lld,%lld): L2=%llu L3=%llu L4=%llu L5=%llu\n",
            (long long)t_lo, (long long)t_hi,
            (unsigned long long)c2, (unsigned long long)c3,
            (unsigned long long)c4, (unsigned long long)c5);
    return 0;
}
