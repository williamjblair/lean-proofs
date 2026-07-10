"""T-C: how does row t=2 fail on q-relaxed two-row survivors?

For every (k, d, A) with p01_q = 1 in the t1 CSVs:
    g2    = gcd(A+2, q^k * G_2(d)),  G_2 = prod_{i=0}^{k-1} (d-2+i)
    ratio = (A+2) / g2   (the uncovered part; ratio = 1 <=> row 2 passes)
computed exactly via gcd(M, X mod M).

Baseline for comparison: the SAME statistic on unconditioned window points
(pseudo-random control: for each k, d on a fixed grid, middle-of-window A),
to test whether conditioning on rows 0,1 makes row 2 systematically softer.

Output: tc_row2_gcd.json (per-k distribution of ratios, near-miss fractions,
control distribution).
"""
import csv
import json
import math
import os
from math import gcd

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}


def row_ratio(k, d, A, t, fac):
    M = A + t
    X = fac % M
    for i in range(k):
        X = (X * ((d - t + i) % M)) % M
    g = gcd(M, X)
    return M // g, g


def quantiles(vals):
    if not vals:
        return None
    s = sorted(vals)
    n = len(s)
    return {"min": s[0], "q25": s[n // 4], "median": s[n // 2],
            "q75": s[(3 * n) // 4], "max": s[-1]}


def main():
    report = {}
    for k in sorted(LAMBDA):
        q = LAMBDA[k] - 1
        qk = q ** k
        surv = []
        with open(os.path.join(OUT, f"t1_surv01_k{k}.csv")) as f:
            for r in csv.DictReader(f):
                if int(r["p01_q"]) == 1:
                    surv.append((int(r["d"]), int(r["A"]),
                                 int(r["p012_q"])))
        ratios = []
        passes = 0
        for d, A, p012q in surv:
            ratio, g = row_ratio(k, d, A, 2, qk)
            if ratio == 1:
                passes += 1
                assert p012q == 1, (k, d, A)
            ratios.append((d, A, ratio, g))
        fails = [r for _, _, r, _ in ratios if r > 1]
        gcds = [g for _, _, r, g in ratios if r > 1]
        near100 = sum(1 for r in fails if r <= 100)
        near1000 = sum(1 for r in fails if r <= 1000)
        small_gcd = sum(1 for g in gcds if g <= 10)
        logr = [round(math.log10(r), 2) for r in fails]
        # control: unconditioned window points, same d-scale
        ds = sorted({d for d, _, _ in surv})
        ctrl = []
        if ds:
            import sys
            sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
            from erdos686_exact_core import A_window_interval
            for d0 in ds[:60]:
                iv = A_window_interval(k, d0)
                Amid = (iv[0] + iv[1]) // 2
                r, g = row_ratio(k, d0, Amid, 2, qk)
                ctrl.append((r, g))
        ctrl_fail = [r for r, _ in ctrl if r > 1]
        report[k] = {
            "q": q, "n_two_row_q": len(surv),
            "n_pass_row2": passes,
            "n_fail_row2": len(fails),
            "fail_ratio_quantiles": quantiles(fails),
            "fail_log10ratio_quantiles": quantiles(logr),
            "fail_gcd_quantiles": quantiles(gcds),
            "n_near_miss_ratio<=100": near100,
            "n_near_miss_ratio<=1000": near1000,
            "n_gcd<=10": small_gcd,
            "frac_gcd<=10": round(small_gcd / len(gcds), 4) if gcds else None,
            "control_n": len(ctrl),
            "control_fail_ratio_quantiles": quantiles(ctrl_fail),
            "control_gcd_quantiles": quantiles([g for r, g in ctrl if r > 1]),
        }
        print(f"k={k}: n={len(surv)} pass2={passes} "
              f"near<=100={near100} near<=1000={near1000} "
              f"gcd<=10={small_gcd}/{len(gcds)}", flush=True)
    with open(os.path.join(OUT, "tc_row2_gcd.json"), "w") as f:
        json.dump(report, f, indent=1)
    print("wrote tc_row2_gcd.json")


if __name__ == "__main__":
    main()
