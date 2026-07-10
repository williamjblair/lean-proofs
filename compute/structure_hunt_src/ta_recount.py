"""T-A: independent recount of two-row survivors for d <= 10^6, k = 5..15.

Fresh implementation path, sharing NO code with t1_scan.c:
  * window floor F = floor(c_k * d) from the exact Fraction bracket
    c_bounds(k, 50)  (c2 < c_k <= c1); every d asserts floor(c2*d) ==
    floor(c1*d)  (no 2^60 bracket, no p_lo file);
  * window == [F-(k-2), F] cross-checked against the banked bignum
    predicate A_window_interval on a random sample of (k, d);
  * row products evaluated exactly in numpy int64 (all intermediates
    < 2^48: M = A+t < 2^24 for d <= 10^6, factors reduced mod M first);
    rows 1, 2 rechecked in pure-Python bignum on the row-0 survivors.

Outputs ta_recount_report.json: per-k survivor counts + full row-set and
bucket-counter comparison against t1_surv01_k*.csv / t1_counts.json.
Also resolves the two ambiguous-floor d values (k=13) that t1_scan skipped.
"""
import csv
import json
import math
import os
import random
import sys
import multiprocessing as mp

import numpy as np

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import A_window_interval, c_bounds

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}
DMIN, DMAX = 221, 10 ** 6

THRESH = [10 ** (b // 2) if b % 2 == 0 else math.isqrt(10 ** b)
          for b in range(19)]


def scan_k(k):
    lam = LAMBDA[k]
    q = lam - 1
    lamk, qk = lam ** k, q ** k
    c2, c1, _, _ = c_bounds(k, 50)
    n2, d2 = c2.numerator, c2.denominator
    n1, d1 = c1.numerator, c1.denominator

    F_list = [0] * (DMAX - DMIN + 1)
    for idx, d in enumerate(range(DMIN, DMAX + 1)):
        f2 = (n2 * d) // d2
        f1 = (n1 * d) // d1
        assert f2 == f1, f"ambiguous floor k={k} d={d}"
        F_list[idx] = f2

    # window formula vs banked bignum predicate on a random sample
    rng = random.Random(686000 + k)
    for d in [DMIN, DMAX] + [rng.randrange(DMIN, DMAX) for _ in range(60)]:
        F = (n2 * d) // d2
        assert A_window_interval(k, d) == (F - (k - 2), F), (k, d)

    ds = np.arange(DMIN, DMAX + 1, dtype=np.int64)
    F = np.array(F_list, dtype=np.int64)
    bidx = np.searchsorted(np.array(THRESH, dtype=np.int64), ds,
                           side="right") - 1
    nb = 19
    cnt = {name: np.zeros(nb, dtype=np.int64) for name in
           ("w", "c0_lam", "c0_q", "c0_raw")}

    cand = []   # (d, A, p0l, p0q, p0r) for p0l|p0q
    for j in range(k - 1):
        A = F - j
        M = A
        g = np.ones_like(ds)
        for i in range(k):
            g = (g * ((ds + i) % M)) % M
        p0r = g == 0
        p0l = p0r | (((lamk % M) * g) % M == 0)
        p0q = p0r | (((qk % M) * g) % M == 0)
        np.add.at(cnt["w"], bidx, 1)
        np.add.at(cnt["c0_lam"], bidx[p0l], 1)
        np.add.at(cnt["c0_q"], bidx[p0q], 1)
        np.add.at(cnt["c0_raw"], bidx[p0r], 1)
        sel = np.nonzero(p0l | p0q)[0]
        for ii in sel:
            cand.append((int(ds[ii]), int(A[ii]), bool(p0l[ii]),
                         bool(p0q[ii]), bool(p0r[ii])))

    # rows 1, 2 in pure-Python bignum on candidates
    c01 = {v: [0] * nb for v in ("lam", "q", "raw")}
    c012 = {v: [0] * nb for v in ("lam", "q", "raw")}
    surv = []
    for d, A, p0l, p0q, p0r in cand:
        b = 0
        while b + 1 < nb and THRESH[b + 1] <= d:
            b += 1
        G1 = 1
        for i in range(k):
            G1 *= d - 1 + i
        M1 = A + 1
        p1r = G1 % M1 == 0
        p1l = (lamk * G1) % M1 == 0
        p1q = (qk * G1) % M1 == 0
        p01l, p01q, p01r = p0l and p1l, p0q and p1q, p0r and p1r
        c01["lam"][b] += p01l
        c01["q"][b] += p01q
        c01["raw"][b] += p01r
        if not (p01l or p01q):
            continue
        G2 = 1
        for i in range(k):
            G2 *= d - 2 + i
        M2 = A + 2
        p2r = G2 % M2 == 0
        p2l = (lamk * G2) % M2 == 0
        p2q = (qk * G2) % M2 == 0
        p012l, p012q, p012r = p01l and p2l, p01q and p2q, p01r and p2r
        c012["lam"][b] += p012l
        c012["q"][b] += p012q
        c012["raw"][b] += p012r
        surv.append((d, A, int(p01l), int(p01q), int(p01r),
                     int(p012l), int(p012q), int(p012r)))

    counters = {}
    for b in range(nb):
        if cnt["w"][b] == 0:
            continue
        counters[b] = [int(cnt["w"][b]),
                       int(cnt["c0_lam"][b]), c01["lam"][b], c012["lam"][b],
                       int(cnt["c0_q"][b]), c01["q"][b], c012["q"][b],
                       int(cnt["c0_raw"][b]), c01["raw"][b], c012["raw"][b]]
    surv.sort()
    return k, counters, surv


def resolve_ambiguous():
    """The two d values t1_scan skipped as ambiguous (k=13): decide them
    with the full bignum window predicate and exact divisibility."""
    out = []
    k, lam = 13, LAMBDA[13]
    q = lam - 1
    for d in (401710996, 803421992):
        iv = A_window_interval(k, d)
        rec = {"k": k, "d": d, "window": list(iv)}
        pts = []
        for A in range(iv[0], iv[1] + 1):
            flags = {}
            for name, fac in (("lam", lam ** k), ("q", q ** k), ("raw", 1)):
                ps = []
                for t in range(2):
                    G = 1
                    for i in range(k):
                        G *= d - t + i
                    ps.append((fac * G) % (A + t) == 0)
                flags[name] = ps[0] and ps[1]
            if flags["lam"] or flags["q"]:
                pts.append({"A": A, **flags})
        rec["two_row_survivors"] = pts
        out.append(rec)
    return out


def main():
    with mp.Pool(6) as pool:
        results = pool.map(scan_k, sorted(LAMBDA))

    report = {"d_range": [DMIN, DMAX], "per_k": {}, "mismatches": []}
    j = json.load(open(os.path.join(OUT, "t1_counts.json")))
    for k, counters, surv in results:
        # --- survivor-row comparison against the banked CSV ---
        csv_rows = []
        with open(os.path.join(OUT, f"t1_surv01_k{k}.csv")) as f:
            for r in csv.DictReader(f):
                if int(r["d"]) <= DMAX:
                    csv_rows.append((int(r["d"]), int(r["A"]),
                                     int(r["p01_lam"]), int(r["p01_q"]),
                                     int(r["p01_raw"]), int(r["p012_lam"]),
                                     int(r["p012_q"]), int(r["p012_raw"])))
        csv_rows.sort()
        rows_match = csv_rows == surv
        # --- bucket-counter comparison (buckets 4..11 lie in [100, 1e6)) ---
        # my column order: w,c0l,c01l,c012l,c0q,c01q,c012q,c0r,c01r,c012r
        # t1_counts order: window,c0l,c01l,c012l,c0q,c01q,c012q,c0r,c01r,c012r
        cmp_buckets = {}
        counts_match = True
        for b in range(4, 12):
            mine = counters.get(b)
            theirs = j["buckets"][str(k)].get(str(b))
            th = theirs[1:] if theirs else None
            ok = mine == th
            counts_match &= ok
            cmp_buckets[b] = {"mine": mine, "t1_counts": th, "match": ok}
        n01 = {"lam": sum(s[2] for s in surv), "q": sum(s[3] for s in surv),
               "raw": sum(s[4] for s in surv)}
        n012 = {"lam": sum(s[5] for s in surv), "q": sum(s[6] for s in surv),
                "raw": sum(s[7] for s in surv)}
        report["per_k"][k] = {
            "n_surv01_any": len(surv), "n01": n01, "n012": n012,
            "rows_match_csv": rows_match,
            "bucket_counters_match": counts_match,
            "buckets": cmp_buckets,
        }
        if not rows_match:
            report["mismatches"].append(
                {"k": k, "only_mine": [s for s in surv if s not in csv_rows][:20],
                 "only_csv": [s for s in csv_rows if s not in surv][:20]})
        print(f"k={k}: surv01_any={len(surv)} rows_match={rows_match} "
              f"counters_match={counts_match}", flush=True)

    report["ambiguous_d_resolution"] = resolve_ambiguous()
    with open(os.path.join(OUT, "ta_recount_report.json"), "w") as f:
        json.dump(report, f, indent=1)
    print("ambiguous d:", json.dumps(report["ambiguous_d_resolution"],
                                     default=str)[:800])
    all_ok = all(v["rows_match_csv"] and v["bucket_counters_match"]
                 for v in report["per_k"].values())
    print("T-A", "ALL MATCH" if all_ok else "MISMATCH FOUND")


if __name__ == "__main__":
    main()
