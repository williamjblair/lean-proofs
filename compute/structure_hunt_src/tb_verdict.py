"""T-B verdict pass: are two-row survivors lines or sporadic coincidences?

Line mechanism: A/d = p'/q' reduced, m = d/q' = gcd-scale.  On such a line
the window pins m <= (k-1)/(q'*c_k - p'), the m-part of A is covered by the
element d itself in row 0, so row 0 degenerates to a congruence on m and only
row 1 stays a ~1/A divisor condition.  Diagnostic: the reduced denominator
q' of A/d.  Small q' at large d = line-structured; q' comparable to d
(gcd(A,d) small) = sporadic coincidence.

Reports, per k:
  * distribution of q' by half-decade of d (medians, fraction q' <= 1000);
  * the structured fraction in the top half-decades;
  * AP structure of m-values within each slope family (common differences);
  * window strip bound (k-1)/delta vs observed max m for each family with
    >= 3 members (exact rational check via c_bounds).
Output: tb_verdict.json
"""
import csv
import json
import os
import sys
from fractions import Fraction
from math import gcd

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import c_bounds

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}


def halfdec(d):
    b = 0
    while 10 ** ((b + 1) / 2) <= d:
        b += 1
    return b


def ap_structure(ms):
    """Describe m-values: full AP? union of APs by common difference?"""
    if len(ms) < 3:
        return {"n": len(ms), "type": "too_few"}
    diffs = [ms[i + 1] - ms[i] for i in range(len(ms) - 1)]
    if len(set(diffs)) == 1:
        return {"n": len(ms), "type": "perfect_AP", "diff": diffs[0],
                "m0": ms[0]}
    g = 0
    for x in diffs:
        g = gcd(g, x)
    residues = sorted({m % g for m in ms}) if g > 1 else None
    return {"n": len(ms), "type": "partial", "diffs": diffs,
            "gcd_of_diffs": g, "residues_mod_gcd": residues}


def main():
    verdict = {}
    for k in sorted(LAMBDA):
        c2, c1, _, _ = c_bounds(k, 60)
        surv = []
        with open(os.path.join(OUT, f"t1_surv01_k{k}.csv")) as f:
            for r in csv.DictReader(f):
                if int(r["p01_q"]) == 1:
                    surv.append((int(r["d"]), int(r["A"]),
                                 int(r["p01_raw"]), int(r["p012_q"])))
        surv.sort()
        perbucket = {}
        slope_map = {}
        for d, A, raw, p3 in surv:
            g = gcd(A, d)
            qp = d // g
            b = halfdec(d)
            perbucket.setdefault(b, []).append(qp)
            slope_map.setdefault((A // g, qp), []).append(d)
        buckets = {}
        for b, qps in sorted(perbucket.items()):
            qps.sort()
            n = len(qps)
            buckets[b] = {
                "n": n, "median_qprime": qps[n // 2],
                "n_qprime<=100": sum(1 for x in qps if x <= 100),
                "n_qprime<=1000": sum(1 for x in qps if x <= 1000),
                "n_qprime<=10000": sum(1 for x in qps if x <= 10000),
            }
        # tail structure: survivors in the top two half-decades
        bmax = max(perbucket)
        tail = [x for b in (bmax, bmax - 1) if b in perbucket
                for x in perbucket[b]]
        tail_frac = (sum(1 for x in tail if x <= 10000) / len(tail)
                     if tail else None)

        fams = []
        for (pp, qp), ds in slope_map.items():
            if len(ds) < 2:
                continue
            ms = sorted(d // qp for d in ds)
            # exact window strip bound: m <= (k-1)/delta, delta = q'c - p'
            dlo = qp * c2 - pp     # rational lower bound on delta
            dhi = qp * c1 - pp
            strip = None
            if dlo > 0:
                strip = int(Fraction(k - 1, 1) / dlo)   # m upper bound
            fams.append({
                "slope": f"{pp}/{qp}", "n": len(ds),
                "m_values": ms, "d_values": sorted(ds),
                "delta_interval": [float(dlo), float(dhi)],
                "window_strip_m_max": strip,
                "ap": ap_structure(ms),
            })
        fams.sort(key=lambda f: -f["n"])
        verdict[k] = {
            "n_q_survivors": len(surv),
            "per_halfdecade": buckets,
            "tail_frac_qprime<=10000": tail_frac,
            "families_ge2": fams,
        }
        top = buckets[bmax]
        print(f"k={k}: tail_structured_frac={tail_frac} "
              f"top_bucket(median_q'={top['median_qprime']}, n={top['n']}, "
              f"<=1e4:{top['n_qprime<=10000']})", flush=True)
    with open(os.path.join(OUT, "tb_verdict.json"), "w") as f:
        json.dump(verdict, f, indent=1)
    print("wrote tb_verdict.json")


if __name__ == "__main__":
    main()
