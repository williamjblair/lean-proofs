"""T3 — two-row survivor family analysis (k=11 and k=13 focus, all k reported).

Inputs: artifacts/structure_hunt/t1_surv01_k{k}.csv  (from the T1 scan)
For each {0,1}-survivor (lambda-variant unless noted):
  * u = lambda*d - A;
  * exact gcd g2 = gcd(A+2, lambda^k * G_2); near-miss iff g2 > (A+2)/100;
  * two-divisor / three-divisor decomposition of M=A and M=A+1 over the
    affine terms  T_s(t) = u + lambda*s - (lambda+1)*t;
  * full-term index set: which s have T_s(t) | (A+t)  ("h-pattern"),
    recording h = (A+t)/T_s(t) when it is an integer;
  * rational reconstruction: best rational e/f = A/d with small f (continued
    fraction of A/d), compared against convergents of c(k);
  * small linear relations: integers (e,f,g) with e*A = f*d + g,
    |e|<=40, minimizing |g| (LLL-free brute force; exact).
Decay fit: bin {0,1}-survivor d's into half-decades, fit
    log10(count_per_unit_d) ~ alpha*log10(d) + beta  (least squares, floats
    ONLY in the fit report, never in decision logic).
"""
import csv
import json
import math
import os
import sys
from fractions import Fraction
from math import gcd

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import factorize, c_bounds

ART = "/Users/williamblair/personal/lean-proofs/compute/artifacts"
OUT = os.path.join(ART, "structure_hunt")
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}


def load(k):
    rows = []
    with open(os.path.join(OUT, f"t1_surv01_k{k}.csv")) as f:
        for r in csv.DictReader(f):
            rows.append({kk: int(v) for kk, v in r.items()})
    return rows


def cf_convergents(x: Fraction, depth=25):
    """continued fraction convergents of a positive Fraction."""
    a, b = x.numerator, x.denominator
    out = []
    h0, h1 = 0, 1
    k0, k1 = 1, 0
    while b and len(out) < depth:
        q = a // b
        a, b = b, a - q * b
        h0, h1 = h1, q * h1 + h0
        k0, k1 = k1, q * k1 + k0
        out.append((h1, k1))
    return out


def analyze_k(k, dmin=10 ** 4, dmax=10 ** 6):
    lam = LAMBDA[k]
    lamk = lam ** k
    rows = load(k)
    sel = [r for r in rows if r["p01_lam"] == 1]
    sub = [r for r in sel if dmin <= r["d"] <= dmax]
    report = {"k": k, "lambda": lam, "n_surv01_lam_total": len(sel),
              "n_in_range": len(sub), "range": [dmin, dmax]}

    # --- near-miss fraction on row 2 ---
    near = 0
    g2ratios = []
    fullterm_hist = {}
    hvals_t0 = {}
    recs = []
    for r in sub:
        d, A = r["d"], r["A"]
        u = lam * d - A
        M2 = A + 2
        g = 1 % M2
        for i in range(k):
            g = (g * ((d - 2 + i) % M2)) % M2
        g = (g * (lamk % M2)) % M2
        g2 = gcd(M2, g)          # gcd(A+2, lam^k*G_2) since gcd(M,x)=gcd(M,x mod M)
        ratio = M2 // g2
        g2ratios.append(ratio)
        isnear = g2 * 100 > M2
        near += isnear
        # full-term h-pattern for t=0,1 (and 2)
        fts = {}
        for t in range(3):
            Mt = A + t
            for s in range(k):
                T = u + lam * s - (lam + 1) * t
                if T > 0 and Mt % T == 0:
                    fts.setdefault(t, []).append((s, Mt // T))
        key = tuple((t, tuple(v)) for t, v in sorted(fts.items()))
        fullterm_hist[key] = fullterm_hist.get(key, 0) + 1
        for s, h in fts.get(0, []):
            hvals_t0[h] = hvals_t0.get(h, 0) + 1
        # small linear relation e*A - f*d = g minimal |g| for e<=40
        best = None
        for e in range(1, 41):
            fd = round(e * A / d)
            for f in (fd - 1, fd, fd + 1):
                gg = e * A - f * d
                if best is None or abs(gg) < abs(best[2]):
                    best = (e, f, gg)
        recs.append({"d": d, "A": A, "u": u, "g2_ratio": ratio,
                     "near": bool(isnear), "fullterm": fts,
                     "lin": best, "p012_lam": r["p012_lam"]})
    report["near_miss_count"] = near
    report["near_miss_frac"] = near / len(sub) if sub else None
    report["g2_ratio_hist_small"] = {
        str(v): g2ratios.count(v) for v in sorted(set(g2ratios))[:15]}
    report["fullterm_t0_h_hist"] = dict(sorted(hvals_t0.items()))
    n_with_ft0 = sum(1 for r in recs if 0 in r["fullterm"])
    n_with_ft01 = sum(1 for r in recs if 0 in r["fullterm"]
                      and 1 in r["fullterm"])
    report["n_fullterm_t0"] = n_with_ft0
    report["n_fullterm_t0_and_t1"] = n_with_ft01

    # --- convergents of c(k) vs A/d ---
    c2, c1, _, _ = c_bounds(k, 40)
    conv = cf_convergents((c2 + c1) / 2, 20)
    report["c_convergents"] = conv[:14]
    # how many survivors have A/d exactly equal to a convergent, or d equal
    # to a convergent denominator multiple
    convset = {(p, q) for p, q in conv}
    hits = 0
    for r in recs:
        fr = Fraction(r["A"], r["d"])
        if (fr.numerator, fr.denominator) in convset:
            hits += 1
    report["A_over_d_is_convergent"] = hits

    # --- decay fit over the FULL d-range (all survivors, half-decades) ---
    ds = sorted(r["d"] for r in sel)
    bins = {}
    for d in ds:
        b = int(2 * math.log10(d))
        bins[b] = bins.get(b, 0) + 1
    pts = []
    for b, cnt in sorted(bins.items()):
        lo, hi = 10 ** (b / 2), 10 ** ((b + 1) / 2)
        pts.append((math.log10(math.sqrt(lo * hi)),
                    math.log10(cnt / (hi - lo))))
    # least squares (report only)
    if len(pts) >= 3:
        n = len(pts)
        sx = sum(x for x, _ in pts); sy = sum(y for _, y in pts)
        sxx = sum(x * x for x, _ in pts); sxy = sum(x * y for x, y in pts)
        alpha = (n * sxy - sx * sy) / (n * sxx - sx * sx)
        beta = (sy - alpha * sx) / n
        report["decay_fit"] = {"alpha": round(alpha, 3),
                               "beta": round(beta, 3),
                               "model": "log10(density) = alpha*log10(d)+beta",
                               "points": [(round(x, 2), round(y, 3))
                                          for x, y in pts]}
    report["halfdecade_counts"] = {str(b): c for b, c in sorted(bins.items())}
    return report, recs


def main():
    ks = [int(a) for a in sys.argv[1:]] or [11, 13]
    full = {}
    for k in ks:
        rep, recs = analyze_k(k)
        full[k] = {"report": rep, "records": recs}
        print(json.dumps(rep, indent=1, default=str)[:4000])
        print()
    with open(os.path.join(OUT, "t3_family_analysis.json"), "w") as f:
        json.dump(full, f, indent=1, default=str)
    print("wrote t3_family_analysis.json")


if __name__ == "__main__":
    main()
