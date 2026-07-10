#!/usr/bin/env python3
"""Erdos 686 constant-quotient prefix-three survivor banding (exact arithmetic).

Selects per-(k,q) rational brackets p1/r1 > 4^(1/k) > p2/r2 (verified exactly),
derives the induced integer u-band  uMin(d) = c2*d/e2 + 1  of width W that any
exact-ratio-window point A = (q+1)d - u (n = A-1) must lie in, and verifies by
exhaustive scan that the banded kernel certificates planned for
ErdosProblems/Erdos686ConstantSurvivors.lean are true:

  for every d in [221, bound(k,q)], i in [0, W):  u := c2*d/e2 + 1 + i,
  if 1 <= u < d and the three residual divisibilities (A+t) | P_t hold for
  t = 0,1,2 (P_t = prod_{s<k} |q*s - (d-u+(q+1)t)|), then (k,q,d,u,A) is in
  the survivor list.

Also handles the u = d top edge (A = q*d): exact window crossover per pair,
bracket-derived Lean caps, and the (9,6) line scan for t=1,2 divisor
coincidences, plus a full u in [1,d] window rescan as a cross-check, and the
row-4 (t=3) escape check for every survivor.
"""

import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")

PAIRS = [(5, 3), (6, 3), (7, 4), (8, 5), (9, 6), (10, 6),
         (11, 7), (12, 8), (13, 8), (14, 9), (15, 10)]
BOUND = {(5, 3): 220, (6, 3): 220, (7, 4): 220, (8, 5): 220, (9, 6): 220,
         (10, 6): 266, (11, 7): 7029, (12, 8): 2695, (13, 8): 4467,
         (14, 9): 2811, (15, 10): 2915}
ACTIVE = [p for p in PAIRS if BOUND[p] > 220]


def below_root(p, r, k):
    """p/r < 4^(1/k)  <=>  p^k < 4 r^k (exact; 4^(1/k) irrational for k>2)."""
    return p ** k < 4 * r ** k


def stern_brocot_brackets(k, dmax):
    """Best fractions below/above 4^(1/k) with denominator <= dmax."""
    lo, hi = (1, 1), (2, 1)
    while True:
        med = (lo[0] + hi[0], lo[1] + hi[1])
        if med[1] > dmax:
            break
        if below_root(med[0], med[1], k):
            lo = med
        else:
            hi = med
    return lo, hi  # lo = (p2, r2) below, hi = (p1, r1) above


def residual_prod(k, q, r):
    p = 1
    for s in range(k):
        p *= abs(q * s - r)
    return p


def window_ok(k, A, d):
    """Exact N=4 ratio window with n = A-1."""
    up = (A + d + k - 1) ** k <= 4 * (A + k - 1) ** k
    lo = 4 * A ** k <= (A + d) ** k
    return up and lo


def residuals_pass(k, q, d, u, tmax=2):
    A = (q + 1) * d - u
    for t in range(tmax + 1):
        r = (d - u) + (q + 1) * t
        if residual_prod(k, q, r) % (A + t) != 0:
            return False
    return True


def load_survivors():
    with open(os.path.join(ART, "constant_prefix3_survivors.json")) as f:
        data = json.load(f)
    return [(s["k"], s["q"], s["d"], s["u"], s["A"]) for s in data["survivors"]]


def main():
    survivors = load_survivors()
    surv_set = set(survivors)
    assert len(survivors) == 45, len(survivors)
    report = {"pairs": {}, "u_eq_d": {}, "problems": []}

    # ---- bracket + band selection for the six active pairs -----------------
    for (k, q) in ACTIVE:
        bound = BOUND[(k, q)]
        # tighten until band width stops improving and stays small
        dmax = 200
        best = None
        while dmax <= 400000:
            (p2, r2), (p1, r1) = stern_brocot_brackets(k, dmax)
            assert below_root(p2, r2, k) and not below_root(p1, r1, k)
            e1, e2 = p1 - r1, p2 - r2
            c1 = (q + 1) * e1 - r1
            c2 = (q + 1) * e2 - r2
            assert c1 > 0 and c2 > 0
            Wmax = 0
            for d in range(221, bound + 1):
                lo = c2 * d // e2 + 1
                hi = c1 * d // e1 + (k - 1)
                Wmax = max(Wmax, hi - lo + 1)
            cand = (Wmax, p1, r1, p2, r2)
            if best is None or Wmax < best[0]:
                best = cand
            if best[0] <= k + 1:
                break
            dmax *= 4
        Wmax, p1, r1, p2, r2 = best
        e1, e2 = p1 - r1, p2 - r2
        c1 = (q + 1) * e1 - r1
        c2 = (q + 1) * e2 - r2
        W = Wmax

        # every artifact survivor of this pair must sit inside the band
        for (kk, qq, d, u, A) in survivors:
            if (kk, qq) != (k, q):
                continue
            lo = c2 * d // e2 + 1
            if not (lo <= u < lo + W):
                report["problems"].append(
                    f"survivor {(k,q,d,u,A)} outside band [{lo},{lo+W})")

        # exhaustive band scan (this is exactly what the Lean cert decides)
        extras = []
        npts = 0
        for d in range(221, bound + 1):
            base = c2 * d // e2 + 1
            for i in range(W):
                u = base + i
                if not (1 <= u < d):
                    continue
                npts += 1
                if residuals_pass(k, q, d, u):
                    A = (q + 1) * d - u
                    if (k, q, d, u, A) not in surv_set:
                        extras.append((k, q, d, u, A))
        report["pairs"][f"{k},{q}"] = {
            "p1": p1, "r1": r1, "p2": p2, "r2": r2,
            "e1": e1, "c1": c1, "e2": e2, "c2": c2, "W": W,
            "band_points": npts, "band_extras": extras,
        }

    # ---- u = d line: exact crossover + bracket caps for all 11 pairs -------
    for (k, q) in PAIRS:
        # exact window feasibility of A = q*d at d >= 221:
        # upper: ((q+1)d + k-1)^k <= 4 (qd + k-1)^k ; lower: 4 q^k <= (q+1)^k
        lower_all = 4 * q ** k <= (q + 1) ** k

        def up_line(d):
            return ((q + 1) * d + k - 1) ** k <= 4 * (q * d + k - 1) ** k

        # largest d with up_line (monotone decreasing truth) by scan/bisect
        lo_d, hi_d = 1, 1
        while up_line(hi_d):
            hi_d *= 2
        while lo_d + 1 < hi_d:
            mid = (lo_d + hi_d) // 2
            if up_line(mid):
                lo_d = mid
            else:
                hi_d = mid
        crossover = lo_d if up_line(lo_d) else 0

        # bracket-derived cap: from r1(n+d+k) < p1(n+k), n = qd-1:
        # d*(r1*(q+1) - p1*q) < (k-1)*(p1-r1)
        dmax = 50
        while True:
            (_, _), (p1, r1) = stern_brocot_brackets(k, dmax)
            m = r1 * (q + 1) - p1 * q
            if m > 0:
                cap = ((k - 1) * (p1 - r1) - 1) // m
                target = 220 if (k, q) != (9, 6) else 1700
                if cap <= max(crossover, 220) + 40 or (cap <= target):
                    break
            dmax *= 4
            if dmax > 10 ** 7:
                raise RuntimeError(f"no cap bracket for {(k,q)}")
        report["u_eq_d"][f"{k},{q}"] = {
            "lower_holds_identically": lower_all,
            "exact_upper_crossover": crossover,
            "cap_bracket": {"p1": p1, "r1": r1, "cap": cap},
        }

    # ---- (9,6) u=d line: t=1,2 divisor scan over [221, cap] ----------------
    info96 = report["u_eq_d"]["9,6"]
    cap96 = info96["cap_bracket"]["cap"]
    C1 = residual_prod(9, 6, 7)
    C2 = residual_prod(9, 6, 14)
    passers = []
    t1_only = []
    for d in range(221, cap96 + 1):
        ok1 = C1 % (6 * d + 1) == 0
        ok2 = C2 % (6 * d + 2) == 0
        if ok1:
            t1_only.append(d)
        if ok1 and ok2:
            passers.append(d)
    info96["C1"] = C1
    info96["C2"] = C2
    info96["t1_passers"] = t1_only
    info96["t1_and_t2_passers"] = passers
    for d in passers:
        # would need window + t3 + row-level checks
        A = 6 * d
        info96.setdefault("passer_detail", []).append({
            "d": d, "window": window_ok(9, A, d),
            "t3": residual_prod(9, 6, 21) % (A + 3) == 0,
        })

    # ---- full u in [1,d] window rescan (coordinator cross-check) -----------
    rescan = {}
    for (k, q) in PAIRS:
        bound = BOUND[(k, q)]
        cross = report["u_eq_d"][f"{k},{q}"]["exact_upper_crossover"]
        dmax = max(bound, cross)
        found = []
        A_hi = None
        for d in range(221, dmax + 1):
            # exact window A-range: Amax = max A with 4A^k <= (A+d)^k
            if A_hi is None:
                A_hi = 1
                while 4 * A_hi ** k <= (A_hi + d) ** k:
                    A_hi *= 2
            while not 4 * A_hi ** k <= (A_hi + d) ** k:
                A_hi -= 1
            while 4 * (A_hi + 1) ** k <= (A_hi + 1 + d) ** k:
                A_hi += 1
            Amax = A_hi
            # Amin = min A with ((A+d+k-1))^k <= 4 (A+k-1)^k (monotone in A)
            lo_a, hi_a = 1, Amax + 1
            while lo_a < hi_a:
                mid = (lo_a + hi_a) // 2
                if (mid + d + k - 1) ** k <= 4 * (mid + k - 1) ** k:
                    hi_a = mid
                else:
                    lo_a = mid + 1
            Amin = lo_a
            for A in range(max(Amin, q * d), min(Amax, (q + 1) * d - 1) + 1):
                u = (q + 1) * d - A
                if not (1 <= u <= d):
                    continue
                if not window_ok(k, A, d):
                    continue
                if residuals_pass(k, q, d, u):
                    found.append((k, q, d, u, A))
        rescan[f"{k},{q}"] = found
    report["rescan"] = {kk: v for kk, v in rescan.items()}

    all_rescan = [t for v in rescan.values() for t in v]
    new_lt = [t for t in all_rescan if t not in surv_set and t[3] < t[2]]
    new_eq = [t for t in all_rescan if t not in surv_set and t[3] == t[2]]
    missing = [t for t in surv_set if t not in set(all_rescan)]
    report["rescan_summary"] = {
        "total": len(all_rescan), "new_u_lt_d": new_lt,
        "new_u_eq_d": new_eq, "artifact_missing": missing,
    }

    # ---- row-4 (t=3) escape for every survivor -----------------------------
    row4_fail = []
    for (k, q, d, u, A) in survivors + new_lt + new_eq:
        r3 = (d - u) + 3 * (q + 1)
        if residual_prod(k, q, r3) % (A + 3) == 0:
            row4_fail.append((k, q, d, u, A))
    report["row4_passers_BAD"] = row4_fail

    # ---- (9,6) gray zone beyond bound: trivial-t0 lines r0 = 6j ------------
    gray = []
    for j in range(0, 20):
        r0 = 6 * j
        # in-window segment of the line A = 6d + r0 (u = d - r0)
        Cline1 = residual_prod(9, 6, r0 + 7)
        Cline2 = residual_prod(9, 6, r0 + 14)
        for d in range(221, 24001):
            u = d - r0
            if u < 1:
                continue
            A = 6 * d + r0
            if not window_ok(9, A, d):
                continue
            if Cline1 % (A + 1) == 0 and Cline2 % (A + 2) == 0:
                gray.append({"d": d, "u": u, "A": A, "r0": r0,
                             "t3": residual_prod(9, 6, r0 + 21) % (A + 3) == 0})
    report["k9_gray_zone_trivial_t0_passers"] = gray

    out = os.path.join(ART, "constant_uband_params.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=1, default=str)
    print(json.dumps({kk: {a: b for a, b in v.items() if a != "band_points"}
                      for kk, v in report["pairs"].items()}, indent=1))
    print("u_eq_d:", json.dumps(report["u_eq_d"], indent=1))
    print("rescan_summary:", json.dumps(report["rescan_summary"], indent=1))
    print("row4_passers_BAD:", row4_fail)
    print("k9_gray:", json.dumps(gray, indent=1))
    print("wrote", out)


if __name__ == "__main__":
    main()
