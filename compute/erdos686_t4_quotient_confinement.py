"""T4 - quotient confinement (Erdos #686, N = 4 branch).

Goal: for each k in 5..15 determine EXACTLY which 4-tuples of row-base
quotients (q_1,q_2,q_3,q_4), q_j = (n+j) // (d+1-j), can occur for a
ratio-window pair with d >= 221 and n >= 1 (A = n+1).

Exact rational linear bounds (all Fractions, no floats):

  Bracket 4^(1/k) between rationals via the integer k-th root
      r = floor((4 * S^k)^(1/k)),  S = 10^30,
  certified by the integer inequalities  r^k <= 4*S^k < (r+1)^k, so
      r/S <= 4^(1/k) < (r+1)/S.
  Set c1 = S/(r-S) and c2 = S/(r+1-S); then c2 < c_k = 1/(4^(1/k)-1) <= c1.

  Window => linear confinement (proof by k-th root monotonicity):
      4*A^k <= (A+d)^k          =>  (r/S)*A <= 4^(1/k)*A <= A+d
                                =>  A <= c1*d
      (A+d+k-1)^k <= 4*(A+k-1)^k => A+d+k-1 < ((r+1)/S)*(A+k-1)
                                =>  A > c2*d - (k-1)
  So every window pair satisfies  c2*d - (k-1) < A <= c1*d  (any d).

  For j = 1..4 the quotient argument rho_j = (A+j-1)/(d+1-j) then satisfies
      (c2*d - (k-1) + (j-1)) / (d+1-j)  <  rho_j  <=  (c1*d + j-1) / (d+1-j).
  Both bounding functions are rational-linear in d; solving the linear
  inequalities exactly (Fractions) yields a threshold D(k) with:
      for all d >= D(k):   q_j = v  for j = 1..4,  v = floor(c1).
  (lower threshold from  c2*d - (k-1) + (j-1) >= v*(d+1-j),  slope c2-v > 0;
   upper threshold from  c1*d + (j-1) <  (v+1)*(d+1-j),      slope v+1-c1 > 0)

  For 221 <= d < D(k) the window A-interval is enumerated exactly (monotone
  integer bisection, endpoints re-verified) and the actual joint tuples are
  collected.  The final exact tuple set for d >= 221 is
      brute tuples on [221, D(k)-1]  UNION  {(v,v,v,v)}.

Verification sweep: brute enumeration over d in 221..max(3000, D(k)) confirms
the collected tuple set and that only (v,v,v,v) occurs at and beyond D(k).

Artifact: compute/artifacts/quotient_confinement.json
"""

import json
import os
import time
from fractions import Fraction

from erdos686_exact_core import c_bounds, A_window_interval, window_A

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")

EXPECTED = {
    5:  {(3, 3, 3, 3)},
    6:  {(3, 3, 3, 3)},
    7:  {(4, 4, 4, 4)},
    8:  {(5, 5, 5, 5)},
    9:  {(5, 6, 6, 6), (6, 6, 6, 6)},
    10: {(6, 6, 6, 6)},
    11: {(7, 7, 7, 7)},
    12: {(8, 8, 8, 8)},
    13: {(8, 8, 8, 8), (8, 8, 8, 9)},
    14: {(9, 9, 9, 9)},
    15: {(10, 10, 10, 10)},
}

BRUTE_SAMPLE_DMAX = 3000


def ceil_frac(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def floor_frac(x: Fraction) -> int:
    return x.numerator // x.denominator


def thresholds_for_k(k: int):
    """Exact per-j thresholds forcing q_j = v for all d >= threshold."""
    c2, c1, r, S = c_bounds(k)
    v = floor_frac(c1)
    assert floor_frac(c2) == v, (
        f"k={k}: c2 and c1 straddle an integer; raise the root precision")
    assert c2 - v > 0 and (v + 1) - c1 > 0
    per_j = {}
    for j in range(1, 5):
        # lower: c2*d - (k-1) + (j-1) >= v*(d+1-j)
        #   <=>  d*(c2 - v) >= v*(1-j) + (k-j)
        rhs_lo = Fraction(v * (1 - j) + (k - j))
        D_lo = max(221, ceil_frac(rhs_lo / (c2 - v)))
        # verify at D_lo (slope positive => holds for all d >= D_lo)
        assert c2 * D_lo - (k - 1) + (j - 1) >= v * (D_lo + 1 - j)
        # upper: c1*d + (j-1) < (v+1)*(d+1-j)
        #   <=>  d*((v+1) - c1) > (j-1)*(v+2)
        rhs_hi = Fraction((j - 1) * (v + 2))
        D_hi = max(221, floor_frac(rhs_hi / ((v + 1) - c1)) + 1)
        assert c1 * D_hi + (j - 1) < (v + 1) * (D_hi + 1 - j)
        per_j[j] = {"D_lower": D_lo, "D_upper": D_hi}
    D = max(max(t["D_lower"], t["D_upper"]) for t in per_j.values())
    return {
        "k": k, "S": S, "r": r,
        "root_bracket_check": (r ** k <= 4 * S ** k < (r + 1) ** k),
        "c1": {"num": c1.numerator, "den": c1.denominator},
        "c2": {"num": c2.numerator, "den": c2.denominator},
        "v": v, "per_j": per_j, "D": D,
    }, c2, c1, v, D


def quotient_tuple(A: int, d: int):
    return tuple((A + j - 1) // (d + 1 - j) for j in range(1, 5))


def brute_tuples(k: int, d_lo: int, d_hi: int, c2: Fraction, c1: Fraction):
    """Exact enumeration of all window pairs (A,d), d in [d_lo,d_hi], with
    their joint quotient tuples.  Also cross-checks the linear confinement
    c2*d - (k-1) < A <= c1*d for every window pair."""
    found = {}
    n_pairs = 0
    for d in range(d_lo, d_hi + 1):
        iv = A_window_interval(k, d)
        if iv is None:
            continue
        for A in range(iv[0], iv[1] + 1):
            assert window_A(k, A, d)
            assert c2 * d - (k - 1) < A <= c1 * d, (
                f"linear confinement violated k={k} d={d} A={A}")
            n_pairs += 1
            qt = quotient_tuple(A, d)
            if qt not in found:
                found[qt] = {"count": 0, "d_min": d, "d_max": d,
                             "example": {"d": d, "A": A, "n": A - 1}}
            found[qt]["count"] += 1
            found[qt]["d_min"] = min(found[qt]["d_min"], d)
            found[qt]["d_max"] = max(found[qt]["d_max"], d)
    return found, n_pairs


def run():
    t0 = time.time()
    os.makedirs(ART, exist_ok=True)
    out = {}
    all_ok = True
    for k in range(5, 16):
        cert, c2, c1, v, D = thresholds_for_k(k)
        d_hi = max(BRUTE_SAMPLE_DMAX, D)
        found, n_pairs = brute_tuples(k, 221, d_hi, c2, c1)
        # exact tuple set for all d >= 221:
        #   brute tuples on [221, D-1]  union  forced tuple (v,v,v,v)
        below = {qt for qt, info in found.items() if info["d_min"] < D}
        # tuples seen at/beyond D must be exactly the forced constant tuple
        beyond = {qt for qt, info in found.items() if info["d_max"] >= D}
        forced = (v, v, v, v)
        assert beyond <= {forced}, (
            f"k={k}: non-constant tuple at d >= D={D}: {beyond}")
        exact_set = below | {forced}
        expected = EXPECTED[k]
        match = exact_set == expected
        all_ok &= match
        out[k] = {
            "certificate": cert,
            "brute_scan": {
                "d_range": [221, d_hi],
                "window_pairs": n_pairs,
                "tuples": [{"tuple": list(qt), **info}
                           for qt, info in sorted(found.items())],
            },
            "forced_tuple_for_d_ge_D": list(forced),
            "exact_tuple_set_d_ge_221": sorted(map(list, exact_set)),
            "expected": sorted(map(list, expected)),
            "matches_expected": match,
        }
        tuples_str = " ".join(str(t) for t in sorted(exact_set))
        print(f"k={k:>2} v={v:>2} D={D:>5} window_pairs(221..{d_hi})={n_pairs:>6} "
              f"tuples={{{tuples_str}}} "
              f"{'OK' if match else 'MISMATCH vs expected ' + str(sorted(expected))}")
        for qt, info in sorted(found.items()):
            if qt != (v, v, v, v):
                print(f"      exceptional {qt}: count={info['count']} "
                      f"d in [{info['d_min']}, {info['d_max']}] "
                      f"example A={info['example']['A']}")

    elapsed = time.time() - t0
    print(f"all k match expected table: {all_ok}")
    print(f"elapsed={elapsed:.2f}s")

    payload = {
        "description": "Exact quotient-confinement certificates: for each k, "
                       "rational bracket r/S <= 4^(1/k) < (r+1)/S certified "
                       "by integer k-th-root inequalities, linear confinement "
                       "c2*d-(k-1) < A <= c1*d for every window pair, per-j "
                       "thresholds D forcing q_j = v for d >= D, and exact "
                       "brute enumeration of joint tuples for 221 <= d < D.",
        "quotient_def": "q_j = (n+j) // (d+1-j), n = A-1, j = 1..4",
        "window": "(A+d+k-1)^k <= 4*(A+k-1)^k and 4*A^k <= (A+d)^k",
        "brute_sample_dmax_at_least": BRUTE_SAMPLE_DMAX,
        "all_match_expected": all_ok,
        "per_k": out,
        "elapsed_seconds": round(elapsed, 3),
    }
    jpath = os.path.join(ART, "quotient_confinement.json")
    with open(jpath, "w") as f:
        json.dump(payload, f, indent=1)
    print(f"wrote {jpath}")
    return out, all_ok


if __name__ == "__main__":
    run()
