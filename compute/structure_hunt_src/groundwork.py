"""Groundwork for the structure hunt (exact integer arithmetic only).

1. Verify the exact window characterization:
       window_A(k,A,d)  <=>  floor(c_k*d) - (k-2) <= A <= floor(c_k*d)
   where c_k = 1/(4^(1/k)-1), using the certified rational bracket from
   erdos686_exact_core.c_bounds.

2. Check, on the 45 banked three-row survivors, which slack-factor variant
   of the row condition they satisfy:
       ROW_lam(t): (A+t) | (q+1)^k * G_t      (task statement, lambda = q+1)
       ROW_q(t):   (A+t) | q^k * G_t          (banked residualRowPoly form)
       ROW_raw(t): (A+t) | G_t                (original, no slack)
   with G_t = prod_{i=0}^{k-1} (d-t+i).

3. Emit certified 2^60-scale brackets:
       p_lo(k) = floor(c_k * 2^60)            for k = 5..15
       g_lo(k) = floor((4^(1/k)-1) * 2^60)    for k = 16..3000
   Certification: exact Fraction comparison against a scale-10^40 integer
   k-th-root bracket, asserting  p_lo/2^60 < c_k < (p_lo+1)/2^60  etc.
"""
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import (
    A_window_interval, window_A, c_bounds, integer_kth_root,
)

ART = "/Users/williamblair/personal/lean-proofs/compute/artifacts"
OUT = os.path.join(ART, "structure_hunt")
SCALE = 1 << 60

LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}


def certified_floor_scaled(num_frac_lo: Fraction, num_frac_hi: Fraction,
                           scale: int):
    """floor(x*scale) for irrational x bracketed by lo < x < hi (Fractions).
    Returns p with p/scale < x < (p+1)/scale, certified, or raises."""
    p = (num_frac_lo * scale).__floor__()
    p2 = (num_frac_hi * scale).__floor__()
    assert p == p2, "bracket too wide for this scale; increase precision"
    # certify strictly
    assert Fraction(p, scale) < num_frac_lo, "lower certification failed"
    assert num_frac_hi < Fraction(p + 1, scale), "upper certification failed"
    return p


def c_frac_bracket(k: int, scale_pow: int = 40):
    c2, c1, r, S = c_bounds(k, scale_pow)   # c2 < c_k < c1  (c1 = S/(r-S))
    return c2, c1


def gamma_scaled_certified(k: int) -> int:
    """g = floor((4^(1/k)-1) * 2^60), certified by the exact integer
    inequalities  (2^60+g)^k < 4*2^(60k) < (2^60+g+1)^k  (strict: 4^(1/k)
    is irrational for k >= 2, so equality is impossible).  The initial
    guess comes from decimal floating point and is then corrected/certified
    with exact big-int comparisons only."""
    from decimal import Decimal, getcontext
    getcontext().prec = 50
    S = 1 << 60
    guess = int((Decimal(4) ** (Decimal(1) / k) - 1) * S)
    target = 4 * (1 << (60 * k))
    g = guess
    # correct downward/upward with exact comparisons (at most a step or two)
    while (S + g) ** k >= target:
        g -= 1
    while (S + g + 1) ** k <= target:
        g += 1
    assert (S + g) ** k < target < (S + g + 1) ** k
    return g


def _gamma_worker(k: int):
    return k, gamma_scaled_certified(k)


def main():
    os.makedirs(OUT, exist_ok=True)

    # ---- 1. window characterization ----------------------------------
    print("== window characterization check ==")
    import random
    random.seed(686)
    bad = 0
    for k in range(5, 16):
        c2, c1 = c_frac_bracket(k)
        ds = list(range(221, 400)) + [1000, 5000, 12345, 999983] + \
            [random.randrange(221, 10 ** 8) for _ in range(40)]
        for d in ds:
            F_lo = (c2 * d).__floor__()
            F_hi = (c1 * d).__floor__()
            assert F_lo == F_hi, (k, d)   # bracket decides floor(c*d)
            F = F_lo
            iv = A_window_interval(k, d)
            expect = (F - (k - 2), F)
            if iv != expect:
                bad += 1
                print(f"  MISMATCH k={k} d={d} interval={iv} expected={expect}")
        print(f"  k={k}: window == [floor(c*d)-(k-2), floor(c*d)] on "
              f"{len(ds)} d values OK")
    assert bad == 0

    # ---- 2. slack-variant check on the 45 survivors ------------------
    print("== row-variant check on 45 banked survivors ==")
    surv = json.load(open(os.path.join(ART, "constant_prefix3_survivors.json")))
    rows_report = []
    n_lam_pass = n_q_pass = n_raw_pass = 0
    for s in surv["survivors"]:
        k, q, d, A = s["k"], s["q"], s["d"], s["A"]
        lam = LAMBDA[k]
        assert lam == q + 1
        res = {"k": k, "d": d, "A": A}
        for name, fac in (("lam", lam ** k), ("q", q ** k), ("raw", 1)):
            ok = True
            for t in range(3):
                G = 1
                M = A + t
                for i in range(k):
                    G = (G * ((d - t + i) % M)) % M
                if (fac % M) * G % M != 0:
                    ok = False
                    break
            res[name] = ok
        rows_report.append(res)
        n_lam_pass += res["lam"]
        n_q_pass += res["q"]
        n_raw_pass += res["raw"]
    print(f"  of 45: lam^k-pass={n_lam_pass}  q^k-pass={n_q_pass}  "
          f"raw-pass={n_raw_pass}")
    for r in rows_report:
        if not r["lam"]:
            print(f"  NOT lam-pass: {r}")

    # ---- 3. certified scaled constants -------------------------------
    print("== emitting certified 2^60 constants ==")
    small = {}
    for k in range(5, 16):
        c2, c1 = c_frac_bracket(k)
        p = certified_floor_scaled(c2, c1, SCALE)
        small[k] = p
        # also certify lambda = floor(c)+1
        assert (c2.__floor__() == c1.__floor__())
        assert LAMBDA[k] == c2.__floor__() + 1
    with open(os.path.join(OUT, "c_scaled_small_k.json"), "w") as f:
        json.dump({"scale_log2": 60, "p_lo": small,
                   "lambda": LAMBDA}, f, indent=1)
    print(f"  small k done: {small}")

    import multiprocessing as mp
    with mp.Pool(6) as pool:
        results = pool.map(_gamma_worker, range(16, 3001), chunksize=50)
    results.sort()
    lines = [f"{k} {g}" for k, g in results]
    with open(os.path.join(OUT, "gamma_scaled_large_k.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"  large k done: {len(lines)} entries")
    print("GROUNDWORK OK")


if __name__ == "__main__":
    main()
