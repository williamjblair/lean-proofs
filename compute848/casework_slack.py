#!/usr/bin/env python3
"""
Erdos #848, Case 1 (A* contains an even element b).

Baseline (Sothanaphan, Mar 24 2026 note, Case 1):
    |A|/N <= (23/25) C_quad + (2/25) C_{2,5} + 0.001973 + 9.4 N^{-1/4}
main term ~ 0.0376115, slack to 1/25 ~ 0.0023885.

This script asks: how much does splitting A* by its smallest witness prime p
(p = 1 mod 4, p >= 13, p^2 | x^2+1) and sieving each piece against the fixed
even b buy us in the main term, and what does the resulting slack do to the
explicit threshold N0.

Per-prime variants for |A*_p|/N, A*_p = {x in A* : p^2 | x^2+1}
(exactly 2 classes +-t mod p^2, t^2 = -1 mod p^2):

  V0  trivial, no mod-25 use:            2/p^2
  V0b trivial inside the 23/25 frame:    (23/25)(2/p^2)
  V1  Lemma2.2 with q0 = p^2, one class lost:
                                          (1/p^2)(1 + C_{2,p})
  V2  Lemma2.2 with q0 = 25p^2, 46 classes, 24 lost worst case:
                                          (1/(25p^2))(24 + 22 C_{2,5,p})
  V3  bad class trivially inside 23/25, good class sieved with q0 = p^2:
                                          (1/p^2)((23/25) + C_{2,p})

Lemma 2.2 / Corollary 1 hypothesis check for q0 = p^2, class t:
  need p^2 !| (b t + 1).  t^2 = -1 (mod p^2)  =>  t^{-1} = -t, so
  b t + 1 = 0 (mod p^2)  <=>  b = -t^{-1} = t (mod p^2).
  So the hypothesis fails for class t iff b = t (mod p^2), and for class -t
  iff b = -t (mod p^2).  At most ONE of the two classes can be bad (t != -t
  mod p^2 since p is odd and t is a unit), and when it is bad it is genuinely
  unusable: b = t mod p^2 forces ab+1 = t^2+1 = 0 mod p^2 for all a in that
  class.  Hence the honest bound loses exactly one of the two classes.
  For q0 = 25 p^2 the mod-5 half can fail too: 25 | (bt+1) iff t = -b^{-1}
  mod 25, i.e. at most 1 of the 23 admissible classes mod 25; worst-case
  overlap gives 24 bad of 46.

Sieve constants (b even => 2 is excluded from the product; p | q0 => p is
excluded; 5 excluded only when 5 | q0):
  C_{2,p}   = 1 - (6/pi^2) / ((1-1/4)(1-1/p^2))
  C_{2,5,p} = 1 - (6/pi^2) / ((1-1/4)(1-1/25)(1-1/p^2))

Explicit error chain (Sothanaphan):
  Prop 2 (per residue class mod q, q in {25,50}):
    R(1+log R) + 2X(log R + 2)/R + (N^2+1)(1 + log_{2+sqrt3} N)/R^2
  with R = ceil((259/200) N^{2/3}); summed over the 23 admissible classes.
  Corollary 1 (per class): kappa_{q0} N^{3/4}, kappa_25 = 4.7.
"""

import numpy as np
from mpmath import mp, mpf, log, sqrt, pi, floor, ceil

mp.dps = 40

SPLIT_CANDIDATES = [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113]
PLIM = 10**7


# ---------------------------------------------------------------- primes -----
def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


PR = primes_upto(PLIM)
P1MOD4 = [int(p) for p in PR if p % 4 == 1 and p >= 13]


def _full_prod():
    acc = mpf(1)
    for p in P1MOD4:
        acc *= 1 - mpf(2) / (p * p)
    return acc


_TR = _full_prod()
_TAIL_LO = 1 - mpf(2) / (PLIM - 1)  # tail p > PLIM: prod >= 1 - sum 2/p^2


def prod_quad(exclude=()):
    """prod_{p=1(4), p>=13, p not in exclude} (1 - 2/p^2), with rigorous tail."""
    acc = _TR
    for p in set(exclude):
        acc /= 1 - mpf(2) / (p * p)
    return acc * _TAIL_LO, acc  # (lower bound on product, truncated product)


PROD_ALL_LO, PROD_ALL_TR = prod_quad()
C_QUAD = 1 - PROD_ALL_LO

SIX_PI2 = 6 / pi**2
C_25 = 1 - SIX_PI2 / ((1 - mpf(1) / 4) * (1 - mpf(1) / 25))  # C_{2,5}
C_5 = 1 - SIX_PI2 / (1 - mpf(1) / 25)  # C_5


def C_2p(p):
    return 1 - SIX_PI2 / ((1 - mpf(1) / 4) * (1 - mpf(1) / (p * p)))


def C_25p(p):
    return 1 - SIX_PI2 / ((1 - mpf(1) / 4) * (1 - mpf(1) / 25) * (1 - mpf(1) / (p * p)))


# ------------------------------------------------------- per-prime bounds -----
def per_prime(p):
    """Return dict of variant -> density bound for |A*_p|/N (main term only),
    plus the number of Corollary-1 applications (per-class kappa hits)."""
    p2 = mpf(p * p)
    v0 = 2 / p2
    v0b = mpf(23) / 25 * 2 / p2
    v1 = (1 + C_2p(p)) / p2
    v2 = (24 + 22 * C_25p(p)) / (25 * p2)
    v3 = (mpf(23) / 25 + C_2p(p)) / p2
    return {
        "V0 triv 2/p^2": (v0, 0, None),
        "V0b triv (23/25)2/p^2": (v0b, 0, None),
        "V1 q0=p^2": (v1, 1, p * p),
        "V2 q0=25p^2": (v2, 22, 25 * p * p),
        "V3 q0=p^2 + 23/25": (v3, 1, p * p),
    }


VARIANT_ORDER = [
    "V0 triv 2/p^2",
    "V0b triv (23/25)2/p^2",
    "V1 q0=p^2",
    "V2 q0=25p^2",
    "V3 q0=p^2 + 23/25",
]


def best_variant(p, allowed=None):
    d = per_prime(p)
    keys = VARIANT_ORDER if allowed is None else [k for k in VARIANT_ORDER if k in allowed]
    k = min(keys, key=lambda k: d[k][0])
    return k, d[k]


def total_main(S, allowed=None):
    """Case-1 main term for split set S."""
    S = sorted(S)
    pieces = []
    tot = mpf(0)
    for p in S:
        k, (val, nclass, q0) = best_variant(p, allowed)
        pieces.append((p, k, val, nclass, q0))
        tot += val
    prod_rest_lo, _ = prod_quad(exclude=S)
    cq_S = 1 - prod_rest_lo
    tot += mpf(23) / 25 * cq_S
    tot += mpf(2) / 25 * C_25
    return tot, cq_S, pieces


# ------------------------------------------------- explicit error machinery ---
LAM = mpf("6.876")  # Lemma 1 root-count constant
LOG_BASE = log(2 + sqrt(3))


def kappa(q0, N):
    """E_{q0}(N) from Sothanaphan Cor.1 proof, with alpha optimised.
    alpha* = (2 lambda q0^{1/4})^{1/3} minimises alpha + lambda q0^{1/4}/alpha^2."""
    q0 = mpf(q0)
    a = (2 * LAM * q0 ** mpf(0.25)) ** (mpf(1) / 3)
    N = mpf(N)
    return (
        mpf("2.4") / N ** mpf(0.75)
        + a
        + 1 / N ** mpf(0.75)
        + (N / q0 + 1) / (a * N ** mpf(1.5))
        + 1 / (a * sqrt(q0) * N ** mpf(1.5))
        + 2 * LAM * q0 ** mpf(0.25) * (N / q0 + 1) / (a * N ** mpf(1.25))
        + 2 * LAM / (a * q0 ** mpf(0.375) * N ** mpf(1.5))
        + LAM * q0 ** mpf(1.25) * (N / q0 + 1) / (a**2 * N)
        + LAM * q0 ** mpf(0.25) / (a**2 * N**2)
    )


def prop2_density_err(N, q=25, c=None):
    """(1/N) * [R(1+log R) + 2X(log R+2)/R + (N^2+1)(1+log_b N)/R^2] per class,
    returned as the three separate terms.  R = ceil(c N^{2/3}), c=259/200 default."""
    N = mpf(N)
    if c is None:
        c = mpf(259) / 200
    R = floor(mpf(c) * N ** (mpf(2) / 3)) + 1  # upper bound for ceil()
    X = N / q + 1
    t1 = R * (1 + log(R)) / N
    t2 = 2 * X * (log(R) + 2) / (N * R)
    t3 = (N**2 + 1) * (1 + log(N) / LOG_BASE) / (N * R**2)
    return t1, t2, t3


def eps(N, tail_factor=23, S=(), include_split_err=False, allowed=None, optR=False):
    """Total explicit density error in Case 1.
    tail_factor: 23 (as written) or 1 (proposed global-Pell correction).
    optR: re-optimise the constant c in R = ceil(c N^{2/3}) for this tail_factor."""
    if optR:

        def g(cc):
            a, b, d = prop2_density_err(N, 25, cc)
            return 23 * (a + b) + tail_factor * d

        lo, hi = mpf("0.05"), mpf("4")
        for _ in range(60):  # ternary search, g is unimodal in c
            m1 = lo + (hi - lo) / 3
            m2 = hi - (hi - lo) / 3
            if g(m1) < g(m2):
                hi = m2
            else:
                lo = m1
        e = g((lo + hi) / 2)
    else:
        t1, t2, t3 = prop2_density_err(N)
        e = 23 * (t1 + t2) + tail_factor * t3
    e += 2 * kappa(25, N) / mpf(N) ** mpf(0.25)  # A7 u A18, 2 classes mod 25
    if include_split_err:
        for p in S:
            _, (_, nclass, q0) = best_variant(p, allowed)
            if nclass:
                e += nclass * kappa(q0, N) / mpf(N) ** mpf(0.25)
    return e


def _bisect(f, lo=mpf(9), hi=mpf(40)):
    """Smallest N0=10^x with f(10^x) <= 0; f decreasing."""
    if f(mpf(10) ** hi) > 0:
        return None
    if f(mpf(10) ** lo) <= 0:
        return mpf(10) ** lo
    for _ in range(70):
        mid = (lo + hi) / 2
        if f(mpf(10) ** mid) > 0:
            lo = mid
        else:
            hi = mid
    return mpf(10) ** hi


def solve_N0(sigma, tail_factor=23, S=(), include_split_err=False, allowed=None, optR=False):
    return _bisect(lambda N: eps(N, tail_factor, S, include_split_err, allowed, optR) - sigma)


def solve_N0_full(S, allowed=None, tail_factor=23, optR=False):
    """Solve  main_term(S) + eps_with_split_error(N,S) = 1/25  for N."""
    tot, _, _ = total_main(S, allowed)
    return _bisect(lambda N: tot + eps(N, tail_factor, S, True, allowed, optR) - mpf(1) / 25)


# ----------------------------------------------------------------- report -----
def fmt(x, d=7):
    return f"{float(x):.{d}f}"


def sci(x):
    return "n/a" if x is None else f"{float(x):.3e}"


def row(S, allowed=None, split_err=True):
    tot, cq, pieces = total_main(S, allowed)
    sigma = mpf(1) / 25 - tot
    out = {
        "S": sorted(S),
        "total": tot,
        "sigma": sigma,
        "cqS": cq,
        "pieces": pieces,
        "N0_23": solve_N0(sigma, 23),
        "N0_1": solve_N0(sigma, 1),
        "N0_23_full": solve_N0_full(S, allowed, 23),
        "N0_1_full": solve_N0_full(S, allowed, 1),
    }
    return out


def main():
    print("=" * 78)
    print("CONSTANTS")
    print("=" * 78)
    print(f"  C_quad   (1 - prod_{{p=1(4),p>=13}}(1-2/p^2))  = {fmt(C_QUAD, 10)}")
    print(f"     [Sothanaphan Lemma 2: < 0.02734669]")
    print(f"  C_{{2,5}}  = 1 - 25/(3 pi^2)                     = {fmt(C_25, 10)}")
    print(f"  C_5      = 1 - 25/(4 pi^2)                     = {fmt(C_5, 10)}")
    print(f"  (23/25) C_quad                                 = {fmt(mpf(23)/25*C_QUAD, 10)}")
    print(f"  (2/25)  C_{{2,5}}                                = {fmt(mpf(2)/25*C_25, 10)}")
    print()
    print("  per-prime sieve constants (b even):")
    print(f"  {'p':>5} {'C_{2,p}':>12} {'C_{2,5,p}':>12}")
    for p in SPLIT_CANDIDATES:
        print(f"  {p:>5} {fmt(C_2p(p),8):>12} {fmt(C_25p(p),8):>12}")
    print()

    print("=" * 78)
    print("PER-PRIME VARIANT COMPARISON (density bound for |A*_p|/N)")
    print("=" * 78)
    hdr = f"  {'p':>4}" + "".join(f"{k:>24}" for k in VARIANT_ORDER)
    print(hdr)
    for p in SPLIT_CANDIDATES:
        d = per_prime(p)
        line = f"  {p:>4}" + "".join(f"{fmt(d[k][0],9):>24}" for k in VARIANT_ORDER)
        best = min(VARIANT_ORDER, key=lambda k: d[k][0])
        print(line + f"   best={best}")
    print()
    print("  kappa_{q0} at N = 2.64e17 (per Corollary-1 application):")
    print(f"  {'q0':>10} {'kappa':>10}    {'q0':>10} {'kappa':>10}")
    for p in SPLIT_CANDIDATES:
        print(
            f"  {p*p:>10} {fmt(kappa(p*p, mpf('2.64e17')),4):>10}"
            f"    {25*p*p:>10} {fmt(kappa(25*p*p, mpf('2.64e17')),4):>10}"
        )
    print(f"  kappa_25 = {fmt(kappa(25, mpf('2.64e17')),4)}  (paper: 4.7)")
    print()

    print("=" * 78)
    print("ERROR CHAIN SANITY CHECK at N = 2.64e17")
    print("=" * 78)
    Nref = mpf("2.64e17")
    t1, t2, t3 = prop2_density_err(Nref)
    print(f"  23*t1 (R(1+logR)/N)          = {float(23*t1):.6e}")
    print(f"  23*t2 (2X(logR+2)/(NR))      = {float(23*t2):.6e}")
    print(f"  23*t3 (Pell tail)            = {float(23*t3):.6e}")
    print(f"  23*(t1+t2+t3)                = {float(23*(t1+t2+t3)):.6e}   (paper: <1.973e-3)")
    print(f"  2*kappa_25*N^-1/4            = {float(2*kappa(25,Nref)/Nref**mpf(0.25)):.6e}   (paper: 4.15e-4)")
    print(f"  eps(N) 23x                   = {float(eps(Nref,23)):.6e}")
    print(f"  eps(N)  1x                   = {float(eps(Nref,1)):.6e}")
    print(f"  baseline slack               = {float(mpf(1)/25 - (mpf(23)/25*C_QUAD + mpf(2)/25*C_25)):.6e}")
    print()

    # ------------------------------------------------------- greedy search ---
    def greedy(kmax=8, allowed=None):
        S, chain = [], []
        cur, _, _ = total_main(S, allowed)
        chain.append((list(S), cur))
        for _ in range(kmax):
            cands = [p for p in SPLIT_CANDIDATES if p not in S]
            best_p, best_t = None, cur
            for p in cands:
                t, _, _ = total_main(S + [p], allowed)
                if t < best_t:
                    best_p, best_t = p, t
            if best_p is None:
                break
            S.append(best_p)
            cur = best_t
            chain.append((sorted(S), cur))
        return sorted(S), chain

    Sg, chain = greedy(8)
    print("=" * 78)
    print("GREEDY CHAIN (best variant per prime, unrestricted)")
    print("=" * 78)
    for Sx, t in chain:
        print(f"  S={str(Sx):<44} total={fmt(t,8)}  slack={fmt(mpf(1)/25-t,8)}")
    print()

    Sg3, chain3 = greedy(8, allowed={"V0b triv (23/25)2/p^2", "V3 q0=p^2 + 23/25"})
    print("  greedy restricted to V3 (cheap error: 1 Cor-1 application per prime):")
    for Sx, t in chain3:
        print(f"  S={str(Sx):<44} total={fmt(t,8)}  slack={fmt(mpf(1)/25-t,8)}")
    print()

    # -------------------------------------- error-aware greedy (minimise N0) -
    V3ONLY = {"V0b triv (23/25)2/p^2", "V3 q0=p^2 + 23/25"}

    def greedy_N0(kmax=8, allowed=V3ONLY, tail_factor=23):
        S = []
        cur = solve_N0_full(S, allowed, tail_factor)
        chain = [([], cur)]
        for _ in range(kmax):
            best_p, best_v = None, cur
            for p in [q for q in SPLIT_CANDIDATES if q not in S]:
                v = solve_N0_full(S + [p], allowed, tail_factor)
                if v is not None and v < best_v:
                    best_p, best_v = p, v
            if best_p is None:
                break
            S.append(best_p)
            cur = best_v
            chain.append((sorted(S), cur))
        return sorted(S), chain

    Sn23, chain_n23 = greedy_N0(8, V3ONLY, 23)
    print("=" * 78)
    print("ERROR-AWARE GREEDY: minimise the actual N0 (V3 variant, 23x tail)")
    print("=" * 78)
    for Sx, v in chain_n23:
        t, _, _ = total_main(Sx, V3ONLY)
        print(f"  S={str(Sx):<40} main={fmt(t,8)}  N0={sci(v)}")
    Sn1, chain_n1 = greedy_N0(8, V3ONLY, 1)
    print("  same, 1x tail:")
    for Sx, v in chain_n1:
        t, _, _ = total_main(Sx, V3ONLY)
        print(f"  S={str(Sx):<40} main={fmt(t,8)}  N0={sci(v)}")
    print()

    # ------------------------------------------------------------- table ----
    entries = [
        ("{} (sanity)", [], None),
        ("{13}", [13], None),
        ("{13,17}", [13, 17], None),
        ("{13,17,29}", [13, 17, 29], None),
        ("greedy-8 main-term (any)", Sg, None),
        ("{13} V3", [13], V3ONLY),
        ("{13,17} V3", [13, 17], V3ONLY),
        ("{13,17,29} V3", [13, 17, 29], V3ONLY),
        ("greedy-8 main-term (V3)", Sg3, V3ONLY),
        (f"greedy-N0 V3 23x {Sn23}", Sn23, V3ONLY),
        (f"greedy-N0 V3 1x {Sn1}", Sn1, V3ONLY),
    ]
    print("=" * 78)
    print("MAIN TABLE   (+err columns include the extra Corollary-1 cost of splitting)")
    print("=" * 78)
    print(
        f"  {'S':<30}{'main term':>12}{'slack':>12}"
        f"{'N0 (23x)':>12}{'N0 (1x)':>12}{'N0 23x +err':>13}{'N0 1x +err':>13}"
    )
    for lab, S, allowed in entries:
        r = row(S, allowed)
        print(
            f"  {lab:<30}{fmt(r['total'],7):>12}{fmt(r['sigma'],7):>12}"
            f"{sci(r['N0_23']):>12}{sci(r['N0_1']):>12}"
            f"{sci(r['N0_23_full']):>13}{sci(r['N0_1_full']):>13}"
        )
    print()
    print("  chosen variants per prime, greedy-8 (any):")
    _, _, pieces = total_main(Sg)
    for p, k, v, nc, q0 in pieces:
        print(f"    p={p:>4}  {k:<24} bound={fmt(v,9)}  Cor-1 applications={nc} (q0={q0})")
    print()
    print("  chosen variants per prime, greedy-8 (V3 only):")
    _, _, pieces = total_main(Sg3, {"V0b triv (23/25)2/p^2", "V3 q0=p^2 + 23/25"})
    for p, k, v, nc, q0 in pieces:
        print(f"    p={p:>4}  {k:<24} bound={fmt(v,9)}  Cor-1 applications={nc} (q0={q0})")
    print()

    # ------------------------------------------------ floor of the chain ----
    print("=" * 78)
    print("FLOOR OF THE ERROR CHAIN (what N0 is reachable even with sigma = 0.04)")
    print("=" * 78)
    for s in ["0.04", "0.02", "0.012", "0.006", "0.0023885"]:
        print(
            f"  sigma={s:>10}  N0(23x)={sci(solve_N0(mpf(s),23)):>10}"
            f"   N0(1x)={sci(solve_N0(mpf(s),1)):>10}"
        )
    print()
    print("  eps(N) at selected N (23x / 1x / 1x with R re-optimised):")
    for e in [10, 11, 12, 13, 14, 15, 16, 17, 18]:
        N = mpf(10) ** e
        print(
            f"    N=1e{e:<3} eps23={float(eps(N,23)):.4e}   eps1={float(eps(N,1)):.4e}"
            f"   eps1_optR={float(eps(N,1,optR=True)):.4e}"
        )
    print()

    print("=" * 78)
    print("BONUS: R = c N^{2/3} RE-OPTIMISED  (259/200 is tuned for the 23x tail)")
    print("=" * 78)
    for lab, S, allowed in [
        ("{} (baseline)", [], None),
        ("{13} V3", [13], V3ONLY),
        ("{13,17} V3", [13, 17], V3ONLY),
        ("{13,17,29} V3", [13, 17, 29], V3ONLY),
        ("{13,17,29,37} V3", [13, 17, 29, 37], V3ONLY),
        ("greedy-8 main (V3)", Sg3, V3ONLY),
    ]:
        t, _, _ = total_main(S, allowed)
        print(
            f"  {lab:<22} main={fmt(t,7)}  "
            f"N0(23x,optR,+err)={sci(solve_N0_full(S,allowed,23,True))}  "
            f"N0(1x,optR,+err)={sci(solve_N0_full(S,allowed,1,True))}"
        )
    print()
    print("  optimal c in R = c N^{2/3}, at N = 1e16:")
    Nx = mpf(10) ** 16
    for tf in (23, 1):
        lo, hi = mpf("0.05"), mpf("4")

        def g(cc, tf=tf):
            a, b, d = prop2_density_err(Nx, 25, cc)
            return 23 * (a + b) + tf * d

        for _ in range(60):
            m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
            if g(m1) < g(m2):
                hi = m2
            else:
                lo = m1
        print(f"    tail factor {tf:>2}x:  c* = {float((lo+hi)/2):.4f}   (paper c = 1.2950)")
    print()
    print("  ABSOLUTE FLOOR with sigma = 0.04 and R re-optimised:")
    print(f"    23x: N0 = {sci(solve_N0(mpf('0.04'),23,optR=True))}")
    print(f"     1x: N0 = {sci(solve_N0(mpf('0.04'),1,optR=True))}")


if __name__ == "__main__":
    main()
