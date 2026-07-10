#!/usr/bin/env python3
"""
Erdos 686, k=15, N=4: exact continued fraction of 4^(1/15) + quasi-convergent
candidate scan to Y <= 10^100.

Companion to derivation.py, which proves (exact rational certificates):
  every solution of P(X) = 4 P(Y), P(T) = T*prod_{j=1..7}(T^2-j^2),
  with Y = n+8 >= Y0 = 2131 (forced by d >= 221; d <= 220 is banked) obeys

     |X^15 - 4 Y^15| <= C_A * Y^13,   C_A ~ 94.5223  (exact rational), and
     |4^(1/15) - X/Y| <= C15 / Y^2,   C15 = 1729/1000.

Confinement class (C15 > 1 > 1/2: beyond Legendre AND beyond Fatou):
  write X/Y = g*(a/b) in lowest terms.
  - g >= 2:  |alpha - a/b| < C15/(g^2 b^2) <= (C15/4)/b^2 < 1/(2b^2), so by
    LEGENDRE (in Mathlib: Real.exists_rat_eq_convergent) a/b is a convergent
    p_m/q_m; the classical lower bound |alpha - p_m/q_m| > 1/(q_m(q_{m+1}+q_m))
    bounds g:  g^2 < C15*(q_{m+1}+q_m)/q_m  (per-index, exact).
  - g == 1:  by WORLEY's theorem [Worley 1981, J. Austral. Math. Soc. 32;
    Dujella 2004]:  |alpha - a/b| < C/b^2  ==>
        (a,b) = (r*p_{m+1} +- s*p_m,  r*q_{m+1} +- s*q_m),
    m >= -1, r,s >= 0 integers with r*s < 2C = 3.458, i.e. r*s <= 3:
        (r,s) in {(1,0),(0,1)} (convergents) or
        {(1,1),(1,2),(2,1),(1,3),(3,1)} x {+,-}   (quasi-convergents).

This script (ALL decision logic exact integer/Fraction):
  1. computes cf(4^(1/15)) to >= 335 terms EXACTLY: a 10^-480 rational
     sandwich via integer 15th roots, CF of both endpoints, common prefix;
     then verifies every convergent by the alternating sign of p^15 - 4q^15
     (integer sign-check against the minimal polynomial x^15 - 4) and the
     determinant identity;
  2. cross-validates the confinement class: brute-enumerates ALL Y in
     [9, 10^6] with ||alpha*Y|| < (9/5)/Y (exact 15th-power window test) and
     checks each against the Worley family (membership of the reduced
     denominator AND of Y itself in the enumerated family);
  3. enumerates the full candidate family up to Y <= 10^100 (superset
     constant CW = 9/5 > C15) and checks the EXACT equation P(X) = 4 P(Y) on
     every candidate pair, reporting intermediate-filter survivors:
        filter T1 (one-sided Thue): |X^15 - 4Y^15| <= C_A*Y^13
        filter T2 (two-sided band): -C_A*Y^13 <= X^15-4Y^15 <= -C_B*Y^13
        filter EQ (exact equation): P(X) = 4*P(Y)
  4. converts "no solution with Y <= 10^100" into the verified d-bound
     d > (rho_lo - 1)*10^100 - 7*rho_lo  ~  9.68*10^98.
"""

import time
from fractions import Fraction as F
from math import gcd, isqrt

T0 = time.time()
NCHK = 0


def PASS(msg):
    global NCHK
    NCHK += 1
    print(f"[PASS {NCHK:02d}] ({time.time()-T0:6.1f}s) {msg}")


def iroot(n, k):
    """floor(n**(1/k)) for n >= 0, pure integer arithmetic."""
    if n < 0:
        raise ValueError
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + k - 1) // k + 1)
    while True:
        r2 = ((k - 1) * r + n // r ** (k - 1)) // k
        if r2 >= r:
            break
        r = r2
    while r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r


def cf_of_fraction(num, den):
    terms = []
    while den:
        a = num // den
        terms.append(a)
        num, den = den, num - a * den
    return terms


def Pv(t):
    """P(t) = t * prod_{j=1..7}(t^2 - j^2), exact."""
    r = t
    for j in range(1, 8):
        r *= t * t - j * j
    return r


# ----------------------------------------------------------- exact constants
# (recomputed from scratch; must match derivation.py / constants.json)
r8 = iroot(4 * 10 ** 120, 15)
rho_lo = F(r8 - 100, 10 ** 8)
rho_hi = F(r8 + 101, 10 ** 8)
assert rho_lo ** 15 < 4 < rho_hi ** 15
C_A = 140 * (4 - rho_lo ** 13) + F(1, 100)
C_B = 140 * (4 - rho_hi ** 13) - F(1, 200)
C15 = F(1729, 1000)
assert C_A / (15 * rho_lo ** 14) <= C15
ymin = (221 - 7 * rho_hi - 7) / (rho_hi - 1)
Y0 = ymin.numerator // ymin.denominator + 1
assert Y0 == 2131
CW = F(9, 5)                       # superset constant for the family (>= C15)
assert CW >= C15 and 2 * CW < 4    # r*s <= 3 for the CW-family as well
PASS(f"constants recomputed: Y0={Y0}, C_A~{float(C_A):.6f}, "
     f"C_B~{float(C_B):.6f}, C15=1729/1000, family constant CW=9/5")

# ======================================================================= (1)
# exact continued fraction of alpha = 4^(1/15)
NDIG = 480
NEED = 335
while True:
    RA = iroot(4 * 10 ** (15 * NDIG), 15)
    assert RA ** 15 <= 4 * 10 ** (15 * NDIG) < (RA + 1) ** 15
    lo_terms = cf_of_fraction(RA, 10 ** NDIG)
    hi_terms = cf_of_fraction(RA + 1, 10 ** NDIG)
    terms = []
    for a, b in zip(lo_terms, hi_terms):
        if a != b:
            break
        terms.append(a)
    if len(terms) >= NEED + 1:
        break
    NDIG += 120
terms = terms[:NEED + 1]           # a_0 .. a_NEED
assert terms[0] == 1 and all(a >= 1 for a in terms[1:])

# convergents p_m/q_m, m = 0..NEED
ps, qs = [], []
pm1, pm2, qm1, qm2 = 1, 0, 0, 1    # (p_{-1},p_{-2},q_{-1},q_{-2})
for a in terms:
    p = a * pm1 + pm2
    q = a * qm1 + qm2
    ps.append(p)
    qs.append(q)
    pm2, pm1, qm2, qm1 = pm1, p, qm1, q

# exact verification against the minimal polynomial x^15 - 4:
#   p_m/q_m < 4^(1/15)  <=>  p_m^15 < 4 q_m^15 ;  convergents alternate.
for m in range(len(ps)):
    s = ps[m] ** 15 - 4 * qs[m] ** 15
    assert s != 0, "4^(1/15) rational?!"
    assert (s < 0) == (m % 2 == 0), f"alternation fails at m={m}"
# determinant identity p_m q_{m-1} - p_{m-1} q_m = (-1)^(m-1)
for m in range(1, len(ps)):
    assert ps[m] * qs[m - 1] - ps[m - 1] * qs[m] == (-1) ** (m - 1)
PASS(f"cf(4^(1/15)): first {NEED+1} terms verified EXACTLY "
     f"(alternating sign of p^15 - 4q^15 + determinant identity); "
     f"sandwich precision 10^-{NDIG}")
print(f"        terms[:40] = {terms[:40]}")
M100 = next(m for m in range(len(qs)) if qs[m] > 10 ** 100)
amax = max(terms[:NEED + 1])
print(f"        q_m > 10^100 first at m = {M100}  "
      f"(q_{M100} ~ {float(qs[M100]):.3e})")
print(f"        max partial quotient a_m, m <= {NEED}: {amax} "
      f"(at m = {terms.index(amax)});  max a_m, m <= {M100+1}: "
      f"{max(terms[:M100+2])}")

# ======================================================================= (2)
# brute cross-validation of the confinement class on Y in [9, 10^6]:
# all Y with some X, |alpha*Y - X| < CW/Y  (exact:  with CW = 9/5,
#   (5XY - 9)^15 < 4 (5Y^2)^15 < (5XY + 9)^15 )
qf = 4.0 ** (1.0 / 15.0)
BRUTE = 10 ** 6
brute = []
for Y in range(9, BRUTE + 1):
    Xf = qf * Y
    X = int(Xf + 0.5)
    if abs(Xf - X) * Y > 2.5:      # float prefilter, generous (CW = 1.8)
        continue
    for XX in (X - 1, X, X + 1):
        L, U = 5 * XX * Y - 9, 5 * XX * Y + 9
        mid = 4 * (5 * Y * Y) ** 15
        if L > 0 and L ** 15 < mid < U ** 15:
            brute.append((Y, XX))
qset = set(qs)
quasi = {1, 2, 3}                          # Worley m = -1 forms (b = r <= 3)
for m in range(1, len(qs)):
    for (r, s) in ((1, 1), (1, 2), (2, 1), (1, 3), (3, 1)):
        quasi.add(r * qs[m] + s * qs[m - 1])
        quasi.add(r * qs[m] - s * qs[m - 1])
worley_ok = 0
for (Y, X) in brute:
    if Pv(X) == 4 * Pv(Y):
        assert X - Y <= 220, f"large-d solution at {(Y, X)}?!"
    g = gcd(X, Y)
    b = Y // g
    assert b in qset or b in quasi, f"Worley violation at {(Y, X)}"
    if g >= 2:
        assert b in qset, f"Legendre (g>=2) violation at {(Y, X)}"
    worley_ok += 1
brute_eq = [(Y, X) for (Y, X) in brute if Pv(X) == 4 * Pv(Y)]
PASS(f"brute scan Y in [9, 10^6]: {len(brute)} pairs with "
     f"|alpha*Y - X| < 1.8/Y (exact window test); every reduced denominator "
     f"in the Worley family; g>=2 cases all pure convergents; "
     f"equation hits: {brute_eq if brute_eq else 'none'}")

# ------------------------------------------------------------------ (2b)
# complete exact catalog of the banked region d <= 220 (interface check):
# crude bracket (derivation.py, PASS 04 machinery) pins Y for each d:
#   (d - 7*rho_hi - 7)/(rho_hi - 1)  <  Y  <  (d + 7*rho_lo)/(rho_lo - 1).
# Overlapping blocks (d < 15) are included: the centered equation is the
# same polynomial identity regardless of overlap.
small_solutions = []
small_checked = 0
for d in range(1, 221):
    ylo = (d - 7 * rho_hi - 7) / (rho_hi - 1)
    yhi = (d + 7 * rho_lo) / (rho_lo - 1)
    ylo_i = max(9, ylo.numerator // ylo.denominator - 1)
    yhi_i = yhi.numerator // yhi.denominator + 2
    for Y in range(ylo_i, yhi_i + 1):
        small_checked += 1
        if Pv(Y + d) == 4 * Pv(Y):
            small_solutions.append((Y, Y + d, Y - 8, d))
assert small_solutions == [(12, 13, 4, 1)], small_solutions
PASS(f"banked-region catalog d in [1,220] ({small_checked} exact window "
     f"checks): the ONLY solution of P(X)=4P(Y) is (Y,X)=(12,13), i.e. "
     f"(n,d)=(4,1) -- the telescoping identity 6*7*...*20 = 4*(5*6*...*19) "
     f"(overlapping blocks, ratio collapses to (n+16)/(n+1)=4); "
     f"NO solution with d in [2,220]")

# ======================================================================= (3)
# full candidate family up to Y <= 10^100
YMAX = 10 ** 100


def floor_sqrt_frac(num, den):
    """floor(sqrt(num/den)) for positive integers."""
    return isqrt(num * den) // den


family = {}                                # Y -> provenance tag
for m in range(0, M100 + 1):
    # per-index multiple bound (g >= 1):  g^2 < CW*(q_{m+1}+q_m)/q_m
    gb = floor_sqrt_frac(CW.numerator * (qs[m + 1] + qs[m]),
                         CW.denominator * qs[m])
    gmax = max(60, gb + 1)                 # blanket 60 for extra margin
    for g in range(1, gmax + 1):
        Yc = g * qs[m]
        if 9 <= Yc <= YMAX and Yc not in family:
            family[Yc] = f"{g}*q_{m}"
    if m >= 1:
        for (r, s) in ((1, 1), (1, 2), (2, 1), (1, 3), (3, 1)):
            for sgn in (1, -1):
                base = r * qs[m] + sgn * s * qs[m - 1]
                for g in range(1, 9):      # quasi forms need only g=1; margin
                    Yc = g * base
                    if 9 <= Yc <= YMAX and Yc not in family:
                        family[Yc] = f"{g}*({r}q_{m}{'+' if sgn>0 else '-'}{s}q_{m-1})"
# family must cover every brute candidate (empirical completeness check)
for (Y, X) in brute:
    assert Y in family, f"family misses brute candidate Y={Y}"
PASS(f"candidate family built: {len(family)} Y-values "
     f"(indices m <= {M100}, multiples to per-index Legendre bound "
     f"max(60, g_m), quasi-convergents r*s <= 3 with margin g <= 8); "
     f"covers all {len(brute)} brute candidates")

pairs_checked = 0
t1_pass = []                               # one-sided Thue survivors
t2_pass = []                               # two-sided band survivors
eq_pass = []
for Yc in sorted(family):
    X0 = iroot(4 * Yc ** 15, 15)
    for X in range(X0 - 2, X0 + 4):
        if X <= Yc:
            continue
        pairs_checked += 1
        lhsq = X ** 15 - 4 * Yc ** 15
        y13 = Yc ** 13
        # filter T1
        if abs(lhsq) * C_A.denominator <= C_A.numerator * y13:
            t1_pass.append((Yc, X))
            # filter T2 (band)
            if (-C_A.numerator * y13 <= lhsq * C_A.denominator and
                    lhsq * C_B.denominator <= -C_B.numerator * y13):
                t2_pass.append((Yc, X))
        # filter EQ (exact equation) -- checked on EVERY candidate pair
        if Pv(X) == 4 * Pv(Yc):
            eq_pass.append((Yc, X))

# the only equation hit allowed anywhere is the banked d=1 telescope (12,13);
# in the theorem's regime (d >= 221, hence Y >= Y0) there must be NONE.
assert all(X - Yc <= 220 for (Yc, X) in eq_pass), eq_pass
assert eq_pass in ([], [(12, 13)]), eq_pass
PASS(f"exact equation checked on all {pairs_checked} candidate pairs "
     f"({len(family)} Y-values <= 10^100): ZERO solutions with d >= 221 "
     f"(only hit: the banked d=1 telescope {eq_pass})")
print(f"        filter T1 (|X^15-4Y^15| <= C_A Y^13):        "
      f"{len(t1_pass)} pairs pass")
print(f"        filter T2 (band [-C_A,-C_B]*Y^13):            "
      f"{len(t2_pass)} pairs pass")
for (Yc, X) in t2_pass:
    ratio = F((X ** 15 - 4 * Yc ** 15) * 10 ** 6, Yc ** 13)
    res = Pv(X) - 4 * Pv(Yc)
    nres = F(abs(res) * 10 ** 6, Yc ** 13)
    print(f"          band survivor: Y ~ 10^{len(str(Yc))-1} "
          f"({family[Yc]}), (X^15-4Y^15)/Y^13 = {float(ratio)/1e6:.4f}, "
          f"|P(X)-4P(Y)|/Y^13 = {float(nres)/1e6:.4f}  -> equation FAILS")

# closest approach to the equation among T1 survivors, normalized by Y^13
best = None
for (Yc, X) in t1_pass:
    nres = F(abs(Pv(X) - 4 * Pv(Yc)), Yc ** 13)
    if best is None or nres < best[0]:
        best = (nres, Yc, X)
if best:
    print(f"        closest equation approach among T1 survivors: "
          f"|P(X)-4P(Y)|/Y^13 = {float(best[0]):.4f} at Y ~ 10^"
          f"{len(str(best[1]))-1}  (a solution needs 0; generic scale ~94.5)")

# ======================================================================= (4)
# verified d-bound: any solution with Y > 10^100 has
#   d = X - Y > (rho_lo - 1)*Y - 7*rho_lo > (rho_lo - 1)*10^100 - 7*rho_lo
db = (rho_lo - 1) * 10 ** 100 - 7 * rho_lo
D_BOUND = db.numerator // db.denominator
PASS("conclusion (conditional only on derivation.py inequalities + "
     "Legendre/Worley):")
print(f"        NO k=15, N=4 solution with Y = n+8 <= 10^100;  combined with")
print(f"        the banked d <= 220 branch this verifies NO solution with")
print(f"        d <= {D_BOUND}")
print(f"           ~ {float(F(D_BOUND, 10**98)):.4f} * 10^98")
print(f"\nALL {NCHK} CHECKS PASSED -- cf_scan.py "
      f"({time.time()-T0:.1f}s total)")
