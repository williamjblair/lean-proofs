#!/usr/bin/env python3
"""
Erdos 686, k = 13, N = 4: exact continued fraction of q = 4^(1/13) and the
quasi-convergent scan to Y <= 10^100.

Inputs proved in derivation.py (all exact):
  any solution P(X) = 4P(Y) of the centered equation with Y >= 600 satisfies
     (89/80) Y < X < (9/8) Y,   |X^13 - 4Y^13| <= (3501/50) Y^11,
     0 < q - X/Y <= (3/2)/Y^2.
  (Y >= 1958 is automatic for d >= 221; d <= 220 is banked in Lean.)

Confinement (Worley 1981 / Dujella 2004, C = 3/2, rs < 2C = 3):
  write X/Y = g*(a/b) in lowest terms; then
    g = 1 :  (a,b) = (r p_{m+1} +- s p_m, r q_{m+1} +- s q_m),
             (r,s) in {(1,0),(0,1),(1,1),(1,2),(2,1)}          [rs <= 2]
    g >= 2:  C/g^2 <= 3/8 < 1/2, so Legendre applies: b = q_m, and
             g^2 < (3/2)(a_{m+1}+2)  since |q - p_m/q_m| > 1/((a_{m+1}+2) q_m^2).

This script (every decision by exact integer arithmetic):
  1. computes cf(4^(1/13)) to >= 320 terms by the polynomial Taylor-shift /
     reversal method: each partial quotient is certified by integer SIGN
     evaluations of an exact integer polynomial whose unique real root is the
     current complete quotient.  NO floating point in the extraction.
  2. cross-checks the terms against a 1500-digit mpmath expansion (advisory),
     verifies convergent unimodularity p_k q_{k-1} - p_{k-1} q_k = (-1)^{k-1}
     and the alternating sign of p_k^13 - 4 q_k^13 (both exact), and verifies
     the classical lower bound |q - p_m/q_m| > 1/((a_{m+1}+2) q_m^2) exactly.
  3. enumerates the full Worley candidate family up to Y <= 10^100 (with a
     generous blanket multiplier and extra mediant multiples for margin) and
     checks the exact equation P(X) = 4 P(Y) on every candidate.
  4. brute-scans ALL Y <= 10^6 for |q - X/Y| < (3/2)/Y^2 (float pre-filter
     with a proven-safe 1e-6 slack, then exact 13th-power confirmation),
     checks the equation, and classifies every hit into the Worley family --
     an end-to-end empirical validation of the confinement step.
  5. closes 8 <= Y <= 2100 unconditionally by direct monotone sweep
     (no approximation input at all; covers the pre-confinement range).
"""

import math
from math import gcd

PASS = 0
def check(label, ok):
    global PASS
    if not ok:
        raise AssertionError("FAILED: " + label)
    PASS += 1
    print(f"[PASS {PASS:2d}] {label}")

E = [91, 3003, 44473, 296296, 773136, 518400]

def Pval(T):
    return (T**13 - 91*T**11 + 3003*T**9 - 44473*T**7
            + 296296*T**5 - 773136*T**3 + 518400*T)

def iroot13(n):
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + 12) // 13)
    while True:
        r2 = (12 * r + n // r**12) // 13
        if r2 >= r:
            break
        r = r2
    while r**13 > n:
        r -= 1
    while (r + 1)**13 <= n:
        r += 1
    return r

# --------------------------------------------------------------- 1. exact CF
# f(z) = sum c[i] z^i has exactly ONE real root (Moebius images of the single
# real root of z^13 - 4; the 12 conjugates stay complex).  sign(f(m)) for
# integer m therefore determines m <=> root exactly.

def poly_eval_sign(c, m):
    v = 0
    for coef in reversed(c):
        v = v * m + coef
    return (v > 0) - (v < 0)

def taylor_shift(c, a):
    """coefficients of f(z + a), exact binomial expansion (degree 13)."""
    from math import comb
    n = len(c) - 1
    out = [0] * (n + 1)
    for i, ci in enumerate(c):
        if ci:
            for jj in range(i + 1):
                out[jj] += ci * comb(i, jj) * a**(i - jj)
    return out

def content_reduce(c):
    g = 0
    for ci in c:
        g = gcd(g, abs(ci))
    return [ci // g for ci in c] if g > 1 else list(c)

def cf_exact(nterms):
    """CF of 4^(1/13): returns list of partial quotients, all decisions exact."""
    c = [-4] + [0]*12 + [1]          # z^13 - 4
    terms = []
    for step in range(nterms):
        s_inf = (c[-1] > 0) - (c[-1] < 0)
        assert s_inf != 0
        # unique real root alpha; find floor(alpha) by exact sign bisection.
        lo = 1 if step > 0 else 1     # alpha > 1 at every step (a_i >= 1)
        assert poly_eval_sign(c, lo) == -s_inf, "root not > 1?"
        hi = 2
        while poly_eval_sign(c, hi) == -s_inf:
            hi *= 2
        # invariant: alpha in (lo, hi), sign(f(lo)) = -s_inf, sign(f(hi)) = +s_inf
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if poly_eval_sign(c, mid) == -s_inf:
                lo = mid
            else:
                hi = mid
        a = lo                        # floor(alpha): f(a) opposite sign to f(a+1)
        terms.append(a)
        # alpha' = 1/(alpha - a):  g(z) = z^13 * f(a + 1/z)  (shift then reverse)
        c = taylor_shift(c, a)[::-1]
        c = content_reduce(c)
    return terms

N_TERMS = 330
print(f"computing cf(4^(1/13)) to {N_TERMS} terms, exact polynomial method ...")
terms = cf_exact(N_TERMS)
print("        terms[:40] =", terms[:40])

# advisory cross-check with high-precision floating point
import mpmath as mp
mp.mp.dps = 1500
v = mp.mpf(4) ** (mp.mpf(1)/13)
mp_terms = []
for _ in range(N_TERMS):
    a = int(mp.floor(v))
    mp_terms.append(a)
    v = 1/(v - a)
check(f"exact CF terms agree with 1500-digit mpmath expansion on all {N_TERMS} terms",
      mp_terms == terms)

# convergents
ps, qs = [1, terms[0]], [0, 1]
for a in terms[1:]:
    ps.append(a * ps[-1] + ps[-2])
    qs.append(a * qs[-1] + qs[-2])
ps, qs = ps[1:], qs[1:]               # ps[m]/qs[m] = m-th convergent, m >= 0

check("unimodularity p_m q_{m-1} - p_{m-1} q_m = (-1)^{m-1} for all m",
      all(ps[m]*qs[m-1] - ps[m-1]*qs[m] == (-1)**(m-1) for m in range(1, len(ps))))
check(f"alternation: sign(p_m^13 - 4 q_m^13) = (-1)^{{m+1}} for all {len(ps)} convergents "
      "(exact 13th-power integer test)",
      all((ps[m]**13 < 4*qs[m]**13) == (m % 2 == 0) for m in range(len(ps))))

M100 = next(m for m in range(len(qs)) if qs[m] > 10**100)
M102 = next(m for m in range(len(qs)) if qs[m] > 10**102)
a_max = max(terms[1:M102 + 2])
print(f"        q_m > 10^100 first at m = {M100};  q_m > 10^102 first at m = {M102}")
print(f"        max partial quotient a_m for 1 <= m <= {M102+1}: a_max = {a_max}")

# classical lower bound used for the g-bound (exact, both parities):
#   |q - p_m/q_m| > 1/((a_{m+1}+2) q_m^2)
def quality_lower_ok(m):
    p, qd, a1 = ps[m], qs[m], terms[m + 1]
    A = (a1 + 2) * qd**2
    if m % 2 == 0:   # p/qd < q:  need  q > p/qd + 1/(A)  <=>  4 (qd A)^13 > (p A + qd)^13
        return 4 * (qd * A)**13 > (p * A + qd)**13
    else:            # p/qd > q:  need  q < p/qd - 1/A
        return 4 * (qd * A)**13 < (p * A - qd)**13
check(f"exact lower bound |q - p_m/q_m| > 1/((a_{{m+1}}+2) q_m^2) for all m <= {M102}",
      all(quality_lower_ok(m) for m in range(M102 + 1)))

G_needed = math.isqrt((3 * (a_max + 2)) // 2) + 1
G = max(50, G_needed + 5)
print(f"        Legendre-multiple bound: g <= sqrt(1.5*(a_max+2)) => g <= {G_needed}; "
      f"blanket G = {G}")

# ------------------------------------------------- 2. Worley family, Y <= 1e100
BOUND = 10**100
print(f"enumerating Worley family (G = {G}, mediant classes rs <= 2, margin "
      f"multiples g <= 8) up to Y <= 10^100 ...")
family = {}          # Y -> tag (first tag wins; for classification/reporting)
def add(Y, tag):
    if 1 <= Y <= BOUND and Y not in family:
        family[Y] = tag

for m in range(M102 + 1):
    for g in range(1, G + 1):
        add(g * qs[m], f"{g}*q[{m}]")
    if m >= 1:
        combos = [(1, 1), (1, 2), (2, 1)]
        for (r, s) in combos:
            for g in range(1, 9):                     # g=1 required; g<=8 margin
                add(g * (r*qs[m] + s*qs[m-1]), f"{g}*({r}q[{m}]+{s}q[{m-1}])")
                add(g * abs(r*qs[m] - s*qs[m-1]), f"{g}*|{r}q[{m}]-{s}q[{m-1}]|")

print(f"        family size: {len(family)} distinct Y values")

checked_pairs = 0
solutions = []
thue_passes = []      # (Y, X, tag) passing |X^13-4Y^13| <= (3501/50) Y^11
for Y, tag in family.items():
    if Y < 8:          # domain: Y = n+7 >= 8 (P vanishes on 0..6: fake 0=0 hits)
        continue
    fourY13 = 4 * Y**13
    X0 = iroot13(fourY13)
    Y11_scaled = 3501 * Y**11
    Y13c = 4 * (2 * Y**2)**13
    for X in range(X0 - 2, X0 + 3):
        if X <= Y:
            continue
        checked_pairs += 1
        if Pval(X) == 4 * Pval(Y):
            solutions.append((Y, X, tag))
        if 50 * abs(X**13 - fourY13) <= Y11_scaled:
            thue_passes.append((Y, X, tag))
            # pinning conversion must hold whenever Y >= 600 and X is bracketed
            if Y >= 600 and 80*X > 89*Y and 8*X < 9*Y:
                assert (2*X*Y - 3)**13 < Y13c < (2*X*Y + 3)**13, (Y, X)

check(f"exact equation P(X) = 4P(Y) fails on ALL {checked_pairs} family pairs "
      f"({len(family)} Y-values) up to Y = 10^100",
      solutions == [])
# classification by set membership (tags can collide: q_{m+1} = 2q_m + q_{m-1}
# is also the (2,1) mediant of index m, first-tag-wins hides it)
conv_set = {qs[m] for m in range(M100 + 1)}
conv_pass = sum(1 for (Y, _, _) in thue_passes if Y in conv_set)
check(f"positive control: EVERY convergent pair (p_m, q_m) with 8 <= q_m <= 10^100 "
      f"passes the Thue filter (the confinement is not vacuous)",
      all(50 * abs(ps[m]**13 - 4 * qs[m]**13) <= 3501 * qs[m]**11
          for m in range(M100 + 1) if qs[m] >= 8))
print(f"        Thue-filter passes |X^13-4Y^13| <= (3501/50)Y^11: "
      f"{len(thue_passes)} pairs; {conv_pass} have Y = q_m (true convergent "
      f"denominators), the rest are multiples/mediants; the pinning conversion "
      f"(2XY-3)^13 < 4(2Y^2)^13 < (2XY+3)^13 verified on all with Y >= 600")
small_show = [(t[0], t[2]) for t in thue_passes if t[0] <= 10**9]
print(f"        Thue passes with Y <= 10^9: {small_show}")

# --------------------------------------- 3. brute scan Y <= 10^6 (validation)
# float pre-filter safety: |fl(qf*Y) - qY| <= 3 ulp * qY <= 3*2^-52*1.2e6
# < 8e-10 for Y <= 1e6, far below the 1e-6 slack; every float-passer is then
# confirmed or rejected by the exact 13th-power test, every true candidate
# passes the padded float test.  Decisions: exact only.
print("brute scan: all 8 <= Y <= 10^6 with |q - X/Y| < (3/2)/Y^2 ...")
qf = 4.0 ** (1.0 / 13.0)
brute = []
for Y in range(8, 10**6 + 1):
    z = qf * Y
    X0 = int(z)
    thr = 1.5 / Y + 1e-6
    for X in (X0, X0 + 1):
        if abs(z - X) < thr and X > 0:
            # exact: |qY - X| < 3/(2Y)  <=>  (2XY-3)^13 < 4(2Y^2)^13 < (2XY+3)^13
            if (2*X*Y - 3)**13 < 4 * (2*Y**2)**13 < (2*X*Y + 3)**13:
                brute.append((Y, X))
check("no exact solution among the brute-scan candidates (Y <= 10^6)",
      all(Pval(X) != 4 * Pval(Y) for (Y, X) in brute))
print(f"        {len(brute)} candidates with |q - X/Y| < (3/2)/Y^2, Y <= 10^6")

# Worley classification of every brute candidate (empirical confinement check)
misfits = [(Y, X) for (Y, X) in brute if Y not in family]
check("every brute-scan candidate Y lies in the enumerated Worley family "
      "(empirical validation of the confinement step)",
      misfits == [])
for (Y, X) in brute[:12]:
    g = gcd(X, Y)
    resid = Pval(X) - 4*Pval(Y)
    print(f"          Y={Y:<8} X={X:<8} g={g}  tag={family.get(Y,'?'):<18} "
          f"resid={float(resid):+.3e}")

# --------------------------------- 4. unconditional closure of 8 <= Y <= 2100
print("unconditional sweep 8 <= Y <= 2100 (all X > Y, monotone stepping) ...")
found = []
for Y in range(8, 2101):
    B = 4 * Pval(Y)
    X = Y + 1
    while Pval(X) < B:
        X += 1
    if Pval(X) == B:
        found.append((Y, X))
check("no solution at all with 8 <= Y <= 2100 (covers every n <= 2093, ALL d; "
      "no approximation input)", found == [])

print()
print(f"ALL {PASS} CHECKS PASSED.")
print("=" * 72)
print("CONCLUSION (conditional only on derivation.py's proved chain + Worley):")
print(f"  no k=13, N=4 solution with Y = n+7 <= 10^100;")
print(f"  with the window translation (derivation.py PASS 21) and the banked")
print(f"  d <= 220 certificates:  NO SOLUTION WITH d <= 1.125 * 10^99.")
print(f"  family: {len(family)} Y-candidates, {checked_pairs} (X,Y) pairs, 0 passes.")
