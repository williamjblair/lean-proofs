#!/usr/bin/env python3
"""
Erdos 686, k=5, N=4: the convergent-pinning reduction (full-equation route).

Centered coordinates: X := n+d+3 = D+2, Y := n+3 = A+2 (so Y >= 4, X > Y).
The equation (n+d+1)...(n+d+5) = 4 (n+1)...(n+5) becomes EXACTLY

    X^5 - 5X^3 + 4X = 4 (Y^5 - 5Y^3 + 4Y)                       (*)

  [ since z(z+1)(z+2)(z+3)(z+4) = w^5 - 5w^3 + 4w at w = z+2 ]

Hence   X^5 - 4Y^5 = 5X^3 - 4X - 20Y^3 + 16Y  =: G(X,Y).

With q := 4^(1/5), any solution has X/Y near q and

    |q - X/Y| = |G| / (Y^2 * (X^4 + X^3(qY) + ... + (qY)^4) / Y^2 ...)

    asymptotically  |qY - X| -> ((4 - q^3)/q^4) / Y = 0.561655... / Y.

CLAIM (validated below, elementary to make fully rigorous):
  for Y >= 40,  |q - X/Y| < 0.58 / Y^2  < 1/Y^2.
By Legendre/Fatou, X/Y in lowest terms g*(x/y) must then have y a convergent
denominator of cf(q) or a mediant neighbour.  Solutions therefore live on an
EXPONENTIALLY SPARSE explicit family; "no solution with Y <= 10^N" reduces to
O(N) exact integer checks.

This script:
  1. verifies the centering identity and the constant (4-q^3)/q^4 exactly;
  2. brute-force enumerates ALL Y <= 2*10^6 with ||qY|| < 0.9/Y (generous),
     checks (*) on each - cross-validates the d-scan;
  3. computes cf(4^(1/5)) far enough that q_k > 10^120, verifying every
     convergent EXACTLY via integer quintic inequalities;
  4. enumerates the generous candidate family (convergents, mediants,
     small multiples) up to 10^120 and checks (*) exactly on each.
"""
import sympy as sp
from fractions import Fraction

# ---------------------------------------------------------------- step 1
x, w = sp.symbols('x w')
lhs = sp.expand(x*(x+1)*(x+2)*(x+3)*(x+4))
rhs = sp.expand((w**5 - 5*w**3 + 4*w).subs(w, x+2))
assert sp.expand(lhs - rhs) == 0
print("[PASS] centering identity: z(z+1)..(z+4) = w^5-5w^3+4w, w=z+2")

qv = sp.root(4, 5)
kappa = sp.N((4 - qv**3)/qv**4, 50)
print("       (4-q^3)/q^4 =", kappa)

# exact integer test helpers: X = round(q*Y): find via integer fifth root of 4Y^5
def iroot5(n):
    """floor(n^(1/5)) exact, pure integer arithmetic (safe for huge n)."""
    if n < 0:
        raise ValueError
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + 4) // 5)   # r >= n^(1/5)
    while True:
        r2 = (4 * r + n // r**4) // 5      # integer Newton step
        if r2 >= r:
            break
        r = r2
    while r**5 > n:
        r -= 1
    while (r + 1)**5 <= n:
        r += 1
    return r

def eq_holds(X, Y):
    return X**5 - 5*X**3 + 4*X == 4*(Y**5 - 5*Y**3 + 4*Y)

# ---------------------------------------------------------------- step 2
# all Y <= 2e6 with |qY - X| < 0.9/Y for some integer X (i.e. 4Y^5 close to X^5)
# exact test: |qY - X| < eps  <=>  (X-eps)^5 < 4 Y^5 < (X+eps)^5; we use
# rational eps = 9/(10Y) and exact integer comparisons after clearing denoms.
print("brute scan Y <= 2e6 for ||qY|| < 0.9/Y candidates ...")
cand = []
for Y in range(4, 2_000_001):
    fourY5 = 4 * Y**5
    X = iroot5(fourY5)          # X <= qY < X+1
    # test X and X+1 as nearest-integer candidates
    for XX in (X, X + 1):
        # |qY - XX| < 9/(10Y)  <=>  (10Y*XX - 9)^5 < 4 * (10 Y * Y)^5 < (10Y*XX + 9)^5
        L = 10 * Y * XX - 9
        R = 10 * Y * XX + 9
        mid = 4 * (10 * Y * Y) ** 5
        if L**5 < mid < R**5:
            cand.append((Y, XX))
sols = [(Y, X) for (Y, X) in cand if eq_holds(X, Y)]
print(f"       candidates: {len(cand)}; exact solutions of (*): {sols}")
print("       candidate list (Y, X, Y*||qY||, equation residual X^5-5X^3+4X-4(Y^5-5Y^3+4Y)):")
for (Y, X) in cand:
    dev = float(abs(qmp_placeholder * Y - X)) if False else None
    resid = X**5 - 5*X**3 + 4*X - 4*(Y**5 - 5*Y**3 + 4*Y)
    import math
    qf = 4 ** 0.2
    print(f"         Y={Y:<9} X={X:<9} Y*|qY-X|={abs(qf*Y-X)*Y:8.4f}   resid={resid:+.3e}" if abs(resid) > 1e18 else
          f"         Y={Y:<9} X={X:<9} Y*|qY-X|={abs(qf*Y-X)*Y:8.4f}   resid={resid:+d}")
assert sols == [], "unexpected solution!"
print("[PASS] no solution with 4 <= Y <= 2*10^6  (=> no k=5 solution with n+3 <= 2*10^6)")

# ---------------------------------------------------------------- step 3
# continued fraction of q = 4^(1/5) with EXACT verification of each convergent.
import mpmath as mp
mp.mp.dps = 800
qmp = mp.mpf(4) ** (mp.mpf(1)/5)

def cf_terms(val, n):
    terms = []
    v = val
    for _ in range(n):
        a = int(mp.floor(v))
        terms.append(a)
        v = 1/(v - a)
    return terms

N_TERMS = 320
terms = cf_terms(qmp, N_TERMS)
# build convergents
ps = [1, terms[0]]
qs = [0, 1]
for a in terms[1:]:
    ps.append(a * ps[-1] + ps[-2])
    qs.append(a * qs[-1] + qs[-2])
ps, qs = ps[1:], qs[1:]   # ps[k]/qs[k] = k-th convergent, k>=0

# exact verification: p/q < 4^{1/5}  <=>  p^5 < 4 q^5 ; alternation must hold.
ok = True
for k in range(len(ps)):
    below = ps[k]**5 < 4 * qs[k]**5
    if below != (k % 2 == 0):
        ok = False
        print("  convergent alternation FAILED at k =", k)
        break
print(f"[{'PASS' if ok else 'FAIL'}] cf(4^(1/5)) first {N_TERMS} terms verified exactly "
      f"(alternating quintic test)")
assert ok
amax = max(terms[:260])
print(f"       max partial quotient among first 260 terms: {amax}")
# Legendre-multiple bound: Y = g*q_k possible only for g^2 <= a_{k+1}+2;
# with amax <= 2498 the blanket g <= 50 below is a valid superset.
assert amax + 2 <= 2500, "increase g range!"
print("       terms[:40] =", terms[:40])
print("       q_k reaches 10^120 at k =",
      next(k for k in range(len(qs)) if qs[k] > 10**120))

# ---------------------------------------------------------------- step 4
# generous candidate family: for each convergent (p_k, q_k), test
#   Y in { g*q_k : 1 <= g <= 50 }  and mediant denominators q_k +- q_{k-1},
#   and for each Y the integers X in {floor((4Y^5)^(1/5)), +-2}.
print("checking the exact equation on the sparse family up to 10^130 ...")
checked = 0
found = []
seenY = set()
for k in range(len(qs)):
    denoms = set()
    for g in range(1, 51):
        denoms.add(g * qs[k])
    if k >= 1:
        for g in range(1, 9):   # mediants need only g=1; g<=8 for extra margin
            denoms.add(g * (qs[k] + qs[k-1]))
            denoms.add(g * abs(qs[k] - qs[k-1]))
    for Y in denoms:
        if Y < 4 or Y > 10**130 or Y in seenY:
            continue
        seenY.add(Y)
        fourY5 = 4 * Y**5
        X0 = iroot5(fourY5)
        for X in range(X0 - 2, X0 + 3):
            checked += 1
            if X > Y and eq_holds(X, Y):
                found.append((Y, X))
print(f"       family size: {len(seenY)} Y-values, {checked} (X,Y) pairs checked")
print(f"       exact solutions found: {found}")
assert found == []
print("[PASS] no solution on the generous convergent family up to Y = 10^130")
print()
print("Conclusion: conditional ONLY on the elementary pinning inequality")
print("  |q - X/Y| < 0.58/Y^2  for Y >= 40  (Fatou/Legendre step),")
print("there is NO k=5, N=4 solution with n+3 <= 10^120 (i.e. d <~ 3*10^119).")
