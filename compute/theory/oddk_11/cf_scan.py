#!/usr/bin/env python3
"""
Erdos 686, k=11, N=4: exact continued fraction of 4^(1/11) and the
Worley/quasi-convergent scan.

EVERYTHING in this file is pure integer arithmetic.  No floating point is
used anywhere, not even for initial guesses: partial quotients are produced
by exact homographic sign walks against the minimal polynomial x^11 - 4,
using (11 odd, t -> t^11 strictly monotone on all of R):

    sign(A*alpha + B) = sign(4*A^11 + B^11),      alpha := 4^(1/11).

Steps:
  1. cf(4^(1/11)) to 340 terms, every floor PROVED by two integer sign checks;
  2. convergent verification: quintic^{11}-alternation p^11 <> 4 q^11 and the
     best-approximation inequality |q^2 alpha - p q| < 1, both exact;
  3. Worley/Dujella candidate family for C = 13/10 (r*s < 2C = 13/5, so
     r*s <= 2), plus generous superset margins, enumerated up to Y <= 10^100;
  4. exact equation check P11(X) = 4*P11(Y) on every candidate, X in a
     +-2 window around floor((4 Y^11)^(1/11)) (the pin forces X = floor(qY));
  5. the two-sided pin filter (10XY+12)^11 < 4(10Y^2)^11 < (10XY+13)^11 --
     the "intermediate filter" from derivation.py -- reported separately;
  6. unconditional integer-bisection brute scan of ALL Y in [7, 2*10^5];
  7. cross-validation: every Y in [100, 2*10^5] passing the pin filter lies
     in the theoretical Worley family (empirical check of step 3's theory).

Inputs proved in derivation.py (exact, sympy):
  every solution with Y >= 100 has X = floor(alpha*Y) and
     6/5 < Y^2*(alpha - X/Y) < 13/10.
"""

import sys
from math import isqrt

# ---------------------------------------------------------------- utilities


def iroot11(n):
    """floor(n^(1/11)) by pure-integer Newton; exact for huge n."""
    if n < 0:
        raise ValueError
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + 10) // 11)      # r >= n^(1/11)
    while True:
        r2 = (10 * r + n // r**10) // 11
        if r2 >= r:
            break
        r = r2
    while r**11 > n:
        r -= 1
    while (r + 1)**11 <= n:
        r += 1
    return r


def P11(t):
    """P11(t) = t(t^2-1)(t^2-4)(t^2-9)(t^2-16)(t^2-25), exact."""
    t2 = t * t
    return t * (t2 - 1) * (t2 - 4) * (t2 - 9) * (t2 - 16) * (t2 - 25)


def eq_holds(X, Y):
    return P11(X) == 4 * P11(Y)


def sign_lin(A, B):
    """Exact sign of A*alpha + B, alpha = 4^(1/11)  (never 0 for (A,B)!=(0,0))."""
    v = 4 * A**11 + B**11
    return 1 if v > 0 else (-1 if v < 0 else 0)


# ------------------------------------------ 1. exact continued fraction terms
NTERMS = 340
SCALE = 10**700
ALPHA_NUM = iroot11(4 * SCALE**11)          # floor(alpha * SCALE), guess only
assert ALPHA_NUM**11 <= 4 * SCALE**11 < (ALPHA_NUM + 1)**11

print(f"computing cf(4^(1/11)) to {NTERMS} terms, all floors verified exactly ...")
terms = []
A, B, C, D = 1, 0, 0, 1                     # alpha_i = (A alpha + B)/(C alpha + D)
for i in range(NTERMS):
    assert sign_lin(C, D) > 0, "denominator sign lost"
    num = A * ALPHA_NUM + B * SCALE
    den = C * ALPHA_NUM + D * SCALE
    a = num // den                          # guess (exact ints, approx alpha)
    # exact verification / correction walk:  a = floor(alpha_i)
    while sign_lin(A - a * C, B - a * D) < 0:
        a -= 1
    while sign_lin(A - (a + 1) * C, B - (a + 1) * D) >= 0:
        a += 1
    assert i == 0 or a >= 1
    terms.append(a)
    A, B, C, D = C, D, A - a * C, B - a * D
    assert max(abs(A), abs(B), abs(C), abs(D)) < 10**660, "precision headroom"

print(f"[PASS] {NTERMS} partial quotients, each floor certified by 2 integer "
      f"sign checks (4A^11 + B^11)")
print("       terms[:40] =", terms[:40])

# convergents
ps = [1, terms[0]]
qs = [0, 1]
for a in terms[1:]:
    ps.append(a * ps[-1] + ps[-2])
    qs.append(a * qs[-1] + qs[-2])
ps, qs = ps[1:], qs[1:]                     # ps[k]/qs[k] = k-th convergent

# ------------------------------------------ 2. exact convergent verification
for k in range(len(ps)):
    below = ps[k]**11 < 4 * qs[k]**11
    assert below == (k % 2 == 0), f"alternation failed at k={k}"
print(f"[PASS] alternation p_k^11 <> 4 q_k^11 correct for all {len(ps)} convergents")

for k in range(1, len(ps)):
    p, q = ps[k], qs[k]
    assert (p * q - 1)**11 < 4 * q**22 < (p * q + 1)**11, f"quality failed at k={k}"
print(f"[PASS] |q_k^2 alpha - p_k q_k| < 1 for all k >= 1 (exact 11th-power checks)")

K100 = next(k for k in range(len(qs)) if qs[k] > 10**100)
K102 = next(k for k in range(len(qs)) if qs[k] > 10**102)
amax_scan = max(terms[:K102 + 2])
print(f"       q_k exceeds 10^100 at k = {K100}; 10^102 at k = {K102}; "
      f"max partial quotient below there: {amax_scan}")
big = [(i, a) for i, a in enumerate(terms[:K102 + 2]) if a >= 100]
print(f"       partial quotients >= 100 below index {K102 + 2}: {big}")

# ------------------------------------------ 3. Worley candidate family, Y <= 10^100
# theory (C = 13/10):  any solution Y >= 100 has, with g = gcd(X,Y):
#   g >= 2:  Y = g*q_m, g^2 < (13/10)(a_{m+1}+2)          [Legendre, 13/40 < 1/2]
#   g  = 1:  Y = r*q_{m+1} +- s*q_m, r,s >= 0, r*s <= 2   [Worley/Dujella]
# scan uses a strict SUPERSET: blanket multiples g <= G_BLANKET, quasi-range
# a in 1..3, b in -3..3, and multiples g <= 8 of q_k +- q_{k-1}.
YMAX = 10**100
G_BLANKET = 64
gmax_needed = isqrt(13 * (amax_scan + 2) // 10) + 1
print(f"       per-theory multiple bound: g <= {gmax_needed}; blanket used: "
      f"{max(G_BLANKET, gmax_needed)}")
G_BLANKET = max(G_BLANKET, gmax_needed)

family = set()
for k in range(1, K102 + 1):
    qk, qk1 = qs[k], qs[k - 1]
    for g in range(1, G_BLANKET + 1):
        family.add(g * qk)
    for r, s in ((1, 1), (1, 2), (2, 1)):
        family.add(r * qk + s * qk1)
        if r * qk - s * qk1 > 0:
            family.add(r * qk - s * qk1)
    for a in range(1, 4):
        for b in range(-3, 4):
            v = a * qk + b * qk1
            if v > 0:
                family.add(v)
    for g in range(1, 9):
        family.add(g * (qk + qk1))
        if qk - qk1 > 0:
            family.add(g * (qk - qk1))
family = sorted(y for y in family if 7 <= y <= YMAX)
print(f"       candidate family size (7 <= Y <= 10^100): {len(family)}")

# ------------------------------------------ 4.+5. exact checks on the family
found = []
pin_pass = []          # two-sided pin  (10XY+12)^11 < 4(10Y^2)^11 < (10XY+13)^11
near_window = []       # looser window  [1, 3/2]:  (10XY+10) / (10XY+15)
pairs_checked = 0
for Y in family:
    X0 = iroot11(4 * Y**11)
    for X in range(X0 - 2, X0 + 4):
        if X <= Y:
            continue
        pairs_checked += 1
        if eq_holds(X, Y):
            found.append((Y, X))
    mid = 4 * (10 * Y * Y)**11
    for X in (X0, X0 + 1):
        lo, hi = 10 * X * Y + 12, 10 * X * Y + 13
        if lo**11 < mid < hi**11:
            pin_pass.append((Y, X))
        lo, hi = 10 * X * Y + 10, 10 * X * Y + 15
        if lo**11 < mid < hi**11:
            near_window.append((Y, X))

def classify(Y):
    """CF pedigree of a family member (first matching decomposition)."""
    for k in range(1, K102 + 1):
        if qs[k] > Y:
            break
        if Y % qs[k] == 0 and Y // qs[k] <= G_BLANKET:
            g = Y // qs[k]
            return f"{g}*q_{k}" if g > 1 else f"q_{k}"
    for k in range(1, K102 + 1):
        if qs[k - 1] > Y:
            break
        for a in range(1, 4):
            for bb in range(-3, 4):
                if a * qs[k] + bb * qs[k - 1] == Y:
                    return f"{a}*q_{k}{bb:+d}*q_{k - 1}"
    for k in range(1, K102 + 1):
        for g in range(1, 9):
            if g * (qs[k] + qs[k - 1]) == Y or g * (qs[k] - qs[k - 1]) == Y:
                return f"{g}*(q_{k}+-q_{k - 1})"
    return "?"


print(f"[PASS] family scan: {pairs_checked} (X,Y) pairs checked exactly; "
      f"solutions of P11(X)=4*P11(Y): {found}")
assert found == []
print(f"       two-sided-pin survivors (the ONLY (X,Y) a solution could be): "
      f"{len(pin_pass)}")
for (Y, X) in pin_pass:
    print(f"         Y = {Y}")
    print(f"           ({len(str(Y))} digits, form {classify(Y)}, "
          f"X - floor(qY) = {X - iroot11(4 * Y**11)})")
print(f"       loose-window [1,3/2] survivors: {len(near_window)}")
for (Y, X) in near_window[:12]:
    print(f"         Y = {Y if Y < 10**40 else str(Y)[:20] + '...'} "
          f"({len(str(Y))} digits, form {classify(Y)})")

# strict Worley-family membership of every pin survivor (no scan margins):
#   {g*q_m : g^2 < (13/10)(a_{m+1}+2)}  U  {r*q_m +- s*q_{m-1} : r*s <= 2}
strictQ = set()
for k in range(0, K102 + 1):
    gmax = isqrt(13 * (terms[k + 1] + 2) // 10) + 1 if k + 1 < len(terms) else 2
    for g in range(1, gmax + 1):
        strictQ.add(g * qs[k])
    if k >= 1:
        for r, s in ((1, 1), (1, 2), (2, 1)):
            strictQ.add(r * qs[k] + s * qs[k - 1])
            if r * qs[k] - s * qs[k - 1] > 0:
                strictQ.add(r * qs[k] - s * qs[k - 1])
stray16 = [Y for (Y, X) in pin_pass if Y not in strictQ]
print(f"[{'PASS' if not stray16 else 'FAIL'}] all {len(pin_pass)} pin survivors "
      f"lie in the STRICT Worley family (no margins); strays: {len(stray16)}")
for Y in stray16:
    print(f"         STRAY: {Y}")
assert stray16 == [], "Worley-theory violation -- investigate!"

# ------------------------------------------ 6. unconditional brute scan Y <= 2*10^5
print("brute integer-bisection scan of ALL Y in [7, 2*10^5] ...")
BRUTE = 200_000
brute_sols = []
for Y in range(7, BRUTE + 1):
    tgt = 4 * P11(Y)
    lo, hi = Y + 1, 2 * Y            # P11(2Y) > 4 P11(Y) for Y >= 7 (checked)
    assert P11(hi) > tgt
    while lo < hi:                    # smallest X with P11(X) >= tgt
        mid = (lo + hi) // 2
        if P11(mid) < tgt:
            lo = mid + 1
        else:
            hi = mid
    if P11(lo) == tgt:
        brute_sols.append((Y, lo))
assert brute_sols == []
print(f"[PASS] no solution with 7 <= Y <= {BRUTE} (monotone bisection, exact)")

# ------------------------------------------ 7. cross-validate Worley membership
# The Worley HYPOTHESIS is the one-sided bound |alpha - X/Y| < 13/(10 Y^2).
# Enumerate ALL Y in [100, 2*10^5] satisfying it (exact 11th-power window
# test) and verify each lies in the theoretical family (NO scan margins):
#   {g*q_m : g^2 < (13/10)(a_{m+1}+2)} U {r*q_m +- s*q_{m-1} : r*s <= 2}.
theo = set()
for k in range(0, len(qs)):
    if qs[k] > 400 * BRUTE:
        break
    gmax = isqrt(13 * (terms[k + 1] + 2) // 10) + 1 if k + 1 < len(terms) else 2
    for g in range(1, gmax + 1):
        theo.add(g * qs[k])
    if k >= 1:
        for r, s in ((1, 1), (1, 2), (2, 1)):
            theo.add(r * qs[k] + s * qs[k - 1])
            if r * qs[k] - s * qs[k - 1] > 0:
                theo.add(r * qs[k] - s * qs[k - 1])

filter_pass = []
for Y in range(100, BRUTE + 1):
    X0 = iroot11(4 * Y**11)
    mid = 4 * (10 * Y * Y)**11
    for X in (X0, X0 + 1):
        if (10 * X * Y - 13)**11 < mid < (10 * X * Y + 13)**11:
            filter_pass.append((Y, X))
stray = [(Y, X) for (Y, X) in filter_pass if Y not in theo]
print(f"[PASS] Worley-hypothesis passers |alpha - X/Y| < 13/(10Y^2) in "
      f"[100, 2*10^5]: {len(filter_pass)}; strays outside theoretical family: "
      f"{len(stray)}")
assert stray == []
two_sided = [(Y, X) for (Y, X) in filter_pass
             if (10 * X * Y + 12)**11 < 4 * (10 * Y * Y)**11 < (10 * X * Y + 13)**11]
print(f"       of these, two-sided-pin (solution-viable) passers: {len(two_sided)}")
for (Y, X) in filter_pass[:15]:
    print(f"         Y = {Y:<8} X = {X:<8} form {classify(Y)}")

# ------------------------------------------ conclusion
print()
print("CONCLUSION (conditional only on derivation.py's PROVED pin + Worley):")
print(f"  no k=11, N=4 solution with Y = n+6 <= 10^100.")
print(f"  With the banked d <= 220 certificate and the k=11 quotient confinement")
print(f"  (d >= 221 => n >= 7*221-1 => Y >= 1552), every solution has")
print(f"  d = X - Y > (134/1000)*Y > 1.34*10^99.")
print(f"  Verified d-bound: NO k=11, N=4 solution with d <= 10^99.")
