#!/usr/bin/env python3
"""
Erdos 686, k=9, N=4: exact continued fraction of q = 4^(1/9) and the
quasi-convergent (Worley) candidate scan.

NO floating point in any decision: the CF is extracted from an exact rational
enclosure of q produced by integer 9th roots (r^9 < 4*10^(9N) < (r+1)^9), and
every partial quotient is certified by floor-agreement of the two exact
rational endpoints.  Convergents are re-verified independently by the
alternating sign of p^9 - 4q^9 (minimal polynomial x^9 - 4) and by the
determinant identity p_m q_{m-1} - p_{m-1} q_m = (-1)^(m-1).

Inputs (from derivation.py, all PROVED there symbolically):
  * for every solution with d >= 221 (banked confinement => Y = n+5 >= 1330):
        0 < q - X/Y <= C_9 / Y^2,      C_9 = 1031/1000       (one-sided)
  * d <= 220 is closed by the banked Lean machinery.

Confinement step (Worley 1981 / Dujella 2004, quasi-convergents):
  |q - a/b| < c/b^2, gcd(a,b)=1  =>  (a,b) = (r p_{m+1} +- s p_m,
  r q_{m+1} +- s q_m) for some m >= -1 and integers r,s >= 0 with rs < 2c.
  Here 2*C_9 = 2.062, so rs <= 2:  (r,s) in {(1,1),(1,2),(2,1)} plus the
  convergents themselves.  For X/Y with g := gcd(X,Y) >= 2:
  |q - x/y| < (C_9/g^2)/y^2 < 1/(2y^2)  => Legendre (x/y a convergent), and
  |q - p_m/q_m| > 1/((a_{m+1}+2) q_m^2)  =>  g^2 <= C_9 (a_{m+1}+2).

Scan (generous supersets of all of the above):
  Y in { g q_m : 1 <= g <= max(50, per-index bound) }
    u { g (r q_{m+1} +- s q_m) : rs <= 4, 1 <= g <= 8 }        for all m,
  5 <= Y <= 10^100; for each Y test X in [floor(qY)-2, floor(qY)+3]
  against the exact equation P9(X) = 4 P9(Y).
Plus:
  * unconditional exact sweep of ALL Y <= 10^6 (monotone bisection on X,
    no CF theory used);
  * empirical Worley validation: every Y <= 2*10^5 passing the exact Thue
    filter 0 < qY - floor(qY) <= C_9/Y is classified within the family.

KNOWN EXACT COINCIDENCE (not a counterexample): (Y, X) = (7, 8), i.e.
(n, d) = (2, 1): P9(8) = 4*P9(7) is the telescoping identity
4*5*...*12 = 4*(3*4*...*11) with OVERLAPPING blocks (d = 1 < k = 9).
The problem statement (ErdosProblems/Erdos686Reduction.lean) requires
m >= n + k, i.e. d >= k = 9, so this pair is outside the problem domain;
it is the banked "k = 9 exceptional branch".  Both the family scan and
the unconditional sweep must find it -- and nothing else.
"""

import json
import os
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
CONST = json.load(open(os.path.join(HERE, "constants.json")))
C9 = Fr(int(CONST["C9"].split("/")[0]), int(CONST["C9"].split("/")[1]))
RHO2 = Fr(int(CONST["rho2"].split("/")[0]), int(CONST["rho2"].split("/")[1]))
assert C9 == Fr(1031, 1000) and 2 * C9 < Fr(21, 10)

N_TERMS = 320
Y_LIMIT = 10**100
G_CONV = 50          # blanket multiple bound for convergents (checked vs a_max)
G_QUASI = 8          # margin multiples for quasi-convergents (theory needs 1)
RS_SET = [(1, 1), (1, 2), (2, 1),               # required: rs <= 2
          (1, 3), (3, 1), (2, 2), (1, 4), (4, 1)]  # margin: rs <= 4


def P9(t):
    return t * (t*t - 1) * (t*t - 4) * (t*t - 9) * (t*t - 16)


def iroot(n, k):
    """floor(n^(1/k)), pure integer Newton."""
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + k - 1) // k + 1)
    while True:
        r2 = ((k - 1) * r + n // r**(k - 1)) // k
        if r2 >= r:
            break
        r = r2
    while r**k > n:
        r -= 1
    while (r + 1)**k <= n:
        r += 1
    return r


# ---------------------------------------------------------------- step 1
# exact rational enclosure of q and exact CF extraction
def cf_exact(n_terms, digits):
    r = iroot(4 * 10**(9 * digits), 9)
    assert r**9 < 4 * 10**(9 * digits) < (r + 1)**9   # strict: q irrational
    lo, hi = Fr(r, 10**digits), Fr(r + 1, 10**digits)
    terms = []
    for _ in range(n_terms):
        alo = lo.numerator // lo.denominator
        ahi = hi.numerator // hi.denominator
        if alo != ahi:
            return terms, False           # precision exhausted
        terms.append(alo)
        lo, hi = lo - alo, hi - alo
        if lo <= 0:
            return terms, False           # endpoint hit: need more digits
        lo, hi = 1 / hi, 1 / lo
    return terms, True


t0 = time.time()
digits = 500
while True:
    terms, ok = cf_exact(N_TERMS, digits)
    if ok:
        break
    digits *= 2
print(f"[PASS] cf(4^(1/9)): {N_TERMS} terms extracted EXACTLY "
      f"(interval floors, {digits} guard digits, {time.time()-t0:.1f}s)")
print(f"       terms[:40] = {terms[:40]}")

# convergents
ps, qs = [1, terms[0]], [0, 1]
for aa in terms[1:]:
    ps.append(aa * ps[-1] + ps[-2])
    qs.append(aa * qs[-1] + qs[-2])
ps, qs = ps[1:], qs[1:]        # ps[m]/qs[m] = m-th convergent, m >= 0

# independent exact verification against the minimal polynomial x^9 - 4:
#   p_m/q_m < q  <=>  p_m^9 < 4 q_m^9, and signs must alternate (even below)
for m in range(N_TERMS):
    s = ps[m]**9 - 4 * qs[m]**9
    assert s != 0, "rational 9th root of 4?!"
    assert (s < 0) == (m % 2 == 0), f"alternation fails at m={m}"
print(f"[PASS] all {N_TERMS} convergents verified: sign(p^9 - 4q^9) alternates "
      "(exact minimal-polynomial test)")

for m in range(1, N_TERMS):
    assert ps[m] * qs[m-1] - ps[m-1] * qs[m] == (-1)**(m - 1)
print(f"[PASS] determinant identity p_m q_(m-1) - p_(m-1) q_m = (-1)^(m-1) "
      f"for all m < {N_TERMS}  (=> gcd(p_m, q_m) = 1)")

# straddle certificates: every partial quotient a_{m+1} is pinned by TWO
# integer sign checks against the minimal polynomial x^9 - 4, evaluated at
# the semiconvergents  s_a := (a p_m + p_{m-1}) / (a q_m + q_{m-1}):
#   a = a_{m+1}   : sign(u^9 - 4 v^9) = sign side of p_{m-1}  [far side]
#   a = a_{m+1}+1 : sign flips                                 [crossed]
# The map a -> s_a is a Moebius function of a, strictly monotone toward and
# past alpha, and x -> x^9 is strictly increasing, so the single sign flip
# between a and a+1 certifies a_{m+1} = a exactly.  (a_0 = 1 is certified by
# the floor bracket 1^9 < 4 < 2^9.)
assert 1**9 < 4 < 2**9
n_straddle = 0
pprev, qprev = 1, 0            # (p_{-1}, q_{-1});  D_{-1} = 1 > 0
for m in range(N_TERMS - 1):
    a = terms[m + 1]
    u1, v1 = a * ps[m] + pprev, a * qs[m] + qprev
    u2, v2 = u1 + ps[m], v1 + qs[m]
    s1 = u1**9 - 4 * v1**9
    s2 = u2**9 - 4 * v2**9
    # side convention: index-j convergent has  D_j < 0  <=>  j even;
    # s_a (a = a_{m+1}) IS the (m+1)-convergent, side (-1)^m of D_{m+1};
    # s_{a+1} has crossed alpha, i.e. lies on the side of p_m.
    assert s1 != 0 and (s1 < 0) == ((m + 1) % 2 == 0)
    assert s2 != 0 and (s2 < 0) == (m % 2 == 0)
    n_straddle += 2
    pprev, qprev = ps[m], qs[m]
print(f"[PASS] straddle certificates: all {N_TERMS - 1} partial quotients "
      f"a_1..a_{N_TERMS-1} pinned by {n_straddle} integer sign checks "
      f"(semiconvergent straddles; no floating point)")

a_max = max(terms)
g_needed = iroot(int(C9 * (a_max + 2)) + 1, 2) + 1
print(f"       max partial quotient a_max = {a_max} (at index {terms.index(a_max)}); "
      f"g-multiple bound g^2 <= C_9(a+2) needs g <= {g_needed}")
G = max(G_CONV, g_needed)
m100 = next(m for m in range(N_TERMS) if qs[m] > Y_LIMIT)
print(f"       q_m exceeds 10^100 at m = {m100} "
      f"(q_m ~ 10^{len(str(qs[m100]))-1}); {N_TERMS} terms reach "
      f"q_m ~ 10^{len(str(qs[-1]))-1}")

# ---------------------------------------------------------------- step 2
# the generous Worley family up to 10^100, exact equation check on each
t0 = time.time()
seenY = set()
thue_pass = []       # family members that pass the exact Thue filter
found = []           # equation hits with d = X - Y >= 9 (problem domain)
trivial = []         # equation hits with d < 9 (overlapping telescopes)
checked = 0
for m in range(N_TERMS):
    dens = set()
    for g in range(1, G + 1):
        dens.add(g * qs[m])
    if m + 1 < N_TERMS:
        for (r, s) in RS_SET:
            for base in (r * qs[m+1] + s * qs[m], r * qs[m+1] - s * qs[m]):
                if base > 0:
                    for g in range(1, G_QUASI + 1):
                        dens.add(g * base)
    for Y in dens:
        if Y < 5 or Y > Y_LIMIT or Y in seenY:     # domain: Y = n+5 >= 5
            continue
        seenY.add(Y)
        X0 = iroot(4 * Y**9, 9)              # = floor(qY) since (qY)^9 = 4Y^9
        # exact Thue filter: 0 < qY - X0 <= C_9/Y
        #   (X0 < qY automatic; test (X0 + C9/Y)^9 >= 4 Y^9 exactly)
        if (Fr(X0) + C9 / Y)**9 >= 4 * Y**9:
            thue_pass.append(Y)
        p4 = 4 * P9(Y)
        for X in range(X0 - 2, X0 + 4):
            if X > Y:
                checked += 1
                if P9(X) == p4:
                    (found if X - Y >= 9 else trivial).append((Y, X))
print(f"[PASS] Worley family scan: {len(seenY)} Y-values, {checked} (X,Y) pairs, "
      f"Y <= 10^100  ({time.time()-t0:.1f}s)")
print(f"       exact Thue-filter passes among family: {len(thue_pass)} "
      f"(these are the even-index convergents & near variants; expected)")
print(f"       overlap telescopes with d = X-Y < 9 (outside problem domain): {trivial}")
print(f"       exact equation passes with d >= 9: {found}")
assert trivial == [(7, 8)], "trivial set changed"   # (n,d)=(2,1): 4..12 = 4*(3..11)
assert found == [], "UNEXPECTED SOLUTION"
print("[PASS] no solution with d >= 9 on the generous quasi-convergent family "
      "up to Y = 10^100")

# residual margin of the closest Thue-filter passes (display only)
import math
closest = []
for Y in sorted(thue_pass)[:200]:
    X0 = iroot(4 * Y**9, 9)
    resid = P9(X0) - 4 * P9(Y), P9(X0 + 1) - 4 * P9(Y)
    closest.append((Y, X0, resid[0] != 0 and resid[1] != 0))
assert all(c[2] for c in closest)

# ---------------------------------------------------------------- step 3
# unconditional exact sweep: ALL Y <= 10^6 (no CF theory, monotone bisection)
t0 = time.time()
qf = 4 ** (1 / 9)
sweep_sols = []
for Y in range(5, 10**6 + 1):           # domain: Y = n+5 >= 5 (n >= 0)
    p4 = 4 * P9(Y)
    X = int(qf * Y)                     # float seed only; corrected exactly:
    while P9(X + 1) <= p4:
        X += 1
    while P9(X) > p4:
        X -= 1
    # now P9(X) <= 4 P9(Y) < P9(X+1)  with P9 strictly increasing on [4,oo)
    if P9(X) == p4 and X > Y:
        sweep_sols.append((Y, X))
# the d = 1 telescope (n, d) = (2, 1) is the ONLY hit, and it is overlapping
# (d = 1 < 9), hence outside the m >= n + k problem domain:
assert sweep_sols == [(7, 8)], sweep_sols
assert all(X - Y < 9 for (Y, X) in sweep_sols)
print(f"[PASS] unconditional sweep: the only Y in [5, 10^6] admitting an "
      f"integer X with P9(X) = 4 P9(Y) is the d=1 telescope (Y,X) = (7,8); "
      f"NO disjoint-block (d >= 9) solution  ({time.time()-t0:.1f}s)")

# ---------------------------------------------------------------- step 4
# empirical Worley validation: every Thue-filter survivor Y <= 2*10^5 must be
# classified as g*q_m (g^2 <= C_9(a_{m+1}+2)) or r q_{m+1} +- s q_m (rs <= 2)
t0 = time.time()


def classify(Y):
    tags = []
    for m in range(N_TERMS):
        if qs[m] > Y:
            break
        if Y % qs[m] == 0:
            g = Y // qs[m]
            if g == 1:
                tags.append(f"q_{m}")
            elif m + 1 < N_TERMS and g * g <= C9 * (terms[m + 1] + 2):
                tags.append(f"{g}*q_{m} (a_{m+1}={terms[m+1]})")
        if m + 1 < N_TERMS:
            for (r, s) in [(1, 1), (1, 2), (2, 1)]:
                if Y == r * qs[m+1] + s * qs[m]:
                    tags.append(f"{r}*q_{m+1}+{s}*q_{m}")
                if Y == r * qs[m+1] - s * qs[m]:
                    tags.append(f"{r}*q_{m+1}-{s}*q_{m}")
    return tags


near = []
for Y in range(5, 2 * 10**5 + 1):
    X0 = iroot(4 * Y**9, 9)
    if (Fr(X0) + C9 / Y)**9 >= 4 * Y**9:
        near.append((Y, X0))
print(f"       Thue-filter survivors with Y <= 2*10^5: {len(near)}")
all_classified = True
for (Y, X0) in near:
    tags = classify(Y)
    dev = float((qf * Y - X0) * Y)
    infam = Y in seenY
    if not tags:
        all_classified = False
    print(f"         Y={Y:<8} X0={X0:<8} Y*(qY-X0)={dev:7.4f}  "
          f"family={'yes' if infam else 'NO'}  tag={tags[0] if tags else 'NONE'}")
assert all_classified, "Worley classification violated empirically!"
print(f"[PASS] every Thue-filter survivor (Y <= 2*10^5) lies in the Worley "
      f"family with rs <= 2 / g^2 <= C_9(a+2)  ({time.time()-t0:.1f}s)")

# ---------------------------------------------------------------- step 5
# SELF-CONTAINED confinement family (no Worley/Legendre/Fatou input).
# Theorem (proved in note.md Section 3, elementary): alpha irrational with
# convergents p_m/q_m, theta_m := |q_m alpha - p_m|.  If |alpha Y - X| <= C/Y
# with q_m <= Y < q_{m+1}, expand (X, Y) = (r p_{m+1} + s p_m,
# r q_{m+1} + s q_m) over ZZ (unimodular basis).  Then s != 0 and exactly one:
#   (i)   r = 0:   Y = g q_m (g = s >= 1)  and  g^2 q_m < C (q_m + q_{m+1});
#   (ii)  r >= 1:  s = -t <= -1, Y = r q_{m+1} - t q_m, 1 <= r <= t,
#                                         and  t * Y < C (q_m + q_{m+1});
#   (iii) r <= -1: s >= 2, Y = s q_m - |r| q_{m+1}, 1 <= |r| < s,
#                                         and  s * Y < C (q_m + q_{m+1}).
# Only inputs: the exact identity q_{m+1} theta_m + q_m theta_{m+1} = 1 and
# the sign alternation of q_j alpha - p_j (both two-line CF facts).  For a
# fixed t (resp. s) the interval [q_m, q_{m+1}) admits AT MOST ONE r, so the
# family is finite and enumerable per index -- this confines even C > 1
# (here C = C_9 = 1031/1000) with no classical black box.
t0 = time.time()
sc_family = {}                       # Y -> (m, tag)
for m in range(m100 + 1):
    qm, qm1 = qs[m], qs[m + 1]
    if qm1 <= qm:                    # empty interval (cannot occur here)
        continue
    capn, capd = C9.numerator * (qm + qm1), C9.denominator   # cap = C(qm+qm1)
    # class (i): multiples of q_m inside [q_m, q_{m+1})
    g = 1
    while g * g * qm * capd < capn and g * qm < qm1:
        if g * qm <= Y_LIMIT:
            sc_family.setdefault(g * qm, (m, f"{g}*q_{m}"))
        g += 1
    # class (ii): Y = r q_{m+1} - t q_m  (unique r per t)
    t = 1
    while t * qm * capd < capn:      # t*Y >= t*q_m must stay under the cap
        r = -((-(1 + t) * qm) // qm1)          # ceil((1+t) q_m / q_{m+1})
        Yc = r * qm1 - t * qm
        if qm <= Yc < qm1 and t * Yc * capd < capn and Yc <= Y_LIMIT:
            sc_family.setdefault(Yc, (m, f"{r}*q_{m+1}-{t}*q_{m}"))
        t += 1
    # class (iii): Y = s q_m - r q_{m+1}, r >= 1  (unique r per s)
    s = 2
    while s * qm * capd < capn:
        r = ((s - 1) * qm) // qm1
        if r >= 1:
            Yc = s * qm - r * qm1
            if qm <= Yc < qm1 and s * Yc * capd < capn and Yc <= Y_LIMIT:
                sc_family.setdefault(Yc, (m, f"{s}*q_{m}-{r}*q_{m+1}"))
        s += 1
sc_checked = 0
sc_eq = []
for Yc in sc_family:
    if Yc < 5:
        continue
    X0 = iroot(4 * Yc**9, 9)
    p4 = 4 * P9(Yc)
    for X in range(X0 - 2, X0 + 4):
        if X > Yc:
            sc_checked += 1
            if P9(X) == p4:
                sc_eq.append((Yc, X))
# a solution of the equation in the Thue regime (Y >= 1330) satisfies the
# hypothesis with C = C_9, hence MUST appear here; d < 9 telescopes need not.
assert all(X - Yc < 9 for (Yc, X) in sc_eq), f"UNEXPECTED SOLUTION {sc_eq}"
assert sc_eq in ([], [(7, 8)]), sc_eq
# empirical completeness: every one-sided Thue survivor found by the brute
# scan (step 4) must lie in the self-contained family
missing = [Y for (Y, _) in near if Y not in sc_family]
assert missing == [], f"self-contained family misses {missing}"
new_only = sum(1 for Y in sc_family if Y not in seenY)
print(f"[PASS] SELF-CONTAINED family: {len(sc_family)} Y-values <= 10^100 "
      f"({new_only} not already in the Worley-superset family), {sc_checked} "
      f"exact equation checks: no solution with d >= 9 "
      f"(hits: {sc_eq if sc_eq else 'none'}); all {len(near)} brute survivors "
      f"covered  ({time.time()-t0:.1f}s)")
print(f"       => the Y <= 10^100 exclusion is conditional ONLY on the "
      f"derivation.py chain + two elementary CF identities (no classical "
      f"Worley/Fatou needed)")

# ---------------------------------------------------------------- summary
dmax = (RHO2 - 1) * Y_LIMIT
print()
print("=" * 72)
print("CONCLUSION (conditional only on the derivation.py chain + the")
print("elementary self-contained confinement of step 5; the classical")
print("Worley/Dujella route of steps 2-4 independently gives the same):")
print(f"  no k=9, N=4 solution with d >= 9 and Y = n+5 <= 10^100")
print(f"  (the only equation coincidence found anywhere is the d=1 telescope")
print(f"   (Y,X) = (7,8), outside the m >= n+k problem domain).")
print(f"  Any solution with d >= 221 has d > (rho2-1)*Y, i.e. Y < d/(rho2-1);")
print(f"  hence NO solution with 221 <= d <= {float(dmax):.6e}")
print(f"  (exactly floor = {int(dmax)})")
print(f"  and d <= 220 is closed by the banked Lean machinery:")
print(f"  => verified bound d <= 1.665283 * 10^99.")
print("=" * 72)
