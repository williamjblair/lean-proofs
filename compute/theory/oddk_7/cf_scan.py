#!/usr/bin/env python3
"""
Erdos 686, k=7, N=4: continued fraction of q = 4^(1/7) (pure-integer,
certificate-carrying) and the exact scan of the Fatou/Legendre candidate
family for  P7(X) = 4 P7(Y),  P7(T) = T^7 - 14T^5 + 49T^3 - 36T,
X = n+d+4, Y = n+4.

Input from derivation.py (all PROVED there by exact sign checks):
  every solution with Y >= 250 satisfies |q - X/Y| <= C_7/Y^2,
  C_7 = 2(4 - r^5)/r^6, r = 60949/50000;  C_7 < 399/500 = 0.798 < 1.

Confinement (C_7 in (1/2, 1) -- Fatou class, exactly as k=5):
  write X/Y = g*(a/b) in lowest terms.
  * g >= 2:  |q - a/b| < C_7/(g^2 b^2) <= C_7/4 / b^2 < 1/(2b^2), so by
    LEGENDRE a/b is a convergent p_i/q_i; the classical lower bound
    |q - p_i/q_i| > 1/((a_{i+1}+2) q_i^2) then forces g^2 < C_7*(a_{i+1}+2),
    i.e. g^2 <= a_{i+1} + 1.
  * g = 1:  by FATOU (|q - a/b| < 1/b^2), a/b is a convergent p_i/q_i or a
    mediant neighbour (p_{i+1} +- p_i)/(q_{i+1} +- q_i).
  Superset actually scanned (covers the weaker, easier-to-formalize
  "semiconvergent" statement as well):
    Y in {g*q_i : 1 <= g <= 50}                       (needs max a_{i+1} <= 2498)
      u {g*(a*q_i + q_{i-1}) : 1 <= a <= a_{i+1}+1, 1 <= g <= 8}
  (a = a_{i+1}-1 and a_{i+1}+1 give q_{i+1} -+ q_i, so both Fatou mediants
  are included; all intermediate fractions are included with margin g <= 8.)

This script (ALL decision logic exact integer arithmetic):
  1. generates >= 320 partial quotients of cf(4^(1/7)) purely from integer
     7th-power sign checks u^7 vs 4 v^7 (semiconvergent straddle certificate
     for every floor -- no floating point anywhere in the decision path);
     cross-checks against mpmath at 1500 digits, and against the classical
     alternation p_i^7 - 4 q_i^7 sign = (-1)^(i+1);
  2. exhaustively verifies (*) has NO solution with 4 <= Y <= 10^6
     (monotone integer bisection in X -- unconditional, no bracket needed);
  3. brute-enumerates all Y <= 2*10^6 with ||q Y|| < 0.95/Y (generous vs the
     true deviation ~0.7974/Y) via exact 7th-power comparisons, classifies
     each against the convergent/semiconvergent family (empirical Fatou
     validation), and checks (*) exactly on each;
  4. enumerates the candidate family up to Y <= 10^120 (>> task bound 10^100)
     and checks (*) exactly on every (X, Y) with X in iroot7(4Y^7) +- 2.

Result: ZERO solutions.  With the banked d <= 220 certificate and the
confinement 4d <= n+1 < 5d (d >= 221), this verifies: no k=7, N=4 solution
with Y = n+4 <= 10^120, hence none with d <= 2*10^119 (conditional only on
the PROVED pinning chain + classical Legendre/Fatou).
"""

import sys

BOUND_MAIN = 10**120     # scan bound for the candidate family (task: 10^100)
BOUND_TASK = 10**100
N_TERMS = 320
G_CONV = 50              # multiples of convergent denominators (g^2 <= a+1 < 2500)
G_SEMI = 8               # margin multiples of semiconvergent denominators

# ---------------------------------------------------------------- helpers


def iroot7(n):
    """floor(n^(1/7)) exact, pure integer arithmetic."""
    if n < 0:
        raise ValueError
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + 6) // 7)     # r >= n^(1/7)
    while True:
        r2 = (6 * r + n // r**6) // 7        # integer Newton step
        if r2 >= r:
            break
        r = r2
    while r**7 > n:
        r -= 1
    while (r + 1)**7 <= n:
        r += 1
    return r


def P7(t):
    t2 = t * t
    return t * (t2 - 1) * (t2 - 4) * (t2 - 9)


def eq_holds(Xv, Yv):
    return P7(Xv) == 4 * P7(Yv)


def side(u, v):
    """sign of u/v - 4^(1/7) for u, v > 0: exact 7th-power comparison."""
    lhs, rhs = u**7, 4 * v**7
    assert lhs != rhs, "4^(1/7) rational?!"
    return 1 if lhs > rhs else -1


# ---------------------------------------------- 1. continued fraction, exact
# a0 = 1 since 1^7 < 4 < 2^7.
assert side(1, 1) == -1 and side(2, 1) == 1
terms = [1]
p_prev, q_prev = 1, 0            # p_{-1}/q_{-1} ("+infinity side": +1)
p_cur, q_cur = 1, 1              # p_0/q_0 = a0
side_prev, side_cur = 1, side(p_cur, q_cur)
straddle_checks = 0

while len(terms) < N_TERMS:
    # a_{k+1} = max{a >= 1 : semiconvergent s_a on side_prev}; s_a crosses
    # q = 4^(1/7) exactly once as a increases (monotone), so exponential +
    # binary search with exact sign checks is valid.
    def s_side(a):
        return side(a * p_cur + p_prev, a * q_cur + q_prev)

    hi = 1
    while s_side(hi) == side_prev:
        hi *= 2
    lo = hi // 2                                   # s_side(lo) == side_prev or lo == 0
    if lo == 0:
        raise AssertionError("a must be >= 1")
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if s_side(mid) == side_prev:
            lo = mid
        else:
            hi = mid
    a = lo
    # floor certificate (the two integer sign checks that pin a_{k+1}):
    assert s_side(a) == side_prev and s_side(a + 1) == side_cur
    straddle_checks += 2
    terms.append(a)
    p_prev, p_cur = p_cur, a * p_cur + p_prev
    q_prev, q_cur = q_cur, a * q_cur + q_prev
    side_prev, side_cur = side_cur, side(p_cur, q_cur)

# rebuild convergent lists
ps = [1, terms[0]]
qs = [0, 1]
for a in terms[1:]:
    ps.append(a * ps[-1] + ps[-2])
    qs.append(a * qs[-1] + qs[-2])
ps, qs = ps[1:], qs[1:]          # ps[i]/qs[i] = i-th convergent, i >= 0

# classical alternation cross-check: p_i/q_i < q  iff  i even
for i in range(len(ps)):
    assert side(ps[i], qs[i]) == (1 if i % 2 else -1), i

# mpmath cross-check of the terms (diagnostic only; exactness is above)
import mpmath as mp
mp.mp.dps = 1500
v = mp.mpf(4) ** (mp.mpf(1) / 7)
float_terms = []
for _ in range(N_TERMS):
    a = int(mp.floor(v))
    float_terms.append(a)
    v = 1 / (v - a)
assert float_terms == terms, "mpmath cross-check mismatch"

print(f"[PASS] cf(4^(1/7)): {N_TERMS} terms generated purely from integer "
      f"7th-power sign checks ({straddle_checks} straddle certificates), "
      f"alternation + mpmath(1500dps) cross-checks OK")
print(f"       terms[:40] = {terms[:40]}")
amax = max(terms[1:])
print(f"       max partial quotient a_i, 1 <= i < {N_TERMS}: {amax} "
      f"(at i = {terms.index(amax)})")
assert amax <= 2498, "g <= 50 superset bound needs enlarging!"
k100 = next(i for i in range(len(qs)) if qs[i] > BOUND_TASK)
k120 = next(i for i in range(len(qs)) if qs[i] > BOUND_MAIN)
print(f"       q_i exceeds 10^100 at i = {k100}, 10^120 at i = {k120} "
      f"(of {len(qs)} verified)")

# ------------------------------------- 2. exhaustive small-Y check (Y <= 1e6)
print(f"exhaustive direct check of P7(X) = 4*P7(Y) for 4 <= Y <= 10^6 ...")
Y_EXH = 10**6
exh_sols = []
for Yv in range(4, Y_EXH + 1):
    target = 4 * P7(Yv)
    lo, hi = Yv + 1, 2 * Yv + 10          # P7 monotone on [3,oo); X < 2Y here
    while lo < hi:
        mid = (lo + hi) // 2
        if P7(mid) < target:
            lo = mid + 1
        else:
            hi = mid
    if P7(lo) == target:
        exh_sols.append((Yv, lo))
assert exh_sols == [], exh_sols
print(f"[PASS] no solution with 4 <= Y <= 10^6 (monotone bisection, exact; "
      f"unconditional -- covers n + 4 <= 10^6, all d)")

# ------------------------- 3. brute ||qY|| window scan, Y <= 2e6 (empirical
#                              Fatou validation + independent cross-check)
print("brute scan Y <= 2*10^6 for ||q*Y|| < 0.95/Y candidates ...")
cand = []
for Yv in range(4, 2_000_001):
    Xv = iroot7(4 * Yv**7)               # X <= qY < X+1
    for XX in (Xv, Xv + 1):
        # |qY - XX| < 19/(20Y)  <=>  (20Y*XX - 19)^7 < 4 (20Y^2)^7 < (20Y*XX + 19)^7
        L = 20 * Yv * XX - 19
        R = 20 * Yv * XX + 19
        mid = 4 * (20 * Yv * Yv) ** 7
        if L**7 < mid < R**7:
            cand.append((Yv, XX))

# classify each candidate against the family (exact)
famY = {}
for i in range(len(qs)):
    if qs[i] > 3 * 10**6:
        break
    for g in range(1, 51):
        famY.setdefault(g * qs[i], f"{g}*q_{i}")
    if i >= 1:
        for a in range(1, terms[i] + 2 if i < len(terms) else 2):
            base = a * qs[i - 1] + (qs[i - 2] if i >= 2 else 0)
            for g in range(1, 9):
                famY.setdefault(g * base, f"{g}*({a}q_{i-1}+q_{i-2})")

print(f"       {len(cand)} candidates; classification + exact equation check:")
brute_sols = []
for (Yv, XX) in cand:
    resid = P7(XX) - 4 * P7(Yv)
    tag = famY.get(Yv, "NOT-IN-FAMILY")
    qf = 4 ** (1 / 7)
    print(f"         Y={Yv:<8} X={XX:<8} Y*|qY-X|~{abs(qf*Yv-XX)*Yv:7.4f}  "
          f"{tag:<18} resid={resid:+d}" if abs(resid) < 10**18 else
          f"         Y={Yv:<8} X={XX:<8} Y*|qY-X|~{abs(qf*Yv-XX)*Yv:7.4f}  "
          f"{tag:<18} resid~{float(resid):+.3e}")
    if eq_holds(XX, Yv):
        brute_sols.append((Yv, XX))
assert brute_sols == []
not_in_family = [(Yv, XX) for (Yv, XX) in cand if Yv not in famY]
assert not_in_family == [], f"Fatou violated empirically?! {not_in_family}"
print(f"[PASS] all {len(cand)} brute candidates lie in the scanned family "
      f"(empirical Fatou/Legendre validation); none satisfies the equation")

# --------------------------- 4. candidate family scan up to Y <= 10^120
print(f"scanning the Fatou/Legendre candidate family up to Y = 10^120 ...")
seenY = set()
checked = 0
found = []
near_misses = []                 # |resid| < Y^4: absurdly generous "near" filter
tight_family = 0                 # size of the THEORY family (not the superset)
for i in range(min(k120 + 1, len(qs))):
    denoms = set()
    for g in range(1, G_CONV + 1):
        denoms.add(g * qs[i])
    ai1 = terms[i + 1] if i + 1 < len(terms) else 1
    # theory family size at this index: g = 1..floor(sqrt(a_{i+1}+1)) multiples
    # of q_i, plus the two Fatou mediants
    g_bound = int((ai1 + 1) ** 0.5)
    while (g_bound + 1)**2 <= ai1 + 1:
        g_bound += 1
    while g_bound**2 > ai1 + 1:
        g_bound -= 1
    tight_family += max(g_bound, 1) + 2
    if i >= 1:
        for a in range(1, ai1 + 2):
            base = a * qs[i - 1] + (qs[i - 2] if i >= 2 else 0)
            for g in range(1, G_SEMI + 1):
                denoms.add(g * base)
    for Yv in denoms:
        if Yv < 4 or Yv > BOUND_MAIN or Yv in seenY:
            continue
        seenY.add(Yv)
        X0 = iroot7(4 * Yv**7)
        for Xv in range(X0 - 2, X0 + 3):
            checked += 1
            if Xv <= Yv:
                continue
            resid = P7(Xv) - 4 * P7(Yv)
            if resid == 0:
                found.append((Yv, Xv))
            elif abs(resid) < Yv**4:
                near_misses.append((Yv, Xv, resid))

n_task = sum(1 for Yv in seenY if Yv <= BOUND_TASK)
print(f"       family size: {len(seenY)} Y-values <= 10^120 "
      f"({n_task} <= 10^100); {checked} (X,Y) pairs checked exactly")
print(f"       tight theory family (g*q_i, g^2 <= a_i+1, + 2 mediants): "
      f"~{tight_family} Y-values over {min(k120 + 1, len(qs))} indices")
print(f"       near-misses (|P7(X)-4P7(Y)| < Y^4): {len(near_misses)}")
for (Yv, Xv, r) in near_misses[:10]:
    print(f"         Y={Yv} X={Xv} resid={r}")
print(f"       exact solutions found: {found}")
assert found == []
print(f"[PASS] no solution on the candidate family up to Y = 10^120")

print()
print("Conclusion: conditional ONLY on the PROVED pinning chain")
print("  |4^(1/7) - X/Y| <= C_7/Y^2 < 1/Y^2  (Y >= 250; derivation.py)")
print("and classical Legendre/Fatou, there is NO k=7, N=4 solution with")
print("  Y = n+4 <= 10^120   (in particular none with Y <= 10^100),")
print("hence (via banked confinement 4d <= n+1 < 5d for d >= 221, and the")
print("banked d <= 220 certificate) none with  d <= 2*10^119.")
