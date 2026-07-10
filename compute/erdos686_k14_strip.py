#!/usr/bin/env python3
"""Exact verification + certificate search for the Erdos686 k=14 strip
221 <= d < 663000 (module ErdosProblems/Erdos686FourteenStrip.lean).

Setting (from ErdosProblems/Erdos686EvenK.lean): w = 2(n+d)+15, v = 2n+15,
S(W) = prod_{l in {1,3,...,13}} (W^2 - l^2), 16384*blockProduct 14 x = S(2x+15),
T = 16*(polynomial part of sqrt(S)) = 16W^7 - 3640W^5 + 202566W^3 - 2656355W,
D = T^2 - 256*S.  With m = T(w) - 2T(v), X = T(w) + 2T(v):
  m*X = D(w) - 4D(v)      (on the curve S(w) = 4 S(v)).
Window (banked): 19w <= 21v + 24, 11v <= 10w + 11, and d >= 221 forces
v >= V0 = 3991 (row_base_lower_k14: 9d <= n+1).

This script verifies:
 1. T, D exactly; m odd (T odd at odd args); 7 | T identically (Fermat).
 2. The m-trap: Delta = D(w)-4D(v) < 0 (univariate shifted certificate at
    v0 = 3991) and -B0*X < Delta for the minimal certifiable B0, keeping a
    LOWER bound for D(w) (not just D(w) >= 0), which halves B0.
    Both linarith combinations are checked as exact polynomial identities
    with nonnegative multipliers.
 3. CANDS = odd multiples of 7 in (0, B0)  (m = -a, a in CANDS).
 4. For each modulus M: okSet(M) = {T(x)-2T(y) mod M : S(x) = 4S(y) mod M}
    (x, y unrestricted for odd M; x, y odd for M a power of 2, where the
    S-curve is vacuous since 2^21 | S(odd)).  Candidate a is killed by M
    iff (-a) mod M not in okSet(M).
 5. Greedy weighted set cover of CANDS by prime moduli (weight p^2 = kernel
    cost of the (ZMod p)^2 decide), then emits the per-prime bad-residue
    lists and verifies the dispatch: every a in CANDS has, for some chosen
    p, (p - a % p) % p in badList(p) with badList(p) disjoint from okSet(p).
"""

import json
import sympy as sp
from sympy import symbols, expand, Poly

W, t, v, w = symbols('W t v w', integer=True)

# ---------------------------------------------------------------- 1. algebra
S = expand(sp.prod([(W**2 - l**2) for l in range(1, 14, 2)]))

# polynomial part of sqrt(S): P = W^7 + p5 W^5 + p3 W^3 + p1 W
p5, p3, p1 = symbols('p5 p3 p1')
P = W**7 + p5*W**5 + p3*W**3 + p1*W
diff = expand(S - P**2)
sol = {}
for b, deg in [(p5, 12), (p3, 10), (p1, 8)]:
    sol[b] = sp.solve(diff.coeff(W, deg).subs(sol), b)[0]
P = expand(P.subs(sol))
T = expand(16 * P)
T_expected = 16*W**7 - 3640*W**5 + 202566*W**3 - 2656355*W
assert expand(T - T_expected) == 0, T
D = expand(T**2 - 256 * S)
D_expected = (1318847348*W**6 - 92807039780*W**4 + 1455430979401*W**2
              + 4674935865600)
assert expand(D - D_expected) == 0, D
print("[1] T, D match the banked EvenK values.")

Tw, Tv = T.subs(W, w), T.subs(W, v)
Dw, Dv = D.subs(W, w), D.subs(W, v)
Sw, Sv = S.subs(W, w), S.subs(W, v)
# m*X = 256(S(w) - 4S(v)) + D(w) - 4D(v)
assert expand((Tw - 2*Tv)*(Tw + 2*Tv) - (256*(Sw - 4*Sv) + Dw - 4*Dv)) == 0
print("[1] identity m*X = 256(S(w)-4S(v)) + D(w) - 4D(v) verified.")

# m odd at odd args: T(W) mod 2 = W  (only odd coefficient is -2656355)
assert all(c % 2 == 0 for c in [16, 3640, 202566]) and 2656355 % 2 == 1
# 7 | T identically: T = 16(W^7 - W) + 7*(-520W^5 + 28938W^3 - 379477W)
assert expand(T - (16*(W**7 - W) + 7*(-520*W**5 + 28938*W**3 - 379477*W))) == 0
print("[1] m odd (T odd at odd W); 7 | T identically (Fermat).")

# ------------------------------------------------------- 2. window certificates
V0 = 3991     # v = 2n+15 >= 2(9*221-1)+15 from row_base_lower_k14 at d = 221

def shifted_ok(poly, v0, strict_const=True):
    cs = Poly(expand(poly.subs(v, v0 + t)), t).all_coeffs()[::-1]
    return all(c >= 0 for c in cs) and (cs[0] > 0 if strict_const else True), cs

# T positivity at V0 (needed for X > 0 at both w and v)
okT, _ = shifted_ok(T.subs(W, v), V0)
assert okT
print(f"[2] T > 0 for W >= {V0}: shifted certificate OK.")

# ---- hDneg:  Delta = D(w) - 4D(v) < 0  for v >= V0, 19w <= 21v+24, v <= w.
# 19^6 D(w) <= 1318847348(21v+24)^6 - 92807039780*19^6 v^4
#              + 1455430979401*19^4 (21v+24)^2 + 4674935865600*19^6
# via h19w6: (19w)^6 <= (21v+24)^6 ; hw4: v^4 <= w^4 ; h19w2: (19w)^2 <= (21v+24)^2.
Psi = expand(4*19**6*Dv
             - (1318847348*(21*v+24)**6 - 92807039780*19**6*v**4
                + 1455430979401*19**4*(21*v+24)**2 + 4674935865600*19**6))
okN, _ = shifted_ok(Psi, V0)
assert okN
# exact linarith identity: 19^6(4D(v)-D(w)) = Psi + 1318847348*A6 +
#   92807039780*19^6*A4 + 1455430979401*19^4*A2, with nonneg multipliers,
# A6 = (21v+24)^6-(19w)^6 >= 0, A4 = w^4-v^4 >= 0, A2 = (21v+24)^2-(19w)^2 >= 0
A6 = (21*v+24)**6 - (19*w)**6
A4 = w**4 - v**4
A2 = (21*v+24)**2 - (19*w)**2
assert expand(19**6*(4*Dv - Dw)
              - (Psi + 1318847348*A6 + 92807039780*19**6*A4
                 + 1455430979401*19**4*A2)) == 0
print(f"[2] hDneg certificate Psi > 0 at v >= {V0}: OK (identity verified).")

# ---- hDlo:  -B0*X < Delta,  i.e.  B0*X + D(w) - 4D(v) > 0, via lower bounds
#  scaled by 10^7*19^5:
#  T(w): 16*19^5(11v-11)^7 - 3640*10^7(21v+24)^5 + 202566*10^7*19^5 v^3
#        - 2656355*10^7*19^4 (21v+24)
#  D(w): 10*19*(1318847348*19^4(11v-11)^6 - 92807039780*10^6(21v+24)^4
#        + 1455430979401*10^6*19^4 v^2 + 4674935865600*10^6*19^4)
def Phi(B0):
    Tw_low = (16*19**5*(11*v-11)**7 - 3640*10**7*(21*v+24)**5
              + 202566*10**7*19**5*v**3 - 2656355*10**7*19**4*(21*v+24))
    Dw_low = 10*19*(1318847348*19**4*(11*v-11)**6
                    - 92807039780*10**6*(21*v+24)**4
                    + 1455430979401*10**6*19**4*v**2
                    + 4674935865600*10**6*19**4)
    return expand(B0*(Tw_low + 2*10**7*19**5*Tv) + Dw_low - 4*10**7*19**5*Dv)

lo, hi = 1, 10**6
while lo < hi:                       # minimal certifiable B0
    mid = (lo + hi) // 2
    lo, hi = (lo, mid) if shifted_ok(Phi(mid), V0)[0] else (mid + 1, hi)
B0 = lo
assert shifted_ok(Phi(B0), V0)[0] and not shifted_ok(Phi(B0 - 1), V0)[0]
# exact linarith identity with nonneg multipliers:
B0s = symbols('B0', positive=True)
A7 = (10*w)**7 - (11*v-11)**7      # h10w7 (from 11v <= 10w+11, v>=1)
A5 = (21*v+24)**5 - (19*w)**5      # h19w5 (from 19w <= 21v+24, w>0)
A3 = w**3 - v**3                   # hw3
A1 = (21*v+24) - 19*w              # hlink
B6 = (10*w)**6 - (11*v-11)**6      # h10w6
B4 = (21*v+24)**4 - (19*w)**4      # h19w4
B2 = w**2 - v**2                   # hw2
lhs = expand(10**7*19**5*(B0s*(Tw + 2*Tv) + Dw - 4*Dv))
rhs = expand(Phi(B0s.subs({}, ) if False else B0s)  # Phi with symbolic B0
             ) if False else None
PhiB = expand(B0s*(16*19**5*(11*v-11)**7 - 3640*10**7*(21*v+24)**5
                   + 202566*10**7*19**5*v**3 - 2656355*10**7*19**4*(21*v+24)
                   + 2*10**7*19**5*Tv)
              + 10*19*(1318847348*19**4*(11*v-11)**6
                       - 92807039780*10**6*(21*v+24)**4
                       + 1455430979401*10**6*19**4*v**2
                       + 4674935865600*10**6*19**4)
              - 4*10**7*19**5*Dv)
assert expand(lhs - (PhiB + B0s*16*19**5*A7 + B0s*3640*10**7*A5
                     + B0s*202566*10**7*19**5*A3 + B0s*2656355*10**7*19**4*A1
                     + 10*19*1318847348*19**4*B6 + 10*19*92807039780*10**6*B4
                     + 10*19*1455430979401*10**6*19**4*B2)) == 0
print(f"[2] hDlo: minimal certifiable B0 = {B0} at v0 = {V0} "
      "(identity with nonneg multipliers verified).")

# --------------------------------------------------------------- 3. candidates
CANDS = [a for a in range(7, B0, 14)]     # m = -a, a odd multiple of 7, a < B0
print(f"[3] |CANDS| = {len(CANDS)} (a = 7, 21, ..., {CANDS[-1]}).")

# --------------------------------------------------------------- 4. okSets
Scoef = [int(c) for c in Poly(S, W).all_coeffs()[::-1]]
Tcoef = [int(c) for c in Poly(T, W).all_coeffs()[::-1]]

def evalmod(coefs, x, M):
    r = 0
    for c in reversed(coefs):
        r = (r * x + c) % M
    return r

def okset(M, odd_only=False):
    xs = [x for x in range(M) if (x % 2 == 1 or not odd_only)]
    Sx = {x: evalmod(Scoef, x, M) for x in xs}
    Tx = {x: evalmod(Tcoef, x, M) for x in xs}
    from collections import defaultdict
    byS = defaultdict(list)
    for x in xs:
        byS[Sx[x]].append(Tx[x])
    ok = set()
    for y in xs:
        for tx in byS.get((4 * Sx[y]) % M, ()):
            ok.add((tx - 2 * Tx[y]) % M)
    return ok

def sieve(n):
    isp = [True] * (n + 1)
    isp[0:2] = [False, False]
    for i in range(2, int(n**0.5) + 1):
        if isp[i]:
            isp[i*i::i] = [False] * len(isp[i*i::i])
    return [p for p in range(2, n + 1) if isp[p]]

kills = {}
for p in sieve(1000):
    if p < 11:
        continue
    ok = okset(p)
    if len(ok) == p:
        continue
    ks = {a for a in CANDS if (-a) % p not in ok}
    if ks:
        kills[p] = (ok, ks)

# composite moduli of interest (report only)
for M in (16, 32, 64, 128):
    ok = okset(M, odd_only=True)
    hit = {a for a in CANDS if (-a) % M not in ok}
    print(f"[4] M={M} (odd x,y): |okSet|={len(ok)}/{M}, kills {len(hit)}")
for M in (49, 343):
    ok = okset(M)
    hit = {a for a in CANDS if (-a) % M not in ok}
    print(f"[4] M={M}: |okSet|={len(ok)}/{M}, kills {len(hit)}")

frac = sorted(((len(ks) / len(CANDS), p) for p, (_, ks) in kills.items()),
              reverse=True)
print(f"[4] primes 11..997 with nonempty kill sets: {len(kills)}; top 10 by "
      f"fraction: {[(p, f'{f:.2f}') for f, p in frac[:10]]}")

# --------------------------------------------------- 5. greedy weighted cover
remaining = set(CANDS)
cover = []
while remaining:
    best = None
    for p, (_, ks) in kills.items():
        gain = len(ks & remaining)
        if gain == 0:
            continue
        score = gain / (p * p)          # kernel cost ~ p^2
        if best is None or score > best[0]:
            best = (score, p, ks)
    if best is None:
        break
    _, p, ks = best
    cover.append(p)
    remaining -= ks
print(f"[5] greedy cover: primes {cover}; leftover = {sorted(remaining)}")
assert not remaining, f"L3 needed for {sorted(remaining)}"

# per-prime bad lists: exactly the residues of assigned candidates
assigned = {}
todo = set(CANDS)
for p in cover:
    ks = kills[p][1] & todo
    assigned[p] = sorted({(-a) % p for a in ks})
    todo -= ks
assert not todo
for p in cover:
    assert not (set(assigned[p]) & kills[p][0]), p    # disjoint from okSet
# dispatch check: every candidate hits some badList
for a in CANDS:
    assert any((p - a % p) % p in assigned[p] for p in cover), a
print("[5] dispatch verified: every candidate killed by its assigned prime.")
print(f"[5] total kernel pairs = {sum(p*p for p in cover)}")
for p in cover:
    print(f"    p={p:4d}: badList ({len(assigned[p])} residues) = {assigned[p]}")

out = {"V0": V0, "B0": B0, "num_cands": len(CANDS),
       "cover": [{"p": p, "bad": assigned[p]} for p in cover]}
with open("compute/artifacts/k14_strip_cover.json", "w") as f:
    json.dump(out, f, indent=1)
print("[5] wrote compute/artifacts/k14_strip_cover.json")
