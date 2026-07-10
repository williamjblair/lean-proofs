#!/usr/bin/env python3
"""Exact verification for the Erdos686 even-k (k in {6,8,10,12,14}) N=4 exclusion,
difference-of-squares route (module ErdosProblems/Erdos686EvenK.lean).

For even k set S_k(W) = prod_{l odd, 1<=l<=k-1} (W^2 - l^2), so that
  2^k * blockProduct k x = S_k(2x + k + 1)   (bridge identity).
The equation blockProduct k (n+d) = 4 blockProduct k n becomes S_k(w) = 4 S_k(v)
with w = 2(n+d)+k+1, v = 2n+k+1 both odd, w = v + 2d > v.

Let P_k be the polynomial part of sqrt(S_k), c the minimal power of 2 with
T := c*P integral, and D := T^2 - c^2 S (integer polynomial, deg D < deg T).
Then with m := T(w) - 2 T(v) and X := T(w) + 2 T(v) pure algebra gives
  m * X = c^2 (S(w) - 4 S(v)) + D(w) - 4 D(v) = D(w) - 4 D(v)  =: Delta.
Window: with the banked ratio-window linearizations (w <~ 4^{1/k} v) and the
banked lower bounds v >= V0 (from d >= 221 via row_base_lower_k*):
  Delta < 0            (upper: w below the harmless multiple of v)
  Delta > -B * X       (lower: 4 D(v) - D(w) small versus X)
hence m in (-B, 0).
  k=6 : c=2,  B=1  -> no integer m: contradiction.
  k=8 : c=1,  B=1  -> contradiction.
  k=12: c=1,  B=1  -> contradiction.
  k=10: c=8,  B=25 -> m odd (T odd at odd W), 5 | m (T == 0 mod 5, Fermat)
                      -> m in {-5, -15}; both impossible mod 11 (decide).
  k=14: c=16, B=7  -> needs v >= ~6.6e6, i.e. d >= d0 ~ 3.7e5 only (partial);
                      then m odd(unused), 7 | m (T == 0 mod 7) -> empty window.
All inequality lemmas are proven in Lean by nlinarith from power-monotonicity
hints plus ONE univariate shifted-positivity certificate each; this script
verifies every polynomial identity, every univariate certificate (all shifted
coefficients >= 0, constant > 0), the mod-p facts, and the omega-level link
arithmetic.
"""

import sympy as sp

W, t = sp.symbols('W t', integer=True)
x, vv, ww, nn, dd = sp.symbols('x v w n d', integer=True)

def S_poly(k, var=W):
    return sp.prod([(var**2 - l**2) for l in range(1, k, 2)])

def sqrt_poly_part(k):
    S = sp.expand(S_poly(k)); h = k // 2
    bs = [sp.Symbol(f'b{i}') for i in range(1, h // 2 + 1)]
    P = W**h + sum(b * W**(h - 2*i) for i, b in enumerate(bs, start=1))
    diff = sp.expand(S - P**2); sol = {}
    for b, i in zip(bs, range(1, len(bs) + 1)):
        eq = diff.coeff(W, 2*h - 2*i).subs(sol)
        sol[b] = sp.solve(eq, b)[0]
    return sp.expand(P.subs(sol))

def check_shift(name, poly, shift, var=None):
    """poly(var) must be > 0 for var >= shift via all shifted coeffs >= 0."""
    var = var or W
    p = sp.expand(poly.subs(var, shift + t))
    cs = sp.Poly(p, t).all_coeffs()[::-1]
    ok = all(c >= 0 for c in cs) and cs[0] > 0
    print(f"  [shift] {name} @ {shift}: nonneg shifted coeffs & const>0: {ok}")
    assert ok, (name, cs)

def min_pos_threshold(poly, var=W):
    p = sp.Poly(sp.expand(poly), var)
    assert p.LC() > 0
    bound = 1
    for r in sp.real_roots(poly):
        bound = max(bound, sp.floor(r) + 1)
    assert all(poly.subs(var, u) > 0 for u in range(int(bound), int(bound) + 3))
    return int(bound)

DATA = {
    6:  dict(c=2,  q=3, V0=1331, B=1,  Aup=24, Bup=19),
    8:  dict(c=1,  q=5, V0=2217, B=1,  Aup=25, Bup=21),
    10: dict(c=8,  q=6, V0=2661, B=25, Aup=23, Bup=20, Alo=8,  Blo=7),
    12: dict(c=1,  q=8, V0=3547, B=1,  Aup=73, Bup=65),
    14: dict(c=16, q=9, V0=None, B=7,  Aup=21, Bup=19, Alo=11, Blo=10),
}

print("=" * 72)
for k, cfg in DATA.items():
    c, q = cfg['c'], cfg['q']
    S = sp.expand(S_poly(k))
    P = sqrt_poly_part(k)
    T = sp.expand(c * P)
    D = sp.expand(T**2 - c*c*S)
    print(f"k={k}: c={c}  T = {T}")
    print(f"        D = {D}")
    assert all(sp.Integer(cf) == cf for cf in sp.Poly(T, W).all_coeffs())
    assert sp.degree(D, W) < sp.degree(T, W)
    # bridge identity  prod_{i=1..k}(2x+2i) == S_k(2x+k+1)
    assert sp.expand(sp.prod([2*x + 2*i for i in range(1, k+1)]) - S.subs(W, 2*x + k + 1)) == 0
    # m*X identity: (T(w)-2T(v))(T(w)+2T(v)) - (D(w)-4D(v)) == c^2 (S(w)-4S(v))
    Tw, Tv = T.subs(W, ww), T.subs(W, vv)
    Dw, Dv = D.subs(W, ww), D.subs(W, vv)
    Sw, Sv = S.subs(W, ww), S.subs(W, vv)
    assert sp.expand((Tw - 2*Tv)*(Tw + 2*Tv) - (Dw - 4*Dv) - c*c*(Sw - 4*Sv)) == 0
    print(f"  identity (T(w)-2T(v))(T(w)+2T(v)) = {c*c}*(S(w)-4S(v)) + D(w)-4D(v): OK")
    # banked-bracket sanity: 4*Bup^k < Aup^k ; (for lower links) Alo^k < 4*Blo^k
    assert 4 * cfg['Bup']**k < cfg['Aup']**k
    if 'Alo' in cfg:
        assert cfg['Alo']**k < 4 * cfg['Blo']**k
    # V0 chain: q*221 - 1 <= n  ->  v = 2n + k + 1 >= 442q + k - 1
    if cfg['V0']:
        assert cfg['V0'] == 442*q + k - 1
    print("-" * 72)

# ---------------- per-k link arithmetic (omega-level) --------------------
# k=6 : from 19(n+d+6) < 24(n+6)  derive 19w <= 24v+24, w=2(n+d)+7, v=2n+7
# k=8 : from 21(n+d+8) < 25(n+8)  derive 21w <= 25v+27
# k=10: from 20(n+d+10) < 23(n+10) derive 20w <= 23v+26
#       from 8(n+1) < 7(n+d+1)    derive 11... -> 8v - 8 <= 7w
# k=12: from 65(n+d+12) < 73(n+12) derive 65w <= 73v+87
# k=14: from 19(n+d+14) < 21(n+14) derive 19w <= 21v+24
#       from 11(n+1) < 10(n+d+1)   derive 11v <= 10w + 11
def link_check(k, A, B, cconst):
    w = 2*(nn+dd) + k + 1; v = 2*nn + k + 1
    # hypothesis: B*(n+d+k) <= A*(n+k) - 1  ->  claim: B*w <= A*v + cconst
    # equivalent to: 2*(B*(n+d+k)) <= 2*A*(n+k) - 2  ->  check symbolic slack
    hyp_slack = sp.expand(A*(nn+k) - 1 - B*(nn+dd+k))     # >= 0
    claim_slack = sp.expand(A*v + cconst - B*w)
    diff = sp.expand(claim_slack - 2*hyp_slack)           # must be >= 0 constant
    assert diff.is_constant() and diff >= 0, (k, diff)
    print(f"  k={k}: {B}w <= {A}v + {cconst}  from bracket ({A},{B}): OK (slack {diff})")

def link_check_lower(k, A, B, cconst):
    # hypothesis: A*(n+1) <= B*(n+d+1) - 1  ->  claim: A*v <= B*w + cconst
    w = 2*(nn+dd) + k + 1; v = 2*nn + k + 1
    hyp_slack = sp.expand(B*(nn+dd+1) - 1 - A*(nn+1))
    claim_slack = sp.expand(B*w + cconst - A*v)
    diff = sp.expand(claim_slack - 2*hyp_slack)
    assert diff.is_constant() and diff >= 0, (k, diff)
    print(f"  k={k}: {A}v <= {B}w + {cconst}  from lower bracket ({A},{B}): OK (slack {diff})")

print("link arithmetic:")
link_check(6, 24, 19, 24)
link_check(8, 25, 21, 27)
link_check(10, 23, 20, 26)
link_check(12, 73, 65, 87)
link_check(14, 21, 19, 24)
link_check_lower(10, 8, 7, 8)     # 8v <= 7w + 8
link_check_lower(14, 11, 10, 11)  # 11v <= 10w + 11
print("-" * 72)

# ---------------- k=6 inequalities --------------------------------------
# Delta = 189(w^2-4v^2) - 2700 < 0 from w < 2v (omega from 19w<=24v+24, v>=2).
# Lower: Delta >= -4D(v) = -(756v^2+3600) > -X  <=  2T(v) > 756v^2+3600, T(w)>0.
S6 = S_poly(6); T6 = 2*W**3 - 35*W; D6 = 189*W**2 + 900
assert sp.expand(T6**2 - 4*S6 - D6) == 0
check_shift("k6 T(W)>0        ", T6 - 1, 1331)
check_shift("k6 2T(v)-4D(v)>0 ", 2*T6 - (756*W**2 + 3600) - 1, 1331)

# ---------------- k=8 inequalities --------------------------------------
S8 = S_poly(8); P8 = W**4 - 42*W**2 + 105; D8 = 4096*W**2
assert sp.expand(P8**2 - S8 - D8) == 0
check_shift("k8 P(W)>0        ", P8 - 1, 2217)
check_shift("k8 2P(v)-4D(v)>0 ", 2*P8 - 4*4096*W**2 - 1, 2217)

# ---------------- k=12 inequalities -------------------------------------
S12 = S_poly(12); P12 = W**6 - 143*W**4 + 4147*W**2 - 24453
D12 = sp.expand(P12**2 - S12)
assert D12 == sp.expand(2223936*W**4 - 73996416*W**2 + 489893184)
check_shift("k12 P(W)>0       ", P12 - 1, 3547)
check_shift("k12 D(W)>=0      ", D12, 3547)
check_shift("k12 2P(v)-4D(v)>0", 2*P12 - 4*D12 - 1, 3547)
# upper: 17850625*Delta <= Phi12(v) < 0, using (65w)^4 <= (73v+87)^4, w^2>=v^2:
Phi12 = sp.expand(2223936*(73*vv+87)**4
                  - 17850625*(8895744*vv**4 - 221989248*vv**2 + 1469679552))
# check assembly: 17850625*(D(w)-4D(v)) <= Phi12  given the two hints
lhs = sp.expand(17850625*(D12.subs(W, ww) - 4*D12.subs(W, vv)))
slack = sp.expand(Phi12 - lhs
                  - 2223936*((73*vv+87)**4 - (65*ww)**4)          # hint1 >= 0
                  - 17850625*73996416*(ww**2 - vv**2))            # hint2 >= 0
assert slack == 0, slack
check_shift("k12 -Phi12(v)>0  ", -Phi12, 3547, var=vv)

# ---------------- k=10 inequalities -------------------------------------
S10 = S_poly(10); T10 = 8*W**5 - 660*W**3 + 7887*W
D10 = sp.expand(T10**2 - 64*S10)
assert D10 == sp.expand(649000*W**4 - 5457375*W**2 + 57153600)
check_shift("k10 T(W)>0       ", T10 - 1, 2661)
# D10 > 0 for ALL W: complete-square certificate
c_sq = 4*649000*57153600 - 5457375**2
print(f"  k10 D>0 cert: 2596000*D = (1298000W^2-5457375)^2 + {c_sq}; positive: {c_sq > 0}")
assert c_sq > 0
assert sp.expand(2596000*D10 - (1298000*W**2 - 5457375)**2 - c_sq) == 0
# upper: 160000*Delta <= Phi10(v) < 0 using (20w)^4<=(23v+26)^4 and w^2>=v^2
Phi10 = sp.expand(649000*(23*vv+26)**4
                  + 160000*(-2596000*vv**4 + 16372125*vv**2 - 171460800))
lhs = sp.expand(160000*(D10.subs(W, ww) - 4*D10.subs(W, vv)))
slack = sp.expand(Phi10 - lhs
                  - 649000*((23*vv+26)**4 - (20*ww)**4)
                  - 160000*5457375*(ww**2 - vv**2))
assert slack == 0, slack
check_shift("k10 -Phi10(v)>0  ", -Phi10, 2661, var=vv)
# lower: 25X + Delta > 0 where Delta = D(w) - 4D(v); keep D(w) (needed at the
# v = 2661 boundary!).  Hints: (8v-8)^5<=(7w)^5, (20w)^3<=(23v+26)^3,
# (8v-8)^4<=(7w)^4, (20w)^2<=(23v+26)^2, w>=0.  Scale 134456000 = 7^5*8000.
U10 = sp.expand(1600000*(8*vv-8)**5 - 277315500*(23*vv+26)**3
                + 36344000000*(8*vv-8)**4 - 5457375*336140*(23*vv+26)**2
                + 134456000*(57153600 + 50*T10.subs(W, vv) - 4*D10.subs(W, vv)))
# assembly check: 134456000*(25*(T(w)+2T(v)) + D(w) - 4D(v)) >= U10 given hints
lhs = sp.expand(134456000*(25*(T10.subs(W, ww) + 2*T10.subs(W, vv))
                           + D10.subs(W, ww) - 4*D10.subs(W, vv)))
slack = sp.expand(lhs - U10
                  - 1600000*((7*ww)**5 - (8*vv-8)**5)             # hint >= 0
                  - 277315500*((23*vv+26)**3 - (20*ww)**3)        # hint >= 0
                  - 36344000000*((7*ww)**4 - (8*vv-8)**4)         # hint >= 0
                  - 5457375*336140*((23*vv+26)**2 - (20*ww)**2)   # hint >= 0
                  - 134456000*25*7887*ww)                         # w >= 0
assert slack == 0, slack
check_shift("k10 U10(v)>0     ", U10, 2661, var=vv)
# congruences
print("  k10 T == 0 mod 5 identically:",
      all(T10.subs(W, a) % 5 == 0 for a in range(5)))
assert sp.expand(T10 - (8*(W**5 - W) + 5*(-132*W**3 + 1579*W))) == 0  # Lean decomposition
# T odd at odd W: m = 2*c + w decomposition
cdec = 4*ww**5 - 330*ww**3 + 3943*ww - (8*vv**5 - 660*vv**3 + 7887*vv)
assert sp.expand(2*cdec + ww - (T10.subs(W, ww) - 2*T10.subs(W, vv))) == 0
print("  k10 parity decomposition m = 2c + w: OK")
# mod 11 kill of m in {-5, -15}:
for m in (-5, -15):
    bad = []
    for a in range(11):
        for b in range(11):
            if (S10.subs(W, a) - 4*S10.subs(W, b)) % 11 == 0 and \
               (T10.subs(W, a) - 2*T10.subs(W, b) - m) % 11 == 0:
                bad.append((a, b))
    print(f"  k10 mod 11, m={m}: solutions {bad} (must be empty)")
    assert not bad

# ---------------- k=14 (partial: large d) --------------------------------
S14 = S_poly(14); P14 = sqrt_poly_part(14); T14 = sp.expand(16*P14)
D14 = sp.expand(T14**2 - 256*S14)
print(f"k=14: T = {T14}")
print(f"      D = {D14}")
# 7 | T identically  (Lean decomposition via W^7-W)
assert all(T14.subs(W, a) % 7 == 0 for a in range(7))
assert sp.expand(T14 - (16*(W**7 - W) + 7*(-520*W**5 + 28938*W**3 - 379477*W))) == 0
print("  k14 T == 0 mod 7, decomposition 16(W^7-W) + 7(...): OK")
# thresholds: need Delta < 0 and Delta > -7X   for v >= V0
# upper Phi14 via (19w)^6 <= (21v+24)^6, w^4 >= v^4, (19w)^2 <= (21v+24)^2, scale 19^6:
Phi14 = sp.expand(1318847348*(21*vv+24)**6
                  - 47045881*92807039780*vv**4
                  + 130321*1455430979401*(21*vv+24)**2
                  + 47045881*4674935865600
                  - 47045881*4*D14.subs(W, vv))
lhs = sp.expand(47045881*(D14.subs(W, ww) - 4*D14.subs(W, vv)))
slack = sp.expand(Phi14 - lhs
                  - 1318847348*((21*vv+24)**6 - (19*ww)**6)
                  - 47045881*92807039780*(ww**4 - vv**4)
                  - 130321*1455430979401*((21*vv+24)**2 - (19*ww)**2))
assert slack == 0, slack
th_up = min_pos_threshold(-Phi14, var=vv)
# lower: 7X + Delta > 0: D(w) >= 0 (need threshold), Delta >= -4D(v);
# 7T(w) >= [16(11v-11)^7/10^7 - 3640(21v+24)^5/19^5 + 202566 v^3 - 2656355(21v+24)/19]*7
scale = 10**7 * 19**5
U14 = sp.expand(7*(16*19**5*(11*vv-11)**7
                   - 3640*10**7*(21*vv+24)**5
                   + 202566*scale*vv**3
                   - 2656355*10**7*19**4*(21*vv+24))
                + scale*(14*T14.subs(W, vv) - 4*D14.subs(W, vv)))
lhs = sp.expand(scale*(7*(T14.subs(W, ww) + 2*T14.subs(W, vv)) - 4*D14.subs(W, vv)))
slack = sp.expand(lhs - U14
                  - 7*16*19**5*((10*ww)**7 - (11*vv-11)**7)
                  - 7*3640*10**7*((21*vv+24)**5 - (19*ww)**5)
                  - 7*202566*scale*(ww**3 - vv**3)
                  - 7*2656355*10**7*19**4*((21*vv+24) - 19*ww))
assert slack == 0, slack
th_lo = min_pos_threshold(U14, var=vv)
th_D = min_pos_threshold(D14)
print(f"  k14 thresholds: -Phi14>0 for v>={th_up}; U14>0 for v>={th_lo}; D14>=0 for W>={th_D}")
V0_14 = max(th_up, th_lo, th_D)
# v = 2n+15, n >= 9d - 1  ->  v >= 18d + 13 >= V0_14  <=>  d >= ceil((V0_14-13)/18)
import math
d0 = math.ceil((V0_14 - 13) / 18)
print(f"  k14 V0 = {V0_14}  ->  partial theorem for d >= {d0}")
D0_14 = 663000            # chosen clean threshold in the Lean file
V0L = 18*D0_14 + 13
assert V0L >= V0_14
check_shift("k14 T(W)>0       ", T14 - 1, V0L)
check_shift("k14 D(W)>=0      ", D14, V0L)
check_shift("k14 -Phi14(v)>0  ", -Phi14, V0L, var=vv)
check_shift("k14 U14(v)>0     ", U14, V0L, var=vv)
print(f"  k14 Lean thresholds: d >= {D0_14}, v >= {V0L}: OK")

# ---------------- numeric sanity of the whole argument -------------------
import random
random.seed(1)
print("numeric sanity (windows really exclude solutions):")
for k, cfg in DATA.items():
    c = cfg['c']; S = S_poly(k)
    T = {6: T6, 8: P8, 10: T10, 12: P12, 14: T14}[k]
    D = {6: D6, 8: D8, 10: D10, 12: D12, 14: D14}[k]
    V0 = cfg['V0'] or V0L
    Aup, Bup = cfg['Aup'], cfg['Bup']
    B = cfg['B']
    for _ in range(200):
        v = random.randrange(V0, 3*V0) | 1
        # w in the two-sided bracket window: Blo*... <= w <= (Aup*v+const)/Bup;
        # the lower link only exists (and is only used) for k = 10, 14.
        wmax = (Aup*v + 90) // Bup
        if 'Alo' in cfg:
            Alo, Blo = cfg['Alo'], cfg['Blo']
            wmin = max(v + 2, -(-(Alo*v - Alo) // Blo))
        else:
            wmin = v + 2
        w = random.randrange(wmin, wmax + 1) | 1
        Delta = int(D.subs(W, w) - 4*D.subs(W, v))
        X = int(T.subs(W, w) + 2*T.subs(W, v))
        assert Delta < 0 and X > 0 and -B*X < Delta, (k, v, w)
print("  OK: Delta in (-B*X, 0) throughout the bracket windows")
print("ALL CHECKS PASSED")
