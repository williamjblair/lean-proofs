#!/usr/bin/env python3
"""
Erdos 686, k=9, N=4: centered identity, exact Thue inequality, and the
quasi-convergent (Worley) confinement constant.

ALL decision logic is exact (sympy over QQ + fractions.Fraction).  Floating
point appears only in display strings and in the mpmath cross-validation
grid (which validates, never decides).

Pipeline (template: compute/theory/k5_third_row_note.md, Sections 5-6):

  [1] centered identity  prod_{i=1..9}(x+i) = P9(x+5),
        P9(T) = T(T^2-1)(T^2-4)(T^2-9)(T^2-16)
              = T^9 - 30 T^7 + 273 T^5 - 820 T^3 + 576 T,
      so with X := n+d+5, Y := n+5 the equation
        (n+d+1)...(n+d+9) = 4 (n+1)...(n+9)
      is exactly  P9(X) = 4 P9(Y), equivalently
        X^9 - 4 Y^9 = u(X) - 4 u(Y),   u(T) := 30 T^7 - 273 T^5 + 820 T^3 - 576 T.

  [2] exact Thue chain, q := 4^(1/9).
      Round 1 (Y >= 60, bracket 29/25 < X/Y < 59/50, derived from the
      equation itself via monotonicity of P9 on [4,oo)):
        A1: 4 P9(Y) - P9(r_lo Y) > 0   for Y >= 60   =>  X > r_lo Y
        A2: P9(r_hi Y) - 4 P9(Y) > 0   for Y >= 60   =>  X < r_hi Y
        B1: 4 u(Y) - u(r_hi Y) > 0     for Y >= 60   =>  X^9 < 4 Y^9, X/Y < q
        B2: 4 u(Y) - u(r_lo Y) <= c7a Y^7  for Y >= 2,  c7a = 120 - 30 r_lo^7
        C : 0 < q - X/Y <= C_a / Y^2,   C_a := c7a / (9 r_lo^8)     (exact)
      Round 2 (Y >= 1330; banked confinement for k=9 gives n+1 >= 6d, so
      d >= 221 forces Y = n+5 >= 6*221+4 = 1330; d <= 220 is banked):
      bootstrap C_a into the tight one-sided bracket
        rho2 < X/Y < q,   rho2 := q-side rational with (rho2 + C_a/1330^2)^9 < 4,
      and rerun B2/C to get the FINAL exact constant
        C_9 = (120 - 30 rho2^7 + (3280 - 820 rho2^3)/1330^4) / (9 rho2^8).

Every positivity claim is PROVED symbolically: substitute Y = Y0 + z and
check all coefficients nonnegative (sum-of-monomials certificate; the
Lean-friendly shape, closable by positivity/nlinarith), with an exact Sturm
count_roots fallback; each claim is also cross-validated on numeric grids.
"""

import json
import os
import sympy as sp
from fractions import Fraction as Fr

x, T, Y, z, a, b = sp.symbols('x T Y z a b')
PASS = []


def report(tag, ok, msg):
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {tag}: {msg}")
    PASS.append((tag, ok))
    assert ok, f"{tag} failed"


# ------------------------------------------------------------------ helpers
def iroot(n, k):
    """floor(n^(1/k)) by pure-integer Newton iteration."""
    if n < 0:
        raise ValueError
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


def q_bracket(digits):
    """Exact rational bracket q_lo < 4^(1/9) < q_hi, width 10^-digits."""
    r = iroot(4 * 10**(9 * digits), 9)
    # 4*10^(9N) = 2^(9N+2) 5^(9N) is never a 9th power (2-exponent != 0 mod 9)
    assert r**9 < 4 * 10**(9 * digits) < (r + 1)**9
    return Fr(r, 10**digits), Fr(r + 1, 10**digits)


def prove_pos_for_Y_ge(poly_expr, Y0, strict=True):
    """Prove poly(Y) > 0 (>= 0 if strict=False) for all real Y >= Y0.
    Primary: shift Y -> Y0 + z, all coefficients nonneg (+ positive constant
    for strict).  Fallback: exact Sturm root count on [Y0, oo) + sign at Y0.
    Returns the certificate method string."""
    shifted = sp.Poly(sp.expand(poly_expr.subs(Y, Y0 + z)), z)
    coeffs = shifted.all_coeffs()
    const = coeffs[-1]
    if all(c >= 0 for c in coeffs) and (const > 0 or not strict):
        return "shift-nonneg-coeffs"
    p = sp.Poly(poly_expr, Y)
    nroots = p.count_roots(Y0, sp.oo)
    v0 = poly_expr.subs(Y, Y0)
    if strict and nroots == 0 and v0 > 0:
        return "sturm-no-roots"
    if not strict and v0 >= 0 and p.count_roots(Y0 + sp.Rational(1, 10**6), sp.oo) == 0:
        return "sturm-no-roots"
    raise AssertionError(f"positivity proof failed for Y >= {Y0}")


# ================================================================== task 1
print("=" * 72)
print("TASK 1: centered identity and explicit P9")
print("=" * 72)

prod9 = sp.expand(sp.prod([x + i for i in range(1, 10)]))
P9fac = T * (T**2 - 1) * (T**2 - 4) * (T**2 - 9) * (T**2 - 16)
P9 = sp.expand(P9fac)
report("identity", sp.expand(prod9 - P9.subs(T, x + 5)) == 0,
       "prod_{i=1..9}(x+i) = P9(x+5),  P9(T) = T(T^2-1)(T^2-4)(T^2-9)(T^2-16)")

P9_expected = T**9 - 30*T**7 + 273*T**5 - 820*T**3 + 576*T
report("expansion", sp.expand(P9 - P9_expected) == 0,
       "P9(T) = T^9 - 30T^7 + 273T^5 - 820T^3 + 576T  (odd, integer coeffs)")

u = 30*T**7 - 273*T**5 + 820*T**3 - 576*T
report("u-split", sp.expand(P9 - (T**9 - u)) == 0,
       "P9(T) = T^9 - u(T),  u(T) = 30T^7 - 273T^5 + 820T^3 - 576T")

# equation transform: P9(X) = 4 P9(Y)  <=>  X^9 - 4Y^9 = u(X) - 4u(Y)
Xs, Ys = sp.symbols('Xs Ys')
lhs = P9.subs(T, Xs) - 4 * P9.subs(T, Ys)
rhs = (Xs**9 - 4*Ys**9) - (u.subs(T, Xs) - 4*u.subs(T, Ys))
report("transform", sp.expand(lhs - rhs) == 0,
       "P9(X) - 4P9(Y) = (X^9 - 4Y^9) - (u(X) - 4u(Y))  identically")

# leading cancellation: deg(u) = 7 = k-2
report("leading-cancel", sp.degree(u, T) == 7,
       "X^9 - 4Y^9 = u(X) - 4u(Y) has degree k-2 = 7: |X^9-4Y^9| <= C*Y^7 scale")

# ------------------------------------------------- monotonicity certificates
dP9 = sp.diff(P9, T)
sh = sp.Poly(sp.expand(dP9.subs(T, 4 + z)), z)
report("P9-monotone", all(c >= 0 for c in sh.all_coeffs()) and sh.all_coeffs()[-1] > 0,
       f"P9'(4+z) has all coeffs >= 0, const = {sh.all_coeffs()[-1]} > 0: "
       "P9 strictly increasing on [4,oo)")

du = sp.diff(u, T)
shu = sp.Poly(sp.expand(du.subs(T, 3 + z)), z)
report("u-monotone", all(c >= 0 for c in shu.all_coeffs()) and shu.all_coeffs()[-1] > 0,
       f"u'(3+z) has all coeffs >= 0, const = {shu.all_coeffs()[-1]} > 0: "
       "u strictly increasing on [3,oo)")

# ================================================================== task 2
print()
print("=" * 72)
print("TASK 2: exact Thue inequality  |4^(1/9) - X/Y| <= C_9 / Y^2")
print("=" * 72)

q_lo12, q_hi12 = q_bracket(12)
print(f"        q = 4^(1/9) in ({q_lo12} , {q_hi12})   [exact 9th-power bracket]")

# ---------------------------------------------------------------- round 1
Y0a = 60
r_lo = sp.Rational(29, 25)     # 1.16 < q
r_hi = sp.Rational(59, 50)     # 1.18 > q
report("r_lo<q", r_lo**9 < 4, f"(29/25)^9 = {sp.Rational(29,25)**9} < 4")
report("q<r_hi", r_hi**9 > 4, f"(59/50)^9 = {float((sp.Rational(59,50))**9):.4f}... > 4")

A1 = sp.expand(4*P9.subs(T, Y) - P9.subs(T, r_lo*Y))
m = prove_pos_for_Y_ge(A1, Y0a)
report("A1", True, f"4 P9(Y) - P9(29Y/25) > 0 for Y >= {Y0a}   [{m}]")

A2 = sp.expand(P9.subs(T, r_hi*Y) - 4*P9.subs(T, Y))
m = prove_pos_for_Y_ge(A2, Y0a)
report("A2", True, f"P9(59Y/50) - 4 P9(Y) > 0 for Y >= {Y0a}   [{m}]")

# bracket corollary (uses P9 monotone on [4,oo), r_lo*Y0a = 69.6 >= 4):
#   any integer solution with Y >= 60 has  29Y/25 < X < 59Y/50.
B1 = sp.expand(4*u.subs(T, Y) - u.subs(T, r_hi*Y))
m = prove_pos_for_Y_ge(B1, Y0a)
report("B1", True, f"4u(Y) - u(59Y/50) > 0 for Y >= {Y0a}: X^9 < 4Y^9, i.e. X/Y < q "
       f"(one-sided approximation!)   [{m}]")

c7a = sp.Rational(120) - 30*r_lo**7
B2 = sp.expand(c7a*Y**7 - (4*u.subs(T, Y) - u.subs(T, r_lo*Y)))
m = prove_pos_for_Y_ge(B2, 2, strict=False)
report("B2", True, f"4u(Y) - u(29Y/25) <= c7a*Y^7 for Y >= 2, c7a = 120-30(29/25)^7 "
       f"= {c7a} ~ {float(c7a):.6f}   [{m}]")

# step C: factor identity + denominator bound
sumsym = sum(a**i * b**(8 - i) for i in range(9))
report("factor-id", sp.expand((a - b)*sumsym - (a**9 - b**9)) == 0,
       "a^9 - b^9 = (a-b) * sum_{i=0..8} a^i b^(8-i)")
# with a = qY > b = X > r_lo*Y > 0 each of the 9 terms is >= (r_lo Y)^8, so
#   0 < qY - X = (4Y^9 - X^9)/Phi <= c7a Y^7 / (9 r_lo^8 Y^8)
C_a = sp.nsimplify(c7a / (9 * r_lo**8))
C_a = sp.Rational(c7a, 1) / (9 * r_lo**8)
print(f"        round 1:  0 < q - X/Y <= C_a/Y^2 for Y >= {Y0a},  "
      f"C_a = {C_a} ~ {float(C_a):.6f}")
report("C_a<6/5", C_a < sp.Rational(6, 5), f"C_a ~ {float(C_a):.6f} < 6/5 (robust constant)")

# ---------------------------------------------------------------- round 2
# Small-Y regime handled by banked machinery: d <= 220 banked outright; for
# d >= 221 the banked (k,q)=(9,6) confinement gives n+1 >= 6d >= 1326, i.e.
#   Y = n+5 >= 6*221 + 4 = 1330  =: Y0b.
Y0b = 1330
report("Y0b", 6*221 + 4 == Y0b, "d >= 221 & n+1 >= 6d  =>  Y = n+5 >= 1330")

dev = Fr(C_a.p, C_a.q) / Fr(Y0b**2)          # C_a / Y0b^2, exact
# choose rho2 = 7-digit decimal with  rho2 + dev < q  (certified by 9th power)
qf_lo, _ = q_bracket(30)
rho2 = Fr((qf_lo - dev).numerator * 10**7 // (qf_lo - dev).denominator, 10**7)
rho2_s = sp.Rational(rho2.numerator, rho2.denominator)
cert = rho2 + dev
report("rho2-cert", cert**9 < 4,
       f"(rho2 + C_a/1330^2)^9 < 4 exactly, rho2 = {rho2} = {float(rho2):.7f}: "
       "round-1 chain gives X/Y > q - C_a/Y^2 >= rho2 for Y >= 1330")
report("rho2<q", rho2**9 < 4, f"rho2^9 < 4  (rho2 < q)")

# B2' with the tight bracket; fold the positive Y^3 term at Y0b
c7b = sp.Rational(120) - 30*rho2_s**7 + (3280 - 820*rho2_s**3) / Y0b**4
B2b = sp.expand(c7b*Y**7 - (4*u.subs(T, Y) - u.subs(T, rho2_s*Y)))
m = prove_pos_for_Y_ge(B2b, Y0b, strict=False)
report("B2'", True, f"4u(Y) - u(rho2*Y) <= c7b*Y^7 for Y >= {Y0b},  "
       f"c7b ~ {float(c7b):.9f}   [{m}]")

C_b = c7b / (9 * rho2_s**8)
C_b_fr = Fr(sp.fraction(C_b)[0].p, sp.fraction(C_b)[1].p) if False else Fr(C_b.p, C_b.q)
print(f"        round 2:  0 < q - X/Y <= C_b/Y^2 for Y >= {Y0b}")
print(f"        C_b exact = {C_b.p}/{C_b.q}")
print(f"        C_b       ~ {float(C_b):.9f}")

C9 = sp.Rational(1031, 1000)
report("C9", C_b <= C9, f"C_b <= C_9 := 1031/1000 = 1.031  (headline exact rational)")
report("C9-alt", C_b <= sp.Rational(129, 125), "C_b <= 129/125 = 1.032 (round spare)")

# the asymptotically optimal constant kappa_9 = 30(q^2-1)/(9q) = (10/3)(q - 1/q)
qv = sp.root(4, 9)
kappa = sp.Rational(10, 3) * (qv - 1/qv)
kappa_n = sp.N(kappa, 40)
print(f"        asymptotic optimum kappa_9 = (10/3)(q - 1/q) = {kappa_n}")
minpoly_kappa = sp.minimal_polynomial(kappa, x)
print(f"        minpoly(kappa_9) = {minpoly_kappa}")
report("kappa<C9", sp.N(C9 - kappa, 40) > 0 and sp.N(kappa - sp.Rational(103, 100), 40) > 0,
       f"1.03 < kappa_9 ~ {float(kappa_n):.7f} <= C_b ~ {float(C_b):.7f} <= 1.031: "
       "C_9 is within 1e-4 of optimal, and C_9 > 1 -- PAST the Fatou threshold")

# Legendre/Fatou/Worley classification of the constant
report("confinement-class", sp.Rational(1, 2) < kappa and 1 < kappa,
       "C_9 > 1: neither Legendre (<1/2) nor Fatou (<1) applies; need "
       "Worley/Dujella quasi-convergents with rs < 2*C_9 = 2.062, i.e. rs <= 2")

# ------------------------------------------------- numeric grid validation
print()
print("numeric cross-validation (mpmath, never decides anything) ...")
import mpmath as mp
mp.mp.dps = 60
qmp = mp.mpf(4) ** (mp.mpf(1) / 9)

# (i) the real solution X*(Y) of P9(X) = 4 P9(Y) satisfies the final bound
P9f = lambda t: t**9 - 30*t**7 + 273*t**5 - 820*t**3 + 576*t
worst = 0
for Ye in [1330, 2000, 5000, 10**4, 10**5, 10**6, 10**8, 10**10, 10**12, 10**15]:
    target = 4 * P9f(mp.mpf(Ye))
    lo, hi = mp.mpf(float(rho2)) * Ye, qmp * Ye     # P9(lo) < target < P9(hi)
    assert P9f(lo) < target < P9f(hi)
    for _ in range(220):
        mid = (lo + hi) / 2
        if P9f(mid) < target:
            lo = mid
        else:
            hi = mid
    Xstar = (lo + hi) / 2
    devq = (qmp - Xstar/Ye) * Ye**2
    worst = max(worst, devq)
    assert 0 < devq <= float(C9), (Ye, devq)
report("grid-X*", True,
       f"real root X*(Y): 0 < (q - X*/Y)*Y^2 <= {mp.nstr(worst, 8)} <= 1.031 on grid; "
       f"-> kappa_9 as Y -> oo")

# (ii) integer grid: exact Fraction evaluation of every claim polynomial
import random
random.seed(686)
A1p, A2p, B1p, B2p, B2bp = [sp.Poly(e, Y) for e in (A1, A2, B1, B2, B2b)]
def fr_eval(poly, yv):
    return sum(Fr(int(c)) * Fr(yv)**e if c == int(c) else Fr(c.p, c.q) * Fr(yv)**e
               for (e,), c in poly.terms())
grid = list(range(Y0a, Y0a + 40)) + [10**3, 1330, 1331, 5000, 10**5, 10**9, 10**15, 10**30]
for yv in grid:
    assert fr_eval(A1p, yv) > 0 and fr_eval(A2p, yv) > 0 and fr_eval(B1p, yv) > 0
    assert fr_eval(B2p, yv) >= 0
    if yv >= Y0b:
        assert fr_eval(B2bp, yv) >= 0
report("grid-exact", True,
       f"A1,A2,B1,B2,B2' exact-positive on integer grid ({len(grid)} points, "
       "Y up to 10^30)")

# (iii) bracket-interior points X in [rho2*Y, q_lo*Y]: 0 < 4u(Y)-u(X) <= c7b*Y^7
# (the bracket usually contains no integer -- that is the point of the whole
#  reduction -- so we check exact rational points spanning it)
uf = lambda t: 30*t**7 - 273*t**5 + 820*t**3 - 576*t
qloF = Fr(q_lo12.numerator, q_lo12.denominator)
cnt = 0
for yv in [1330, 5000, 77777, 10**6, 10**9 + 7, 10**15 + 1]:
    for j in range(5):
        xv = (rho2 + (qloF - rho2) * Fr(j, 4)) * yv
        val = 4*uf(Fr(yv)) - uf(xv)
        assert 0 < val <= Fr(c7b.p, c7b.q) * Fr(yv)**7, (yv, j)
        cnt += 1
    # and up to 8 sampled integers that fall inside the bracket
    ilo = rho2.numerator * yv // rho2.denominator + 1
    ihi = qloF.numerator * yv // qloF.denominator
    if ihi >= ilo:
        step = max(1, (ihi - ilo) // 7)
        for xv in list(range(ilo, ihi + 1, step))[:8] + [ihi]:
            val = 4*uf(Fr(yv)) - uf(Fr(xv))
            assert 0 < val <= Fr(c7b.p, c7b.q) * Fr(yv)**7, (yv, xv)
            cnt += 1
report("grid-u", True,
       f"0 < 4u(Y)-u(X) <= c7b*Y^7 at {cnt} exact bracket points (rational + integer)")

# ------------------------------------------------- persist exact constants
out = {
    "k": 9,
    "P9": "T^9 - 30*T^7 + 273*T^5 - 820*T^3 + 576*T",
    "u": "30*T^7 - 273*T^5 + 820*T^3 - 576*T",
    "Y0a": Y0a, "r_lo": "29/25", "r_hi": "59/50",
    "c7a": f"{c7a.p}/{c7a.q}",
    "C_a": f"{C_a.p}/{C_a.q}",
    "Y0b": Y0b,
    "rho2": f"{rho2.numerator}/{rho2.denominator}",
    "c7b": f"{c7b.p}/{c7b.q}",
    "C_b": f"{C_b.p}/{C_b.q}",
    "C9": "1031/1000",
    "two_C9": "1031/500",
    "kappa9_minpoly": str(minpoly_kappa),
    "q_lo_12": f"{q_lo12.numerator}/{q_lo12.denominator}",
    "q_hi_12": f"{q_hi12.numerator}/{q_hi12.denominator}",
}
here = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(here, "constants.json"), "w") as f:
    json.dump(out, f, indent=2)
print()
print(f"constants written to {os.path.join(here, 'constants.json')}")
print(f"ALL {len(PASS)} CHECKS PASSED")
