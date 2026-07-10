#!/usr/bin/env python3
"""
Erdos 686, k=15, N=4: centered identity + EXACT Thue inequality (derivation).

Setting: n >= 1, d >= 1, (n+d+1)...(n+d+15) = 4*(n+1)...(n+15).
Centered variables X := n+d+8, Y := n+8 (so Y >= 9, X = Y+d > Y); the
equation becomes exactly

    P(X) = 4*P(Y),        P(T) := T * prod_{j=1..7} (T^2 - j^2)
                               =  prod_{j=-7..7} (T + j)          (15 factors)

This script PROVES, with every decision made in exact rational/integer
arithmetic (Fraction / sympy Rational; floats appear only in printed
commentary):

  (1) the centered identity  prod_{i=1..15}(x+i) = P(x+8), and the explicit
      expansion of P;
  (2) rational brackets rho_lo < 4^(1/15) < rho_hi (sign of rho^15 - 4);
  (3) the crude all-Y bracket q(Y-7) < X < q(Y+7)+7, whence d >= 221 forces
      Y >= Y0 (Y0 computed exactly; = 2131);
  (4) monotonicity certificates: P' > 0 and R' > 0 on [8, oo),
      R(T) := T^15 - P(T);
  (5) the tight ratio bracket rho_lo*Y < X < rho_hi*Y for Y >= Y0
      [certificates: 4P(Y) - P(rho_lo*Y) > 0 and P(rho_hi*Y) - 4P(Y) > 0 on
      [Y0, oo), each proved by shifting Y = Y0 + v and checking that ALL
      coefficients are nonnegative rationals -- an nlinarith/positivity-ready
      certificate];
  (6) the two-sided exact Thue inequality, valid for every solution with
      Y >= Y0:
          -C_A * Y^13  <=  X^15 - 4*Y^15  <=  -C_B * Y^13
      with EXPLICIT exact rational C_A, C_B (~ 94.52, ~ 94.50), again by
      shifted-coefficient certificates;
  (7) the approximation constant: |4^(1/15) - X/Y| <= C15 / Y^2 with the
      exact rational C15 = 1729/1000, via C_A/(15*rho_lo^14) <= C15 (exact)
      and the geometric-sum factorization of X^15 - (qY)^15;
  (8) grid validation: certificates (5)(6) evaluated exactly at many Y, and
      the full implication (6) => (7) checked exactly (via a 10^-40 rational
      sandwich of 4^(1/15)) on genuine convergent-quality pairs (X, Y).

Interface to the banked Lean machinery (ErdosProblems/Erdos686.lean):
  d <= 220 is closed by the banked small-core certificates; for d >= 221 the
  crude bracket of (3) gives Y >= Y0 = 2131 unconditionally, so the Thue
  regime covers everything not already banked.  (The banked constant-quotient
  confinement for the (k,q) = (15,10) pair gives n >= 10*221 - 1, i.e.
  Y >= 2217, for d >= 221; our self-contained Y0 = 2131 <= 2217 is weaker as
  a hypothesis and therefore covers that route too.)

Companion: cf_scan.py (continued fraction of 4^(1/15), Worley/quasi-convergent
candidate enumeration to Y <= 10^100, exact equation checks).
"""

import json
import os
from fractions import Fraction as F
from math import gcd

import sympy as sp

# ----------------------------------------------------------------- helpers
NCHK = 0


def PASS(msg):
    global NCHK
    NCHK += 1
    print(f"[PASS {NCHK:02d}] {msg}")


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
    """Continued fraction of num/den (num, den > 0), exact Euclid."""
    terms = []
    while den:
        a = num // den
        terms.append(a)
        num, den = den, num - a * den
    return terms


def common_prefix(u, w):
    out = []
    for a, b in zip(u, w):
        if a != b:
            break
        out.append(a)
    return out


K = 15
HALF = 8          # (K+1)/2
J = 7             # (K-1)/2

# =================================================================== (1)
# centered identity and explicit expansion of P
x, T, Yv, v, aa, bb = sp.symbols('x T Y v a b', positive=True)

lhs = sp.prod([(x + i) for i in range(1, K + 1)])
Pexpr = T * sp.prod([T ** 2 - j ** 2 for j in range(1, J + 1)])
assert sp.expand(lhs - Pexpr.subs(T, x + HALF)) == 0
PASS("centered identity: prod_{i=1..15}(x+i) = P(x+8), "
     "P(T) = T*prod_{j=1..7}(T^2-j^2)")

Ppoly = sp.Poly(sp.expand(Pexpr), T)
# P(T) = sum_i (-1)^i e_i T^(15-2i); extract e_i exactly
e = []
for i in range(0, J + 1):
    c = Ppoly.coeff_monomial(T ** (K - 2 * i))
    e.append(int((-1) ** i * c))
assert e[0] == 1
# every other coefficient (even powers) must vanish
assert all(Ppoly.coeff_monomial(T ** m) == 0 for m in range(0, K, 2))
E1, E2, E3, E4, E5, E6, E7 = e[1:]
print("        P(T) = T^15 - %d T^13 + %d T^11 - %d T^9 + %d T^7 - %d T^5"
      " + %d T^3 - %d T" % (E1, E2, E3, E4, E5, E6, E7))
assert (E1, E2, E3) == (140, 7462, 191620)
assert Ppoly.eval(8) == sp.factorial(15)          # P(8) = 15!
PASS("expansion coefficients e_1..e_7 = %s;  P(8) = 15!  (sanity)" % (e[1:],))


def PF(t):
    """P evaluated exactly at a Fraction/int (factored form)."""
    r = t
    for j in range(1, J + 1):
        r *= t * t - j * j
    return r


def RF(t):
    """R(T) = T^15 - P(T) at a Fraction/int."""
    return t ** 15 - PF(t)


# =================================================================== (2)
# rational brackets for q := 4^(1/15) at denominator 10^8, with +-100 margin
DEN = 10 ** 8
r8 = iroot(4 * 10 ** (15 * 8), 15)               # r8/10^8 <= q < (r8+1)/10^8
assert r8 ** 15 <= 4 * 10 ** 120 < (r8 + 1) ** 15
MARG = 100
rho_lo = F(r8 - MARG, DEN)
rho_hi = F(r8 + 1 + MARG, DEN)
assert rho_lo ** 15 < 4 < rho_hi ** 15           # exact sign checks
assert 1 < rho_lo < rho_hi < 2
PASS(f"brackets: rho_lo = {r8 - MARG}/10^8 < 4^(1/15) < "
     f"{r8 + 1 + MARG}/10^8 = rho_hi   (15th-power sign checks)")
print(f"        q = 4^(1/15) = {sp.N(sp.root(4,15), 30)} ;  "
      f"q - rho_lo ~ {float(F(r8, DEN) - rho_lo):.2e}, "
      f"rho_hi - q ~ {float(rho_hi - F(r8 + 1, DEN)):.2e}")

# =================================================================== (3)
# crude bracket, valid for ALL solutions (Y >= 9):
#   P(X) > (X-7)^15  and  P(Y) < (Y+7)^15  ==>  (X-7)^15 < 4 (Y+7)^15
#   ==>  X - 7 < rho_hi (Y+7)          [since rho_hi^15 > 4]
#   P(X) < X^15     and  P(Y) > (Y-7)^15 ==>  X > rho_lo (Y-7)   [rho_lo^15<4]
# so  d = X - Y < (rho_hi - 1) Y + 7 rho_hi + 7  and
#     d = X - Y > (rho_lo - 1) Y - 7 rho_lo.
# For d >= 221:   Y > (221 - 7 rho_hi - 7)/(rho_hi - 1)  =: y_min.
y_min = (221 - 7 * rho_hi - 7) / (rho_hi - 1)
Y0 = y_min.numerator // y_min.denominator + 1     # smallest integer > y_min
assert Y0 == 2131
PASS(f"d >= 221  ==>  Y >= Y0 = {Y0}   (exact: Y > {float(y_min):.3f}; "
     "crude bracket, no banked input needed)")

# =================================================================== (4)
# monotonicity certificates on [8, oo)
Pd = sp.Poly(sp.diff(sp.expand(Pexpr), T), T)
cauchy_P = 1 + max(abs(F(int(c), int(Pd.LC()))) for c in Pd.all_coeffs())
assert Pd.count_roots(8, int(cauchy_P) + 2) == 0 and Pd.eval(8) > 0
PASS("P'(T) > 0 for T >= 8 (Sturm count on [8, CauchyBound] = 0, P'(8) > 0);"
     " P = product of 15 increasing positive factors on [8, oo)")

Rexpr = sp.expand(T ** 15 - Pexpr)
Rd = sp.Poly(sp.diff(Rexpr, T), T)
# Lean-friendly pairing certificate: R'(T) = sum of positive pairs for T >= 8
thr = [F(11 * E2, 13 * E1), F(7 * E4, 9 * E3), F(3 * E6, 5 * E5)]
assert all(t < 64 for t in thr)
cauchy_R = 1 + max(abs(F(int(c), int(Rd.LC()))) for c in Rd.all_coeffs())
assert Rd.count_roots(8, int(cauchy_R) + 2) == 0 and Rd.eval(8) > 0
PASS("R'(T) > 0 for T >= 8;  pairing thresholds 11e2/13e1, 7e4/9e3, 3e6/5e5 "
     f"= {[str(t) for t in thr]} all < 64 = 8^2  (nlinarith-ready)")


# =================================================================== (5)
# tight ratio bracket via shifted-coefficient certificates
def shifted_nonneg(expr, name, strict_const=True):
    """Certify expr(Y) (>=)0 for all Y >= Y0: substitute Y = Y0 + v and check
    every coefficient of the resulting polynomial in v is >= 0 (and the
    constant term > 0 if strict_const).  Returns the shifted Poly."""
    Q = sp.Poly(sp.expand(expr.subs(Yv, Y0 + v)), v)
    cs = Q.all_coeffs()
    bad = [i for i, c in enumerate(cs) if c < 0]
    assert not bad, (name, "negative shifted coefficients at", bad)
    if strict_const:
        assert cs[-1] > 0, (name, "constant term not > 0")
    return Q


rho_lo_sp = sp.Rational(rho_lo.numerator, rho_lo.denominator)
rho_hi_sp = sp.Rational(rho_hi.numerator, rho_hi.denominator)
PY = sp.expand(Pexpr.subs(T, Yv))
P_lo = sp.expand(Pexpr.subs(T, rho_lo_sp * Yv))
P_hi = sp.expand(Pexpr.subs(T, rho_hi_sp * Yv))

shifted_nonneg(4 * PY - P_lo, "Q_lo = 4P(Y) - P(rho_lo Y)")
shifted_nonneg(P_hi - 4 * PY, "Q_hi = P(rho_hi Y) - 4P(Y)")
PASS(f"ratio bracket for Y >= {Y0}:  rho_lo*Y < X < rho_hi*Y  "
     "[4P(Y)-P(rho_lo Y) > 0 and P(rho_hi Y)-4P(Y) > 0 on [Y0,oo), each by "
     "shift Y = Y0+v & all-coefficients-nonnegative; then P monotone]")
# monotone step sanity: rho_lo*Y0 must sit inside the R-monotone region
assert rho_lo * Y0 > 8

# =================================================================== (6)
# exact two-sided Thue inequality.
#   X^15 - 4Y^15 = R(X) - 4R(Y)      (using the equation P(X) = 4P(Y))
#   R increasing on [8,oo)  and  rho_lo Y < X < rho_hi Y  give
#   R(rho_lo Y) - 4R(Y)  <  X^15 - 4Y^15  <  R(rho_hi Y) - 4R(Y).
C_A = E1 * (4 - rho_lo ** 13) + F(1, 100)         # upper (magnitude) constant
C_B = E1 * (4 - rho_hi ** 13) - F(1, 200)         # lower (magnitude) constant
C_A_sp = sp.Rational(C_A.numerator, C_A.denominator)
C_B_sp = sp.Rational(C_B.numerator, C_B.denominator)
RY = sp.expand(Rexpr.subs(T, Yv))
R_lo = sp.expand(Rexpr.subs(T, rho_lo_sp * Yv))
R_hi = sp.expand(Rexpr.subs(T, rho_hi_sp * Yv))

shifted_nonneg(C_A_sp * Yv ** 13 + (R_lo - 4 * RY), "F1 = C_A Y^13 + R(rho_lo Y) - 4R(Y)",
               strict_const=False)
shifted_nonneg(C_A_sp * Yv ** 13 - (R_hi - 4 * RY), "F2 = C_A Y^13 - (R(rho_hi Y) - 4R(Y))",
               strict_const=False)
shifted_nonneg(-C_B_sp * Yv ** 13 - (R_hi - 4 * RY), "F3 = -C_B Y^13 - (R(rho_hi Y) - 4R(Y))",
               strict_const=False)
PASS("exact Thue inequality, every solution with Y >= Y0:")
print(f"          -C_A*Y^13 <= X^15 - 4Y^15 <= -C_B*Y^13")
print(f"          C_A = 140*(4 - rho_lo^13) + 1/100 = {C_A.numerator}/{C_A.denominator}")
print(f"              ~ {float(C_A):.6f}")
print(f"          C_B = 140*(4 - rho_hi^13) - 1/200 = {C_B.numerator}/{C_B.denominator}")
print(f"              ~ {float(C_B):.6f}")
assert 0 < C_B < C_A

# =================================================================== (7)
# approximation constant.  With q = 4^(1/15):
#   |X^15 - (qY)^15| = |X - qY| * sum_{i=0..14} X^i (qY)^(14-i)
# geometric-sum identity, verified symbolically:
assert sp.expand((aa - bb) * sum(aa ** i * bb ** (14 - i) for i in range(15))
                 - (aa ** 15 - bb ** 15)) == 0
PASS("factorization  a^15 - b^15 = (a-b) * sum_{i<15} a^i b^(14-i)  (symbolic)")
# each of the 15 terms is >= (rho_lo Y)^14 since X > rho_lo*Y and qY > rho_lo*Y
# (q > rho_lo by the sign check rho_lo^15 < 4), so
#   |q - X/Y| <= C_A * Y^13 / (Y * 15 * (rho_lo Y)^14) = C_A/(15 rho_lo^14 Y^2).
C15_exact = C_A / (15 * rho_lo ** 14)
C15 = F(1729, 1000)
assert C15_exact <= C15 < 2                       # exact rational comparison
assert 3 < 2 * C15 < 4                            # Worley bound: r*s <= 3
assert 4 * F(1, 2) > C15 * 1                      # C15/g^2 < 1/2 for g >= 2 (Legendre)
q15 = sp.root(4, 15)
kappa = sp.N(E1 * (4 - q15 ** 13) / (15 * q15 ** 14), 40)
PASS("|4^(1/15) - X/Y| <= C15/Y^2 for Y >= Y0, with exact rational")
print(f"          C15 = 1729/1000 = 1.729   [C_A/(15*rho_lo^14) = "
      f"{float(C15_exact):.9f} <= 1.729, exact]")
print(f"          asymptotic optimum kappa = e1(4-q^13)/(15 q^14) = {kappa}")
print(f"          2*C15 = 3.458 in (3,4]  ==>  Worley r*s <= 3;   "
      f"C15/4 = {float(C15/4):.6f} < 1/2  ==>  g>=2 branch is Legendre")

# =================================================================== (8)
# grid validation (exact arithmetic throughout)
# (8a) certificates evaluated at explicit Y
grid_Y = [Y0, Y0 + 1, Y0 + 17, 2500, 5000, 10 ** 4, 33333, 10 ** 5,
          777777, 10 ** 6, 10 ** 9, 10 ** 12, 10 ** 15]
for Yg in grid_Y:
    assert 4 * PF(Yg) - PF(rho_lo * Yg) > 0
    assert PF(rho_hi * Yg) - 4 * PF(Yg) > 0
    assert C_A * Yg ** 13 + (RF(rho_lo * Yg) - 4 * RF(Yg)) >= 0
    assert C_A * Yg ** 13 - (RF(rho_hi * Yg) - 4 * RF(Yg)) >= 0
    assert -C_B * Yg ** 13 - (RF(rho_hi * Yg) - 4 * RF(Yg)) >= 0
PASS(f"grid: all five certificates re-verified exactly at {len(grid_Y)} "
     f"values of Y in [{Y0}, 10^15]")

# (8b) end-to-end implication  (Thue band => |q - X/Y| <= C15/Y^2)
# on convergent-quality pairs: sandwich q by a 10^-40 rational interval,
# build the CF of the interval, use its convergents (and small multiples).
ADEN = 10 ** 40
ra = iroot(4 * 10 ** (15 * 40), 15)
alpha_lo, alpha_hi = F(ra, ADEN), F(ra + 1, ADEN)
assert ra ** 15 < 4 * 10 ** 600 < (ra + 1) ** 15
terms = common_prefix(cf_of_fraction(ra, ADEN), cf_of_fraction(ra + 1, ADEN))
p2, p1 = 1, terms[0]
q2, q1 = 0, 1
conv = [(p1, q1)]
for a in terms[1:]:
    p1, p2 = a * p1 + p2, p1
    q1, q2 = a * q1 + q2, q1
    conv.append((p1, q1))
nonvac = 0
tested = 0
for (pc, qc) in conv:
    for g in (1, 2, 3, 5, 11):
        Xg, Yg = g * pc, g * qc
        if Yg < Y0 or Yg > 10 ** 34:
            continue
        tested += 1
        thue_one_sided = (abs(Xg ** 15 - 4 * Yg ** 15) <= C_A * Yg ** 13)
        in_bracket = (rho_lo * Yg < Xg < rho_hi * Yg)
        if thue_one_sided and in_bracket:
            nonvac += 1
            # conclusion, checked exactly against the rational sandwich:
            dev = max(abs(alpha_hi - F(Xg, Yg)), abs(alpha_lo - F(Xg, Yg)))
            assert dev <= C15 / (Yg * Yg), (Xg, Yg)
assert nonvac >= 40
PASS(f"end-to-end: on {tested} convergent-quality pairs (g*p_m, g*q_m), "
     f"{nonvac} satisfy the one-sided Thue hypothesis + bracket, and EVERY "
     f"one satisfies |q - X/Y| <= C15/Y^2 (exact 10^-40 sandwich)")

# (8c) no false positives: nearest-integer X for non-convergent Y never
# slips through the equation, and the band is genuinely narrow
import random
random.seed(686)
narrow = 0
for _ in range(2000):
    Yg = random.randint(Y0, 10 ** 18)
    Xg = iroot(4 * Yg ** 15, 15)
    for XX in (Xg, Xg + 1):
        assert PF(XX) != 4 * PF(Yg)
        if -C_A * Yg ** 13 <= XX ** 15 - 4 * Yg ** 15 <= -C_B * Yg ** 13:
            narrow += 1
PASS(f"random probe: 2000 random Y in [Y0, 10^18], nearest-integer X: "
     f"0 equation hits; {narrow} landed in the Thue band "
     f"(expected ~ 2000*(C_A-C_B)/(15 q^14) ~ "
     f"{2000*float(C_A-C_B)/float(15*(F(r8,DEN))**14):.1f})")

# ------------------------------------------------------------------ summary
consts = {
    "k": K,
    "P_coeffs_e1_to_e7": e[1:],
    "rho_lo": [rho_lo.numerator, rho_lo.denominator],
    "rho_hi": [rho_hi.numerator, rho_hi.denominator],
    "Y0": Y0,
    "C_A": [C_A.numerator, C_A.denominator],
    "C_B": [C_B.numerator, C_B.denominator],
    "C15": [C15.numerator, C15.denominator],
    "C15_exact_float": float(C15_exact),
    "kappa_asymptotic": str(kappa),
    "worley_rs_max": 3,
}
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "constants.json")
with open(out, "w") as fh:
    json.dump(consts, fh, indent=1)
print(f"\nconstants written to {out}")
print(f"ALL {NCHK} CHECKS PASSED -- derivation.py")
