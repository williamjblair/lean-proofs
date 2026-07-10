#!/usr/bin/env python3
"""
Erdos 686, k=11, N=4: exact centered identity, Thue inequality, and the
convergent-pinning constant C_11.

Template: compute/theory/k5_third_row_note.md, Sections 5-6 (k=5 case).

Setting: n >= 1, d >= 1, (n+d+1)...(n+d+11) = 4*(n+1)...(n+11).
Centered variables X := n+d+6, Y := n+6  (so X = Y + d, Y >= 7, X >= 8).

ALL decision logic below is exact (sympy Rationals / Python ints / Sturm).
mpmath is used ONLY in step V for a redundant numeric grid validation of the
already-proved inequality chain; it never decides anything.

Pipeline:
  I.   centering identity   prod_{i=1..11}(x+i) = P11(x+6),
       P11(T) = T(T^2-1)(T^2-4)(T^2-9)(T^2-16)(T^2-25)
              = T^11 - 55 T^9 + 1023 T^7 - 7645 T^5 + 21076 T^3 - 14400 T
  II.  strict monotonicity of P11 on [5, oo)          (exact, RootOf/Sturm)
  III. ratio bracket FROM THE EQUATION:  for every solution with Y >= Y0=100,
           (1134/1000) Y < X < (1135/1000) Y
       via signs of P11(r*Y) - 4*P11(Y) on [Y0, oo)   (exact, Sturm)
  IV.  the exact Thue inequality:  for Y >= Y0,
           40 Y^9 < 4 Y^11 - X^11 <= B Y^9        (B exact rational ~ 49.6)
       hence, with q := 4^(1/11),
           6/5 * 1/Y^2  <  q - X/Y  <  13/10 * 1/Y^2       ("two-sided pin")
       in particular X = floor(q Y) and C_11 = 13/10.
  V.   numeric grid validation on the real solution branch X*(Y).
  VI.  Worley/Dujella confinement parameters for C = 13/10:  r*s < 2C = 13/5.
"""

import sympy as sp
from fractions import Fraction as F

PASS = "[PASS]"
checks = 0


def ok(label, cond):
    global checks
    assert cond, f"FAILED: {label}"
    checks += 1
    print(f"{PASS} {label}")


# ------------------------------------------------------------------ constants
K = 11
M = (K - 1) // 2          # 5
CENTER = (K + 1) // 2     # 6
Y0 = 100                  # validity threshold for the bracket + Thue bound

T, x, Xs, Ys, qs, Ss = sp.symbols('T x X Y q S', positive=True)

# =========================================================== I. centered identity
P11 = T * sp.prod([T**2 - j**2 for j in range(1, M + 1)])
P11e = sp.expand(P11)

lhs = sp.expand(sp.prod([x + i for i in range(1, K + 1)]))
rhs = sp.expand(P11e.subs(T, x + CENTER))
ok("centering identity: prod_{i=1..11}(x+i) = P11(x+6)", sp.expand(lhs - rhs) == 0)

coeffs = sp.Poly(P11e, T).all_coeffs()
ok("P11(T) = T^11 - 55T^9 + 1023T^7 - 7645T^5 + 21076T^3 - 14400T",
   coeffs == [1, 0, -55, 0, 1023, 0, -7645, 0, 21076, 0, -14400, 0])

# L(T) := P11(T) - T^11   (the lower-degree tail)
L = P11e - T**11
Lc = {9: -55, 7: 1023, 5: -7645, 3: 21076, 1: -14400}
ok("L(T) tail coefficients", sp.expand(L - sum(c * T**j for j, c in Lc.items())) == 0)

# rearrangement identity: on the solution set P11(X) = 4 P11(Y),
#   X^11 - 4Y^11 = 4 L(Y) - L(X)
ident = sp.expand((Xs**11 - 4 * Ys**11) - (4 * L.subs(T, Ys) - L.subs(T, Xs))
                  - (P11e.subs(T, Xs) - 4 * P11e.subs(T, Ys)))
ok("polynomial identity  X^11-4Y^11 - (4L(Y)-L(X)) = P11(X) - 4 P11(Y)", ident == 0)

# ==================================================== II. monotonicity on [5, oo)
dP = sp.diff(P11e, T)
ok("P11'(5) > 0", dP.subs(T, 5) > 0)
nroots_ge5 = sp.Poly(dP, T).count_roots(5, None)
ok("P11' has no root in [5, oo)  (Sturm)  =>  P11 strictly increasing there",
   nroots_ge5 == 0)

# =============================================== III. ratio bracket from equation
r_lo = sp.Rational(1134, 1000)   # = 567/500
r_hi = sp.Rational(1135, 1000)   # = 227/200

# q = 4^(1/11) lies strictly between the brackets: integer 11th-power checks
ok("1134^11 < 4*1000^11        (r_lo < q)", 1134**11 < 4 * 1000**11)
ok("4*1000^11 < 1135^11        (q < r_hi)", 4 * 1000**11 < 1135**11)
# r_hi^9 < 4 (needed later so that 4Y^j - X^j > 0 for all odd j <= 9)
ok("1135^9 < 4*1000^9          (r_hi^9 < 4)", 1135**9 < 4 * 1000**9)

# U(Y) := P11(r_hi Y) - 4 P11(Y) > 0 for all Y >= Y0  (so X < r_hi*Y);
# V(Y) := 4 P11(Y) - P11(r_lo Y) > 0 for all Y >= Y0  (so X > r_lo*Y).
U = sp.expand((P11e.subs(T, r_hi * Ys) - 4 * P11e.subs(T, Ys)) * 200**11)
V = sp.expand((4 * P11e.subs(T, Ys) - P11e.subs(T, r_lo * Ys)) * 500**11)
PU, PV = sp.Poly(U, Ys), sp.Poly(V, Ys)
ok("U(Y0) > 0 and Sturm: no root of U in [Y0, oo)",
   PU.eval(Y0) > 0 and PU.count_roots(Y0, None) == 0)
ok("V(Y0) > 0 and Sturm: no root of V in [Y0, oo)",
   PV.eval(Y0) > 0 and PV.count_roots(Y0, None) == 0)
rootsU = [sp.N(r) for r in sp.Poly(U, Ys).real_roots()]
rootsV = [sp.N(r) for r in sp.Poly(V, Ys).real_roots()]
print(f"       largest real root of U: {max(rootsU):.4f}   of V: {max(rootsV):.4f}"
      f"   (both < Y0 = {Y0})")
# Consequence (uses II + P11(X) = 4 P11(Y), X,Y >= 7 integers):
#   X <= r_lo Y  would give P11(X) <= P11(r_lo Y) < 4 P11(Y)  -- contradiction;
#   X >= r_hi Y  would give P11(X) >= P11(r_hi Y) > 4 P11(Y)  -- contradiction.
print("       => every solution with Y >= 100 has 1134*Y < 1000*X < 1135*Y")

# ================================================= IV. the exact Thue inequality
# Termwise: for odd j <= 9 and r_lo Y < X < r_hi Y (monotone j-th powers):
#     (4 - r_hi^j) Y^j  <  4Y^j - X^j  <  (4 - r_lo^j) Y^j ,   all three positive.
for j in (1, 3, 5, 7, 9):
    ok(f"4 - r_hi^{j} > 0 (exact)", sp.Rational(4) - r_hi**j > 0)

# X^11 - 4Y^11 = 4L(Y) - L(X)
#             = -55(4Y^9-X^9) + 1023(4Y^7-X^7) - 7645(4Y^5-X^5)
#               + 21076(4Y^3-X^3) - 14400(4Y-X)
sanity = sp.expand(4 * L.subs(T, Ys) - L.subs(T, Xs)
                   - (-55 * (4 * Ys**9 - Xs**9) + 1023 * (4 * Ys**7 - Xs**7)
                      - 7645 * (4 * Ys**5 - Xs**5) + 21076 * (4 * Ys**3 - Xs**3)
                      - 14400 * (4 * Ys - Xs)))
ok("grouped form of 4L(Y) - L(X)", sanity == 0)

b = {j: abs(c) * (sp.Rational(4) - r_lo**j) for j, c in Lc.items()}   # upper amplitudes
a = {j: abs(c) * (sp.Rational(4) - r_hi**j) for j, c in Lc.items()}   # lower amplitudes

# ---- upper bound:  |X^11 - 4Y^11| <= sum_j b_j Y^j <= B Y^9   for Y >= Y0
B = b[9] + b[7] / Y0**2 + b[5] / Y0**4 + b[3] / Y0**6 + b[1] / Y0**8
# fold certificate: H(S) = (B - b9) S^4 - b7 S^3 - b5 S^2 - b3 S - b1,  S = Y^2:
H = sp.expand((B - b[9]) * Ss**4 - b[7] * Ss**3 - b[5] * Ss**2 - b[3] * Ss - b[1])
ok("fold: H(Y0^2) = 0 exactly", sp.Poly(H, Ss).eval(Y0**2) == 0)
hc = sp.Poly(H, Ss).all_coeffs()
ok("fold: Descartes signs (+,-,-,-,-) => unique positive root => H >= 0 on [Y0^2, oo)",
   hc[0] > 0 and all(c < 0 for c in hc[1:]))
ok("fold double-check: Sturm, no root of H in (Y0^2, oo)",
   sp.Poly(H, Ss).count_roots(Y0**2 + 1, None) == 0 and
   sp.Poly(H, Ss).eval(Y0**2 + 1) > 0)

# ---- Lean-readiness certificates (all four inequalities are positivity-grade):
ts = sp.symbols('t', positive=True)
Ush = sp.Poly(sp.expand(U.subs(Ys, ts + Y0)), ts).all_coeffs()
Vsh = sp.Poly(sp.expand(V.subs(Ys, ts + Y0)), ts).all_coeffs()
ok("Lean cert: U(t+100) has all coefficients >= 0 (positivity-grade)",
   all(c >= 0 for c in Ush) and Ush[-1] > 0)
ok("Lean cert: V(t+100) has all coefficients >= 0 (positivity-grade)",
   all(c >= 0 for c in Vsh) and Vsh[-1] > 0)
quoH, remH = sp.div(H, Ss - Y0**2, Ss)
ok("Lean cert: H(S) = (S - 10^4) * (cubic with positive coefficients)",
   sp.expand(remH) == 0 and all(c > 0 for c in sp.Poly(quoH, Ss).all_coeffs()))

# ---- lower bound (sign + size):  4Y^11 - X^11 >= ell * Y^9  for Y >= Y0, where
#   4Y^11 - X^11 = 55(4Y^9-X^9) - 1023(4Y^7-X^7) + 7645(4Y^5-X^5)
#                  - 21076(4Y^3-X^3) + 14400(4Y-X)
#               >= a9 Y^9 - b7 Y^7 - b3 Y^3        (drop the two positive terms)
ell = a[9] - b[7] / sp.Integer(Y0)**2 - b[3] / sp.Integer(Y0)**6
ok("ell > 40  (so 4Y^11 - X^11 > 40 Y^9 > 0: X/Y approaches q from BELOW)",
   ell > 40)
Gq = sp.expand((a[9] - ell) * Ss**3 - b[7] * Ss**2 - b[3])
quoG, remG = sp.div(Gq, Ss - Y0**2, Ss)
ok("Lean cert: lower-bound fold G(S) = (S - 10^4) * (quadratic, positive coeffs)",
   sp.expand(remG) == 0 and all(c > 0 for c in sp.Poly(quoG, Ss).all_coeffs()))

# ---- denominator Phi = sum_{i=0..10} X^i (qY)^{10-i}:
phi = sum(Xs**i * (qs * Ys)**(10 - i) for i in range(11))
ok("factorization  X^11 - (qY)^11 = (X - qY) * Phi  (symbolic)",
   sp.expand(Xs**11 - (qs * Ys)**11 - (Xs - qs * Ys) * phi) == 0)
# bounds: r_lo Y < X, qY  and  X, qY < r_hi Y  give
#   11 r_lo^10 Y^10 < Phi < 11 r_hi^10 Y^10.
Phi_lo = 11 * r_lo**10
Phi_hi = 11 * r_hi**10

# ---- the constant:
#   q - X/Y = (4Y^11 - X^11) / (Y * Phi)   [note 4 = q^11, sign from lower bound]
C11_exact = B / Phi_lo               # upper:  q - X/Y <= C11_exact / Y^2
c_lo_exact = ell / Phi_hi            # lower:  q - X/Y >= c_lo_exact / Y^2
print(f"       B          = {B} = {float(B):.6f}")
print(f"       ell        = {ell} = {float(ell):.6f}")
print(f"       C11_exact  = {C11_exact} = {float(C11_exact):.6f}")
print(f"       c_lo_exact = {c_lo_exact} = {float(c_lo_exact):.6f}")
ok("C11_exact <= 13/10", C11_exact <= sp.Rational(13, 10))
ok("c_lo_exact >= 6/5", c_lo_exact >= sp.Rational(6, 5))

kappa = sp.N(55 * (4 - 4**sp.Rational(9, 11)) / (11 * 4**sp.Rational(10, 11)), 50)
print(f"       asymptotic  Y*(qY - X) -> 55*(4-4^(9/11))/(11*4^(10/11)) = {kappa}")
print()
print("  ==> THE PIN (PROVED for every solution with Y >= 100):")
print("        6/5 / Y^2  <  4^(1/11) - X/Y  <  13/10 / Y^2")
print("      integer form:  (10XY+12)^11 < 4*(10Y^2)^11 < (10XY+13)^11")
print("      in particular 0 < qY - X < 1, i.e. X = floor(q*Y).")

# integer-form equivalence sanity (symbolic, q^11 = 4):
#   q - X/Y > 12/(10 Y^2)  <=>  10 q Y^2 > 10XY + 12  <=>  4 (10Y^2)^11 > (10XY+12)^11
#   q - X/Y < 13/(10 Y^2)  <=>  10 q Y^2 < 10XY + 13  <=>  4 (10Y^2)^11 < (10XY+13)^11
# (monotonicity of t^11; RHS positive since X,Y >= 1). Nothing further to check.

# =============================================== V. numeric grid validation
import mpmath as mp
mp.mp.dps = 60
qmp = mp.mpf(4) ** (mp.mpf(1) / 11)


def P11_mp(t):
    return t * (t * t - 1) * (t * t - 4) * (t * t - 9) * (t * t - 16) * (t * t - 25)


print()
print("grid validation on the real solution branch X*(Y), Y in [100, 10^9]:")
bad = 0
worst_hi, worst_lo = 0.0, 10.0
grid = [int(round(100 * 10 ** (i / 14))) for i in range(0, 99)]
for Yv in grid:
    tgt = 4 * P11_mp(mp.mpf(Yv))
    lo, hi = mp.mpf(Yv) * 1134 / 1000, mp.mpf(Yv) * 1135 / 1000
    assert P11_mp(lo) < tgt < P11_mp(hi)          # bracket check (numeric echo)
    for _ in range(220):                          # plain bisection: robust
        mid = (lo + hi) / 2
        if P11_mp(mid) < tgt:
            lo = mid
        else:
            hi = mid
    Xstar = (lo + hi) / 2
    pin = float((qmp - Xstar / Yv) * Yv**2)
    worst_hi, worst_lo = max(worst_hi, pin), min(worst_lo, pin)
    if not (1.2 < pin < 1.3):
        bad += 1
ok(f"grid: 6/5 < Y^2*(q - X*/Y) < 13/10 at all {len(grid)} grid points "
   f"(range [{worst_lo:.6f}, {worst_hi:.6f}])", bad == 0)
print(f"       endpoint pin values approach kappa = {float(kappa):.6f}")

# =============================================== VI. Worley/Dujella confinement
# C = 13/10 >= 1/2 (Legendre) and >= 1 (Fatou): need the quasi-convergent
# theorem (Worley 1981; Dujella 2004):
#   |alpha - a/b| < C/b^2, gcd(a,b)=1  ==>
#   (a,b) = (r p_{m+1} +- s p_m, r q_{m+1} +- s q_m),  r,s >= 0 integers,
#   r*s < 2C.
# Here 2C = 13/5 = 2.6, so r*s <= 2:
pairs = [(r, s) for r in range(0, 4) for s in range(0, 4)
         if r * s < F(13, 5) and F(13, 5) <= (r + 1) * (s + 1)]  # display aid
print()
print("Worley confinement for C = 13/10 (2C = 13/5):  r*s in {0, 1, 2}")
print("  gcd-reduced options: (r,s) in {(1,0), (0,1), (1,1), (1,2), (2,1)}, signs +-")
print("  g := gcd(X,Y) >= 2 branch: |q - x/y| < 13/(10 g^2 y^2) <= 13/40 < 1/2")
print("    => Legendre applies directly; and g^2 < (13/10)*(a_{m+1} + 2).")
ok("13/40 < 1/2 (Legendre applies to every g >= 2)", F(13, 40) < F(1, 2))

# small-Y translation (inputs from the banked Lean machinery, cited not re-proved):
#   d <= 220 is closed by the banked small-core certificate; for d >= 221 the
#   row-1 quotient confinement for k=11 gives q = 7 and n >= 7*221 - 1 = 1546,
#   hence Y = n + 6 >= 1552 > Y0 = 100.  So Y >= Y0 is automatic in the open branch.
ok("confinement floor: 7*221 - 1 + 6 = 1552 >= Y0", 7 * 221 - 1 + 6 >= Y0)

print()
print(f"ALL {checks} EXACT CHECKS PASSED")
print("summary: for every k=11, N=4 solution with d >= 221:")
print("  Y = n+6 >= 1552, X = Y+d = floor(4^(1/11) * Y), and")
print("  6/5 < Y^2 * (4^(1/11) - X/Y) < 13/10   -- C_11 = 13/10, two-sided.")
