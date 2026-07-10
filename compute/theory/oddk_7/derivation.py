#!/usr/bin/env python3
"""
Erdos 686, k=7, N=4: centered identity, exact Thue inequality, and the
convergent-pinning constant C_7.  Template: compute/theory/k5_third_row_note.md
Section 5/6 and k5_convergent_reduction.py.

Setting: n >= 0, d >= 1, (n+d+1)...(n+d+7) = 4 (n+1)...(n+7).
Centered coordinates X := n+d+4, Y := n+4 (so Y >= 4, X > Y) turn this into

    P7(X) = 4 * P7(Y),      P7(T) = T(T^2-1)(T^2-4)(T^2-9)
                                  = T^7 - 14 T^5 + 49 T^3 - 36 T.       (*)

Leading cancellation:  X^7 - 4Y^7 = G(X,Y) exactly on solutions, where
    G(X,Y) = 14 X^5 - 49 X^3 + 36 X - 56 Y^5 + 196 Y^3 - 144 Y.

This script PROVES (exact symbolic sign checks, no floats in decision logic):

  L1  the centered identity and the explicit expansion of P7;
  L2  the leading-cancellation identity;
  L3  strict monotonicity of P7 on [3,oo) and of X -> G(X,Y) on [2,oo);
  L4  rational bracket sanity  r_lo < 4^(1/7) < r_hi
        (r_lo = 60949/50000 = 1.21898,  r_hi = 12191/10000 = 1.2191),
      certified by integer 7th-power comparisons;
  L5  ratio bracket, lower:  any solution with Y >= Y0 = 250 has X/Y > r_lo
        [single-variable polynomial positivity, exact real-root isolation];
  L6  ratio bracket, upper:  ... X/Y < r_hi;
  L7  G(r_hi Y, Y) < 0 for Y >= 250  (so X^7 - 4Y^7 = G < 0 in the bracket);
  L8  G(r_lo Y, Y) >= -C1 Y^5 for Y >= 1, C1 := 56 - 14 r_lo^5 (exact rational);
      hence |X^7 - 4Y^7| <= C1 * Y^5 for every solution with Y >= 250;
  L9  |4^(1/7) - X/Y| <= C_7 / Y^2 with C_7 := C1/(7 r_lo^6) = 2(4-r_lo^5)/r_lo^6
      exact rational, C_7 < 399/500 = 0.798 < 1  (Fatou threshold 1/Y^2);
  L10 handoff: the banked confinement (Erdos686QuotientConfinement.lean,
      row_base_lower_k7, bracket 11/9 > 4^(1/7)) gives 4d <= n+1 for d >= 221,
      i.e. Y = n+4 >= 887 >= Y0 = 250; d <= 220 is closed by the banked
      small-core certificate.  Also (n+1)/d = 4 exactly (floor), so d > (Y-3)/5.
  L11 numeric grid validation (mpmath, diagnostics only).

Run:  python3 derivation.py       (all checks assert; prints PASS lines)
"""

from fractions import Fraction

import sympy as sp

x, T, X, Y, s, z = sp.symbols('x T X Y s z')

PASS = []


def report(tag, msg):
    PASS.append(tag)
    print(f"[PASS] {tag}: {msg}")


# ---------------------------------------------------------------- L1: identity
P7_factored = T * (T**2 - 1) * (T**2 - 4) * (T**2 - 9)
P7 = sp.expand(P7_factored)
assert P7 == T**7 - 14*T**5 + 49*T**3 - 36*T
prod7 = sp.prod([x + i for i in range(1, 8)])
assert sp.expand(prod7 - P7_factored.subs(T, x + 4)) == 0
report("L1", "prod_{i=1..7}(x+i) = P7(x+4),  P7(T) = T^7 - 14T^5 + 49T^3 - 36T "
             "= T(T^2-1)(T^2-4)(T^2-9)")

# ------------------------------------------------- L2: leading cancellation
G = 14*X**5 - 49*X**3 + 36*X - 56*Y**5 + 196*Y**3 - 144*Y
assert sp.expand((P7.subs(T, X) - 4*P7.subs(T, Y)) - (X**7 - 4*Y**7 - G)) == 0
report("L2", "P7(X) - 4 P7(Y) = X^7 - 4Y^7 - G(X,Y);  on solutions "
             "X^7 - 4Y^7 = G = 14X^5 - 49X^3 + 36X - 56Y^5 + 196Y^3 - 144Y")

# ---------------------------------------------------------- L3: monotonicity
dP = sp.diff(P7, T)                       # 7T^6 - 70T^4 + 147T^2 - 36
coeffs = sp.Poly(sp.expand(dP.subs(T, 3 + s)), s).all_coeffs()
assert all(c > 0 for c in coeffs), coeffs
dG = sp.diff(G, X)                        # 70X^4 - 147X^2 + 36
coeffsG = sp.Poly(sp.expand(dG.subs(X, 2 + s)), s).all_coeffs()
assert all(c > 0 for c in coeffsG), coeffsG
report("L3", f"P7'(3+s) coeffs {coeffs} all > 0  (P7 strictly increasing on [3,oo)); "
             f"dG/dX(2+s) coeffs {coeffsG} all > 0")

# ------------------------------------------------------- L4: bracket sanity
a_lo, b_lo = 60949, 50000        # r_lo = 1.21898
a_hi, b_hi = 12191, 10000        # r_hi = 1.2191
assert a_lo**7 < 4 * b_lo**7, "r_lo must be below 4^(1/7)"
assert 4 * b_hi**7 < a_hi**7, "r_hi must be above 4^(1/7)"
report("L4", f"{a_lo}^7 < 4*{b_lo}^7 and 4*{b_hi}^7 < {a_hi}^7  "
             f"(r_lo = {a_lo}/{b_lo} < 4^(1/7) < r_hi = {a_hi}/{b_hi})")

Y0 = 250


def scaledP(a, b):
    """b^7 * P7(a*Y/b)  as an integer-coefficient polynomial in Y."""
    return sp.expand(a*Y * (a**2*Y**2 - b**2) * (a**2*Y**2 - 4*b**2)
                     * (a**2*Y**2 - 9*b**2))


def positive_on_ray(expr, y0, name):
    """PROVE expr(Y) > 0 for all real Y >= y0: exact real-root isolation
    (sympy CRootOf comparisons are exact), positive leading coefficient,
    and a positive exact evaluation at y0."""
    p = sp.Poly(sp.expand(expr), Y)
    assert p.LC() > 0, f"{name}: leading coefficient not positive"
    roots = sp.real_roots(p.as_expr(), Y)
    assert all(r < y0 for r in roots), f"{name}: real root >= {y0}"
    v0 = p.eval(y0)
    assert v0 > 0, f"{name}: value at {y0} not positive"
    largest = max(roots) if roots else None
    if largest is not None:
        # exact isolating rational bounds for the report
        lo = sp.floor(largest * 1000) / 1000
        return f"largest real root in ({sp.nsimplify(lo)}, {sp.nsimplify(lo)+sp.Rational(1,1000)}]"
    return "no real roots"


# ------------------------------------------- L5/L6: ratio bracket from (*)
# If a solution had 50000*X <= 60949*Y (X <= r_lo Y), monotonicity (both args
# >= 3) gives P7(X) <= P7(r_lo Y), so 4 P7(Y) <= P7(r_lo Y); N_lo > 0 refutes.
N_lo = 4 * b_lo**7 * P7.subs(T, Y) - scaledP(a_lo, b_lo)
info = positive_on_ray(N_lo, Y0, "N_lo")
report("L5", f"N_lo(Y) = 4*{b_lo}^7*P7(Y) - {b_lo}^7*P7({a_lo}Y/{b_lo}) > 0 for "
             f"Y >= {Y0}  [{info}]  => X/Y > {a_lo}/{b_lo}")

N_hi = scaledP(a_hi, b_hi) - 4 * b_hi**7 * P7.subs(T, Y)
info = positive_on_ray(N_hi, Y0, "N_hi")
report("L6", f"N_hi(Y) = {b_hi}^7*P7({a_hi}Y/{b_hi}) - 4*{b_hi}^7*P7(Y) > 0 for "
             f"Y >= {Y0}  [{info}]  => X/Y < {a_hi}/{b_hi}")

# X > Y for any solution with Y >= 250: P7(Y) > 0 and 4P7(Y) > P7(Y).
PY_shift = sp.Poly(sp.expand(P7.subs(T, 4 + s)), s).all_coeffs()
assert all(c >= 0 for c in PY_shift) and PY_shift[-1] > 0, PY_shift
# (P7(4+s) has nonnegative coefficients, constant P7(4) = 5040 > 0
#  => P7(Y) > 0 for Y >= 4)

# ------------------------------------------------------------ L7: G < 0
G_hi = sp.expand(G.subs(X, sp.Rational(a_hi, b_hi) * Y) * b_hi**5)
info = positive_on_ray(-G_hi, Y0, "-G_hi")
report("L7", f"-{b_hi}^5 * G(r_hi*Y, Y) > 0 for Y >= {Y0}  [{info}]; with L3 "
             f"(G increasing in X) => X^7 - 4Y^7 = G(X,Y) < 0 on solutions")

# ------------------------------------------------------------ L8: |G| bound
r_lo = Fraction(a_lo, b_lo)
C1 = 56 - 14 * r_lo**5                     # exact rational
# b_lo^5 * [G(r_lo Y, Y) + C1 Y^5]  ==  c3*Y^3 - c1*Y  with c3, c1 > 0, c3 >= c1
E = sp.expand(G.subs(X, sp.Rational(a_lo, b_lo)*Y) * b_lo**5
              + sp.Rational(C1.numerator, C1.denominator) * b_lo**5 * Y**5)
Epoly = sp.Poly(E, Y)
assert Epoly.degree() == 3, Epoly
c3 = Epoly.coeff_monomial(Y**3)
c1 = -Epoly.coeff_monomial(Y)
assert c3 > 0 and c1 > 0 and c3 >= c1, (c3, c1)
# c3*Y^3 - c1*Y = Y*(c3*Y^2 - c1) >= Y*(c3 - c1) >= 0 for Y >= 1.
report("L8", f"b_lo^5*(G(r_lo Y, Y) + C1 Y^5) = {c3}*Y^3 - {c1}*Y >= 0 for Y >= 1 "
             f"(c3 >= c1 > 0);  C1 = 56 - 14 r_lo^5 = {C1} "
             f"~= {float(C1):.6f};  => |X^7 - 4Y^7| <= C1*Y^5 for Y >= {Y0}")

# ------------------------------------------------------- L9: the constant C_7
# X^7 - 4Y^7 = (X - qY) * Phi,  Phi = sum_{i=0}^{6} X^i (qY)^(6-i).
# In the bracket X > r_lo*Y and qY > r_lo*Y (L4), so Phi > 7 (r_lo Y)^6, hence
#   |q - X/Y| = |X^7 - 4Y^7| / (Y * Phi) < C1 Y^5 / (7 r_lo^6 Y^7) = C_7/Y^2.
C7 = C1 / (7 * r_lo**6)
assert C7 == 2 * (4 - r_lo**5) / r_lo**6
assert C7 < Fraction(399, 500) < 1
report("L9", f"C_7 = 2(4 - r_lo^5)/r_lo^6 = {C7.numerator}/{C7.denominator} "
             f"~= {float(C7):.9f} < 399/500 = 0.798 < 1;  "
             f"|4^(1/7) - X/Y| <= C_7/Y^2 for every solution with Y >= {Y0}")

# asymptotic constant kappa = 2(4 - q^5)/q^6, q = 4^(1/7):  kappa < C_7 exactly.
# kappa < C_7  <=>  2q^2 - C_7 q - 2 < 0  (using q^5 = 4/q^2, q^6 = 4/q).
# The quadratic is increasing in q for q > C_7/4, so a tight upper bracket
# q < qb suffices:  qb = 121901366/10^8  (certified by 7th powers).
qb_num, qb_den = 121901366, 10**8
assert 4 * qb_den**7 < qb_num**7            # qb > 4^(1/7)
assert (121901365)**7 < 4 * qb_den**7       # and the lower neighbour is below
qb = Fraction(qb_num, qb_den)
assert 2*qb*qb - C7*qb - 2 < 0
kappa = sp.N(2*(4 - sp.root(4, 7)**5) / sp.root(4, 7)**6, 50)
report("L9b", f"kappa = 2(4-q^5)/q^6 = {kappa}  (asymptotic Y^2*|q - X/Y|); "
              f"kappa < C_7 certified via exact bracket q < {qb_num}/{qb_den}")

# ------------------------------------------------------------- L10: handoff
# Banked (Erdos686QuotientConfinement.row_base_lower_k7, d >= 221):
#   bracket 11/9 > 4^(1/7):
assert 4 * 9**7 < 11**7
#   => 4d <= n+1, so n >= 4*221 - 1 = 883 and Y = n+4 >= 887 >= Y0.
assert 4 * 221 - 1 == 883 and 883 + 4 >= Y0
# Upper confinement (bracket 6/5 < 4^(1/7)) pins the floor: n+1 < 5d.
assert 6**7 < 4 * 5**7
report("L10", "banked handoff: 4*9^7 < 11^7 (row_base_lower_k7) => for d >= 221, "
              "4d <= n+1, Y = n+4 >= 887 >= Y0 = 250; and 6^7 < 4*5^7 => n+1 < 5d, "
              "so d > (Y-3)/5;  d <= 220 closed by banked small-core certificate")

# --------------------------------------------- L11: numeric grid validation
import mpmath as mp

mp.mp.dps = 80
qmp = mp.mpf(4) ** (mp.mpf(1) / 7)


def real_ratio(Yv):
    """real solution ratio t = X/Y of P7(X) = 4 P7(Y), normalized by Y^7."""
    u = 1 / Yv**2
    rhs = 4 * (1 - 14*u + 49*u**2 - 36*u**3)
    f = lambda t: t**7 - 14*t**5*u + 49*t**3*u**2 - 36*t*u**3 - rhs
    return mp.findroot(f, qmp)


grid = list(range(Y0, 2001, 7)) + [10**4, 10**5, 10**6, 10**9, 10**12, 10**18, 10**24]
worst = mp.mpf(0)
for Yv in grid:
    Ym = mp.mpf(Yv)
    ratio = real_ratio(Ym)
    assert float(ratio) > a_lo / b_lo and float(ratio) < a_hi / b_hi, Yv
    lhs = abs(ratio**7 - 4) * Ym**7        # = |X^7 - 4Y^7|
    assert lhs <= float(C1) * Ym**5 * (1 + mp.mpf(10)**-40), Yv
    dev = abs(qmp - ratio) * Ym**2
    worst = max(worst, dev)
    assert dev < float(C7), (Yv, dev)
report("L11", f"grid check on {len(grid)} Y-values in [{Y0}, 1e24]: bracket, "
              f"|X^7-4Y^7| <= C1*Y^5 and Y^2|q - X/Y| <= C_7 all hold at the real "
              f"solution; max Y^2-deviation {mp.nstr(worst, 12)} (-> kappa)")

# -------------------------- Lean-friendly shift points (all-nonneg coefficients)
print()
print("Lean-certificate shift points (polynomial rewritten at Y = Y* + z has")
print("all coefficients >= 0, so positivity is coefficient-wise -- no nlinarith")
print("search needed):")
for name, expr in (("N_lo", N_lo), ("N_hi", N_hi), ("-G_hi", -G_hi)):
    p = sp.Poly(sp.expand(expr), Y)
    shift = None
    for cand in range(1, 2001):
        cs = sp.Poly(sp.expand(p.as_expr().subs(Y, cand + z)), z).all_coeffs()
        if all(c >= 0 for c in cs) and cs[-1] > 0:
            shift = cand
            break
    assert shift is not None and shift <= Y0, (name, shift)
    print(f"    {name}: minimal all-nonneg shift Y* = {shift}  (<= Y0 = {Y0})")

print()
print(f"ALL {len(PASS)} LEMMAS PASS")
print()
print("Summary: any k=7, N=4 solution with d >= 221 has Y = n+4 >= 887 and")
print(f"    |4^(1/7) - X/Y| <= C_7/Y^2,  C_7 = {C7.numerator}/{C7.denominator} < 399/500 < 1,")
print("which is inside the Fatou threshold 1/Y^2: X/Y is confined to the")
print("convergent/semiconvergent family of cf(4^(1/7)) -- see cf_scan.py.")
