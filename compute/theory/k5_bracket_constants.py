#!/usr/bin/env python3
"""Exact rational bracketing of the constants c, sigma, alpha for Lean use.

All verifications are exact integer computations:
  - c    = 1/(4^{1/5}-1):        3 c^5 - 5c^4 - 10c^3 - 10c^2 - 5c - 1 = 0
  - sigma = (c-3)/(72-23c):      1861153 x^5 - 16581140 x^4 - 2810720 x^3
                                   - 177280 x^2 - 4960 x - 52 = 0
  - alpha = 24 sigma + 1 = 1/(72*4^{1/5}-95):
                                 1861153 x^5 - 407253125 x^4 - 8573750 x^3
                                   - 90250 x^2 - 475 x - 1 = 0
Each is the unique real root in the stated bracket (Sturm-verified).
"""
import sympy as sp
from fractions import Fraction

x = sp.symbols('x')

CASES = [
    ("c",     3*x**5 - 5*x**4 - 10*x**3 - 10*x**2 - 5*x - 1,      (3, 4),   10**12),
    ("sigma", 1861153*x**5 - 16581140*x**4 - 2810720*x**3
              - 177280*x**2 - 4960*x - 52,                        (9, 10),  10**10),
    ("alpha", 1861153*x**5 - 407253125*x**4 - 8573750*x**3
              - 90250*x**2 - 475*x - 1,                           (218, 219), 10**10),
]

for name, poly, (lo, hi), den in CASES:
    P = sp.Poly(poly, x)
    # unique real root in [lo, hi]:
    nroots_interval = P.count_roots(lo, hi)
    nroots_real = P.count_roots(-sp.oo, sp.oo)
    root = sp.nsolve(poly, x, (lo + hi) / 2, prec=60)
    # integer bracket at denominator den: exact sign evaluation
    k = int(sp.floor(root * den))
    def sign_at(p_, q_):
        v = P.eval(sp.Rational(p_, q_))
        return sp.sign(v)
    slo, shi = sign_at(k, den), sign_at(k + 1, den)
    ok = slo * shi < 0
    print(f"{name}: value = {sp.N(root, 45)}")
    print(f"   real roots total = {nroots_real}, in [{lo},{hi}] = {nroots_interval}")
    print(f"   exact bracket: {k}/{den} < {name} < {k+1}/{den}   "
          f"(sign check {slo},{shi}: {'OK' if ok else 'FAIL'})")
    assert ok and nroots_interval == 1

# derived Lean-ready constants
sig_lo, sig_hi = 90766125506, 90766125507       # /1e10
alp_lo, alp_hi = 2188387012157, 2188387012158   # /1e10
print("\nDerived integer constants for Lean statements:")
print("  0 <= sigma*t - s <= 4 + 92*sigma  gives, with brackets:")
print(f"    (A)  10^10 * s <= {sig_hi} * t")
print(f"    (B)  {sig_lo} * t <= 10^10 * s + {4*10**10 + 92*sig_hi}")
print("  0 <= alpha*t - M <= 4 + 92*alpha  gives, with brackets:")
print(f"    (A') 10^10 * M <= {alp_hi} * t")
print(f"    (B') {alp_lo} * t <= 10^10 * M + {4*10**10 + 92*alp_hi}")
sig_root = sp.nsolve(CASES[1][1], x, 9, prec=40)
alp_root = sp.nsolve(CASES[2][1], x, sp.Rational(2188387012157, 10**10), prec=40)
print("  window sizes: 4 + 92*sigma =", sp.N(4 + 92*sig_root, 30))
print("                4 + 92*alpha =", sp.N(4 + 92*alp_root, 30))
