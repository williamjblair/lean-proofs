#!/usr/bin/env python3
"""
Erdos 686, k = 13, N = 4: centered identity, exact Thue inequality, and the
quasi-convergent confinement constant.  Template: compute/theory/
k5_third_row_note.md, Section 5/6 (k = 5 case, C_5 = 0.61).

Everything decided here is decided in EXACT arithmetic (Python ints,
fractions.Fraction, sympy Rational polynomials, Sturm root counts).  Floats
appear only in *display* strings, never in a branch.

Setting.  n >= 1, d >= 1, and
    (n+d+1)(n+d+2)...(n+d+13) = 4 * (n+1)(n+2)...(n+13).
Centered variables  X := n+d+7,  Y := n+7  (so Y >= 8, X >= Y+1):

    P(X) = 4 P(Y),        P(T) = T * prod_{j=1..6} (T^2 - j^2)
         = T^13 - 91 T^11 + 3003 T^9 - 44473 T^7 + 296296 T^5
           - 773136 T^3 + 518400 T.

Main exact results verified below (q := 4^(1/13), irrational):

  [BRACKET]   P(X) = 4P(Y), Y >= 600  ==>  (89/80) Y < X < (9/8) Y,
              and in fact X^13 < 4 Y^13 (X < qY: one-sided approximation).
  [THUE]      then |X^13 - 4 Y^13| <= (3501/50) * Y^11        (C1 = 70.02)
  [PIN]       then 0 < q - X/Y <= (3/2) / Y^2                 (C_13 = 3/2)
              exact asymptotic constant: 7*(q - 1/q) = 1.4957568...
              general odd k: C_k^asy = (k^2-1)/24 * (4^(1/k) - 4^(-1/k)).
  [SMALL-Y]   d <= 220 is banked in Lean; for d >= 221 the window forces
              n >= ceil(c*221) - 13 with c = 1/(q-1) in (8.88573, 8.88652),
              i.e. Y = n+7 >= 1958 >= 600.  So Y0 = 600 loses nothing.

C_13 = 3/2 >= 1/2: Legendre does NOT apply directly.  Worley's theorem
(1981; Dujella 2004 form) with C = 3/2 gives r*s < 2C = 3, hence for
X/Y = g*(a/b) in lowest terms:
  g = 1 :  (X, Y) = (r p_{m+1} +- s p_m, r q_{m+1} +- s q_m),
           (r,s) in {(1,0),(0,1),(1,1),(1,2),(2,1)}       [rs <= 2]
  g >= 2:  C/g^2 <= 3/8 < 1/2  ==> Legendre: b = q_m and
           g^2 < (3/2)(a_{m+1} + 2).
The exact CF of 4^(1/13) and the scan of this family live in cf_scan.py.
"""

from fractions import Fraction as F
import sympy as sp

PASS = 0
def check(label, ok):
    global PASS
    if not ok:
        raise AssertionError("FAILED: " + label)
    PASS += 1
    print(f"[PASS {PASS:2d}] {label}")

K = 13
HALF = (K + 1) // 2          # 7
T, x, Xs, Ys, qs, u = sp.symbols('T x X Y q u')

# ------------------------------------------------------------------ 1. identity
P = sp.expand(T * sp.prod(T**2 - j**2 for j in range(1, HALF)))
prod13 = sp.expand(sp.prod(x + i for i in range(1, K + 1)))
check("centered identity  prod_{i=1..13}(x+i) = P(x+7),  P(T)=T*prod(T^2-j^2)",
      sp.expand(prod13 - P.subs(T, x + HALF)) == 0)
check("P is odd:  P(-T) = -P(T)",
      sp.expand(P.subs(T, -T) + P) == 0)

coeffs = sp.Poly(P, T).all_coeffs()          # degree 13 .. 0
E = [91, 3003, 44473, 296296, 773136, 518400]   # elem. symm. of {1,4,...,36}
gen = sp.expand(sp.prod(x + j**2 for j in range(1, HALF)))
check("elementary symmetric functions of {1,4,9,16,25,36} are "
      "(91, 3003, 44473, 296296, 773136, 518400)",
      sp.Poly(gen, x).all_coeffs() == [1] + E)
check("P(T) = T^13 - 91T^11 + 3003T^9 - 44473T^7 + 296296T^5 - 773136T^3 + 518400T",
      coeffs == [1, 0, -91, 0, 3003, 0, -44473, 0, 296296, 0, -773136, 0, 518400, 0])
print("        P(T) =", sp.sstr(P))

# G(X,Y) := X^13 - 4Y^13 - (P(X) - 4P(Y))  -- the lower-degree remainder
Gpoly = sp.expand(Xs**13 - 4*Ys**13 - (P.subs(T, Xs) - 4*P.subs(T, Ys)))
Gexpected = sp.expand(sum((-1)**(i) * E[i] *
                          (Xs**(11 - 2*i) - 4*Ys**(11 - 2*i)) * (-1)**0
                          for i in range(6)) * 0)   # placeholder, real check below
Gterm = sp.expand( 91*(Xs**11 - 4*Ys**11) - 3003*(Xs**9 - 4*Ys**9)
                 + 44473*(Xs**7 - 4*Ys**7) - 296296*(Xs**5 - 4*Ys**5)
                 + 773136*(Xs**3 - 4*Ys**3) - 518400*(Xs - 4*Ys))
check("P(X)=4P(Y)  <=>  X^13-4Y^13 = G(X,Y) := 91(X^11-4Y^11)-3003(X^9-4Y^9)"
      "+44473(X^7-4Y^7)-296296(X^5-4Y^5)+773136(X^3-4Y^3)-518400(X-4Y)",
      sp.expand(Gpoly - Gterm) == 0)

# ------------------------------------------------------- 2. rational constants
r1, r2 = F(89, 80), F(9, 8)
Y0 = 600
C1 = F(3501, 50)           # Thue constant:   |X^13-4Y^13| <= C1 * Y^11
C  = F(3, 2)               # pinning constant: 0 < q - X/Y <= C / Y^2

check("r1 = 89/80 < q = 4^(1/13):   89^13 < 4*80^13   (exact integers)",
      89**13 < 4 * 80**13)
check("q < r2 = 9/8:                4*8^13 < 9^13",
      4 * 8**13 < 9**13)
check("r2^11 < 4 (upper bracket leaves X^11 < 4Y^11):  9^11 < 4*8^11",
      9**11 < 4 * 8**11)

# ------------------------------------------------- 3. monotonicity of P (Sturm)
Pp = sp.Poly(sp.diff(P, T), T)
check("P'(T) > 0 for all T >= 7 (Sturm: no root of P' in [7,oo), P'(7) > 0)",
      Pp.count_roots(7, None) == 0 and Pp.eval(7) > 0)
rootsPp = sp.Poly(sp.diff(P, T), T).count_roots(6, None)
print(f"        (P' has {rootsPp} real roots >= 6; largest real root of P' "
      f"is below {'6' if rootsPp == 0 else '7'})")

# --------------------------------------- 4. bracket from the equation (Sturm)
# lower: 4P(Y) > P((89/80)Y)  for Y >= Y0    (then P(X)=4P(Y)>P(r1 Y) => X>r1 Y)
Blo = sp.Poly(sp.expand(80**13 * (4*P.subs(T, Ys) - P.subs(T, F(89, 80)*Ys))), Ys)
check(f"4P(Y) - P((89/80)Y) > 0 for Y >= {Y0} (Sturm count_roots==0, value>0)",
      Blo.count_roots(Y0, None) == 0 and Blo.eval(Y0) > 0)
lo, hi = 1, 10**6
while lo + 1 < hi:                       # exact integer bisection for threshold
    mid = (lo + hi) // 2
    if Blo.eval(mid) > 0 and Blo.count_roots(mid, None) == 0:
        hi = mid
    else:
        lo = mid
Ylo_star = hi
print(f"        exact minimal integer threshold for the lower bracket: Y >= {Ylo_star}")

# upper: P((9/8)Y) > 4P(Y) for Y >= Y0'
Bhi = sp.Poly(sp.expand(8**13 * (P.subs(T, F(9, 8)*Ys) - 4*P.subs(T, Ys))), Ys)
lo, hi = 1, 10**6
while lo + 1 < hi:
    mid = (lo + hi) // 2
    if Bhi.eval(mid) > 0 and Bhi.count_roots(mid, None) == 0:
        hi = mid
    else:
        lo = mid
Yhi_star = hi
check(f"P((9/8)Y) - 4P(Y) > 0 for Y >= {Y0} (threshold Y >= {Yhi_star})",
      Bhi.count_roots(Y0, None) == 0 and Bhi.eval(Y0) > 0 and Yhi_star <= Y0)

# Lean-friendly certificate: after the shift Y -> Y0 + u, all coefficients >= 0
Blo_sh = sp.Poly(Blo.as_expr().subs(Ys, Y0 + u), u).all_coeffs()
Bhi_sh = sp.Poly(Bhi.as_expr().subs(Ys, Y0 + u), u).all_coeffs()
check(f"shift certificates: 80^13*(4P(Y)-P(89Y/80)) and 8^13*(P(9Y/8)-4P(Y)) "
      f"have ALL coefficients > 0 after Y -> {Y0}+u  (nlinarith/positivity-ready)",
      all(c > 0 for c in Blo_sh) and all(c > 0 for c in Bhi_sh))

# --------------------------------------------- 5. power-interval certificates
# for odd j and 0 <= A <= X:  X^j - A^j = (X-A) * S_j(X,A),  S_j has coeffs >= 0
for j in (1, 3, 5, 7, 9, 11, 13):
    Sj = sp.Poly(sp.cancel((Xs**j - Ys**j) / (Xs - Ys)), Xs, Ys)
    assert all(c > 0 for c in Sj.coeffs())
check("for odd j<=13, (X^j - A^j)/(X - A) has all coefficients >= 0  "
      "(so r1 Y <= X <= r2 Y  ==>  r1^j Y^j <= X^j <= r2^j Y^j)", True)

# ------------------------------------------------------ 6. exact Thue constant
t = {j: 4 - r1**j for j in (1, 3, 5, 7, 9, 11)}     # |X^j - 4Y^j| <= t_j Y^j
assert all(tv > 0 for tv in t.values())
# (r2^j < 4 for j <= 11, checked above via j=11 and r2>1, so the r1 side rules)
for j in (1, 3, 5, 7, 9, 11):
    assert r2**j < 4 and 4 - r1**j > 4 - r2**j > 0
C1_exact = ( 91 * t[11]
           + F(3003)   * t[9] / Y0**2
           + F(44473)  * t[7] / Y0**4
           + F(296296) * t[5] / Y0**6
           + F(773136) * t[3] / Y0**8
           + F(518400) * t[1] / Y0**10)
print(f"        exact C1' = 91*t11 + e2*t9/Y0^2 + ... = {C1_exact}")
print(f"                  = {float(C1_exact):.10f}   (display only)")
check(f"THUE:  C1' <= C1 = 3501/50 = 70.02   =>   |X^13 - 4Y^13| <= (3501/50) Y^11 "
      f"for Y >= {Y0} under the bracket",
      C1_exact <= C1)

# G < 0 under the bracket (one-sided approximation: X < qY):
u11 = 4 - r2**11
Gupper = (-91 * u11
          + F(3003)   * t[9] / Y0**2
          + F(296296) * t[5] / Y0**6
          + F(518400) * t[1] / Y0**10)
check("G(X,Y) < 0 under the bracket (so X^13 < 4Y^13, i.e. X/Y < q strictly):  "
      "-91(4-r2^11) + e2 t9/Y0^2 + e4 t5/Y0^6 + e6 t1/Y0^10 < 0",
      Gupper < 0)

# --------------------------------------------- 7. factorization X^13-(qY)^13
Phi = sp.expand(sum(Xs**i * (qs*Ys)**(12 - i) for i in range(13)))
prod_expr = sp.expand((Xs - qs*Ys) * Phi)
remainder = sp.rem(prod_expr - (Xs**13 - 4*Ys**13), qs**13 - 4, qs)
check("X^13 - 4Y^13 = (X - qY) * sum_{i=0..12} X^i (qY)^{12-i}   (mod q^13 = 4)",
      sp.expand(remainder) == 0)
# each of the 13 terms of Phi is >= (r1 Y)^12 when X >= r1 Y and qY >= r1 Y:
#   Phi >= 13 r1^12 Y^12.  Final division:
C_exact = C1 / (13 * r1**12)
C_true  = C1_exact / (13 * r1**12)
print(f"        C1/(13 r1^12)      = {C_exact}  =  {float(C_exact):.10f}")
print(f"        sharpest (C1'/..)  = {C_true}   =  {float(C_true):.10f}")
check("PIN:  C1/(13*(89/80)^12) <= 3/2   =>   0 < q - X/Y <= (3/2)/Y^2 "
      f"for every solution with Y >= {Y0}",
      C_exact <= C)

# --------------------------------------- 8. exact asymptotic pinning constant
# lim Y^2 * (q - X/Y) = 91 (4 - q^11) / (13 q^12) = 7 (q - 1/q)
lhs_num = sp.Poly(sp.expand(91 * (4 - qs**11) * qs * 4), qs)          # *4q
rhs_num = sp.Poly(sp.expand(7 * (qs**2 - 1) * 13 * qs**12), qs)       # *13q^13->52... careful:
# 91(4-q^11)/(13 q^12) - 7(q-1/q) = 0  <=>  91(4-q^11)*q = 91(q^2-1)*q^12 ... verify mod q^13-4:
diff = sp.rem(sp.expand(91*(4 - qs**11)*qs - 7*(qs**2 - 1)*13*qs**12),
              qs**13 - 4, qs)
check("asymptotic constant identity:  91(4-q^11)/(13 q^12) = 7(q - 1/q)   (mod q^13=4)",
      sp.expand(diff) == 0)
import mpmath as mp
mp.mp.dps = 40
qv = mp.mpf(4) ** (mp.mpf(1)/13)
print(f"        7(q - 1/q) = {mp.nstr(7*(qv - 1/qv), 25)}   (asymptotically sharp)")
print(f"        general odd k:  C_k^asy = (k^2-1)/24 * (4^(1/k) - 4^(-1/k));"
      f"  k=5 gives {mp.nstr((25-1)/mp.mpf(24)*(4**(mp.mpf(1)/5) - 4**(-mp.mpf(1)/5)), 12)}"
      "  (matches banked k=5 value 0.5616496...)")

# ------------------------------------------------- 9. small-Y / window bridge
# window: 4(n+1)^13 <= (n+d+1)^13  and  (n+d+13)^13 <= 4(n+13)^13
#   (first/last ratio vs geometric mean; classical, banked machinery)
# => n+1 <= c d  and  n+13 >= c d,  c = 1/(q-1).
check("q-bracket for the window constant:  111253^13 < 4*100000^13 < 111254^13  "
      "(so  8.88573 < c = 1/(q-1) < 8.88652)",
      111253**13 < 4 * 100000**13 < 111254**13)
# c > 1/0.11254 > 8.88573:  d >= 221  =>  n >= c*221 - 13 > 1950.74  => n >= 1951
lower_n = F(100000, 11254) * 221 - 13
check("d >= 221  ==>  n >= c*221 - 13 > 1950  ==>  Y = n+7 >= 1958 >= Y0 = 600  "
      "(banked d<=220 machinery covers everything below)",
      lower_n > 1950 and 1958 >= Y0)
# scan-bound translation: Y <= cd + 6 <= (100000/11253) d + 6, so
#   d <= 1.125e99  ==>  Y < 10^100
D_target = 1125 * 10**96
check("d <= 1.125*10^99  ==>  Y <= c*d + 6 < 10^100   (exact rational check)",
      F(100000, 11253) * D_target + 6 < 10**100)

# ------------------------------------------------------- 10. grid validation
print("grid validation (exact integer arithmetic on every point) ...")
import math
def iroot13(n):
    """floor(n^(1/13)) by pure-integer Newton iteration."""
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + 12) // 13)
    while True:
        r2 = (12 * r + n // r**12) // 13
        if r2 >= r:
            break
        r = r2
    while r**13 > n:
        r -= 1
    while (r + 1)**13 <= n:
        r += 1
    return r

grid_Y = [600, 601, 733, 1000, 5000, 12345, 100007, 1000003]
tested = thue_pass = 0
for Y in grid_Y:
    Xmin = (89 * Y) // 80 + 1
    Xmax = (9 * Y) // 8
    step = max(1, (Xmax - Xmin) // 47)
    Xq = iroot13(4 * Y**13)                       # floor(qY): the Thue-relevant X
    Xlist = sorted(x for x in set(list(range(Xmin, Xmax + 1, step))
                                  + [Xmin, Xmax, Xq, Xq + 1]) if Xmin <= x <= Xmax)
    for X in Xlist:
        tested += 1
        Gval = (91*(X**11 - 4*Y**11) - 3003*(X**9 - 4*Y**9)
                + 44473*(X**7 - 4*Y**7) - 296296*(X**5 - 4*Y**5)
                + 773136*(X**3 - 4*Y**3) - 518400*(X - 4*Y))
        assert 50 * abs(Gval) <= 3501 * Y**11, (X, Y)          # |G| <= C1 Y^11
        assert Gval < 0, (X, Y)                                # G < 0
        if 50 * abs(X**13 - 4*Y**13) <= 3501 * Y**11:          # Thue filter
            thue_pass += 1
            # conclusion |q - X/Y| <= (3/2)/Y^2, exact 13th-power form:
            assert (2*X*Y - 3)**13 < 4 * (2*Y**2)**13 < (2*X*Y + 3)**13, (X, Y)
check(f"grid: |G|<=C1*Y^11 and G<0 on {tested} bracketed (X,Y) points; "
      f"{thue_pass} points pass the Thue filter and every one satisfies the "
      f"exact 13th-power pinning inequality (2XY-3)^13 < 4(2Y^2)^13 < (2XY+3)^13",
      True)

print()
print(f"ALL {PASS} CHECKS PASSED.")
print("=" * 72)
print("Chain proved (exact, Y >= 600; Y >= 1958 automatic for d >= 221):")
print("  P(X)=4P(Y)  =>  89Y/80 < X < 9Y/8          [Sturm + shift certificates]")
print("              =>  |X^13-4Y^13| <= (3501/50) Y^11,  X^13 < 4Y^13")
print("              =>  0 < q - X/Y <= (3/2)/Y^2,   q = 4^(1/13)")
print("Worley (C=3/2, rs<3)  =>  X/Y confined to the quasi-convergent family;")
print("see cf_scan.py for the exact CF of 4^(1/13) and the 10^100 scan.")
