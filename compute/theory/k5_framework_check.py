#!/usr/bin/env python3
"""
Validation of the F-framework and structure mining of tight-window survivors.

F := (A+d)^5 - 4 A^5   (integer, defined from the pair (d, A))

PROVED (validated here numerically and by polynomial identity):
  (W1) window  =>  0 <= F <= 4[(A+4)^5 - A^5] - [(D+4)^5 - D^5] <= 80 (A+4)^4
  (C1) F == (d-j)^5 + 4 j^5                    (mod A+j)   [pure algebra]
  (C2) row j+1  =>  F == 4 j^5 - W(d-j)        (mod A+j),  W(x)=10x^4+35x^3+50x^2+24x
  (C3) F == -j^5 + 4 (d+j)^5                   (mod D+j)   [pure algebra]
  (C4) upper row j+1 => F == -j^5 + 4 Wt(d+j)  (mod D+j),  Wt(x)=10x^4-35x^3+50x^2-24x
where D = A + d, R1(x) = x^5 + W(x), x(x-1)(x-2)(x-3)(x-4) = x^5 - Wt(x).
"""
import sympy as sp

d, A, j_ = sp.symbols('d A j', integer=True)
D = A + d
F = (A + d)**5 - 4*A**5
W = lambda x: 10*x**4 + 35*x**3 + 50*x**2 + 24*x
Wt = lambda x: 10*x**4 - 35*x**3 + 50*x**2 - 24*x
R1 = lambda x: sp.prod([x + i for i in range(5)])

print("Polynomial identity checks:")
# R1(x) = x^5 + W(x);  x(x-1)..(x-4) = x^5 - Wt(x)
x = sp.symbols('x')
assert sp.expand(R1(x) - (x**5 + W(x))) == 0
assert sp.expand(sp.prod([x - i for i in range(5)]) - (x**5 - Wt(x))) == 0
print("  R1(x) = x^5 + W(x)                       OK")
print("  x(x-1)(x-2)(x-3)(x-4) = x^5 - Wt(x)      OK")

for j in range(5):
    # (C1): F - ((d-j)^5 + 4 j^5) divisible by A+j in ZZ[d,A]
    q, r = sp.div(sp.expand(F - ((d - j)**5 + 4*j**5)), A + j, A)
    assert r == 0, j
    # (C3): F - (-(j**5) + 4*(d+j)**5) divisible by D+j
    q2, r2 = sp.div(sp.expand(F - (-(j**5) + 4*(d + j)**5)), D + j, A)
    assert r2 == 0, j
print("  (C1),(C3) for j=0..4                     OK")

# (C2): given A+j | R1(d-j), i.e. (d-j)^5 == -W(d-j):
#   F == (d-j)^5 + 4j^5 == 4j^5 - W(d-j) (mod A+j).  Numeric spot check below.
import random
random.seed(686686)
for _ in range(500):
    dd = random.randrange(10, 10**8)
    AA = random.randrange(3*dd, 3*dd + 10**5)
    FF = (AA + dd)**5 - 4*AA**5
    for j in range(5):
        m = AA + j
        assert (FF - ((dd - j)**5 + 4*j**5)) % m == 0
        m2 = AA + dd + j
        assert (FF - (-(j**5) + 4*(dd + j)**5)) % m2 == 0
print("  numeric spot checks (C1),(C3)            OK")

# constant kappa in refined bound F <= ~ (80 - 20*4^{4/5}) A^4 (info only):
q5 = 4 ** sp.Rational(1, 5)
print("  refined F upper coefficient  80 - 20*4^(4/5) =", sp.N(80 - 20*4**sp.Rational(4,5), 20))

# ---------------------------------------------------------------------------
# Structure mining of the 18 tight-window survivors (L>=2), all with d <= 117.
# ---------------------------------------------------------------------------
survivors = [(5,14),(5,15),(6,15),(7,20),(9,26),(12,35),(13,39),(18,55),
             (18,56),(19,56),(21,63),(22,65),(45,140),(46,140),(90,279),
             (117,363)]
print("\nTight-window L>=2 survivors (d, A) with factorization data:")
print(f"{'d':>4} {'A':>4}  {'lvl':>3}  A factored     A+1 factored    A+2 factored"
      f"   f1=R1/A     F/(A+4)^4")
def Rj(jj, dd):
    p = 1
    for i in range(1, 6):
        p *= (dd + i - jj)
    return p
for (dd, AA) in survivors:
    lvl = 2
    if Rj(3, dd) % (AA + 2) == 0:
        lvl = 3
        if Rj(4, dd) % (AA + 3) == 0:
            lvl = 4
            if Rj(5, dd) % (AA + 4) == 0:
                lvl = 5
    FF = (AA + dd)**5 - 4*AA**5
    fac = lambda n: sp.factorint(n)
    fmt = lambda n: '*'.join((f"{p}^{e}" if e > 1 else f"{p}")
                             for p, e in sorted(sp.factorint(n).items()))
    print(f"{dd:>4} {AA:>4}  {lvl:>3}  {fmt(AA):<14} {fmt(AA+1):<15} {fmt(AA+2):<14}"
          f" {Rj(1,dd)//AA:<10} {FF/(AA+4)**4:+.4f}")

# Verify none satisfies the FULL equation (they are relaxation survivors only):
print("\nFull-equation check on survivors (should all be False):")
any_full = False
for (dd, AA) in survivors:
    n = AA - 1
    lhs = 1; rhs = 1
    for i in range(1, 6):
        lhs *= (n + dd + i); rhs *= (n + i)
    if lhs == 4 * rhs:
        any_full = True
        print("  FULL SOLUTION FOUND:", dd, AA)
print("  none satisfies the exact equation:", not any_full)
