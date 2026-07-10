#!/usr/bin/env python3
"""Exact checks for the k=5 square/discriminant cover.

This script uses only integer/rational polynomial arithmetic.  The separate
Magma transcript in k5_square_cover_findings.md checks the curve geometry,
finite-field automorphism groups, and local L-polynomials.
"""

from math import gcd

import sympy as sp


X, Y, Z, t, q, u, v, M = sp.symbols("X Y Z t q u v M")


def P(a):
    return a * (a * a - 1) * (a * a - 4)


# The primitive discriminant identity.
A = u**5 - 4 * v**5
B = u**3 - 4 * v**3
C = u - 4 * v
Duv = 9 * u**6 + 64 * u**5 * v - 200 * u**3 * v**3 + 64 * u * v**5 + 144 * v**6
assert sp.expand(25 * B**2 - 16 * A * C - Duv) == 0


# The quotient and square-cover identity.  On Fcover=0, y^2=D(t,1).
Dt = 9 * t**6 + 64 * t**5 - 200 * t**3 + 64 * t + 144
Fcover = (t**5 - 4) * q**4 - 5 * (t**3 - 4) * q**2 + 4 * (t - 4)
y = 2 * (t**5 - 4) * q**2 - 5 * (t**3 - 4)
assert sp.expand(y**2 - Dt - 4 * (t**5 - 4) * Fcover) == 0


# Exact affine smoothness elimination for P(X)-4P(Y)=0.  At infinity,
# X^5-4Y^5=0 has no common projective zero with its X,Y derivatives.
Faff = sp.expand(P(X) - 4 * P(Y))
RX = sp.resultant(Faff, sp.diff(Faff, X), X)
smooth_resultant = sp.resultant(RX, sp.diff(Faff, Y), Y)
expected_smooth_resultant = 2**76 * 3**12 * 5**24 * 139**2 * 349**2
assert smooth_resultant == expected_smooth_resultant


# A real point lies on the target branch with 1.31 < X/Y < 1.32.
assert P(131) - 4 * P(100) == -1_411_751_880
assert P(132) - 4 * P(100) == 83_141_520


# The only overlapping-block cases are d=1,...,4.  Their unique positive
# real crossings lie strictly between the listed consecutive integers.
for d, y0, left, right in [
    (1, 3, 240, -360),
    (2, 6, 3360, -5040),
    (3, 9, 18480, -19800),
    (4, 12, 67200, -46080),
]:
    assert P(y0 + d) - 4 * P(y0) == left
    assert P(y0 + 1 + d) - 4 * P(y0 + 1) == right
assert sp.factor(P(Y + 1) - 4 * P(Y)) == -Y * (Y - 1) * (Y + 1) * (Y + 2) * (3 * Y - 11)


# A primitive, square-z congruence family in the exact Archimedean window.
# It proves that no finite modulus, even after the gcd reduction and the
# requirement z=g^2, can by itself obstruct the target.
ufam = 141_231 * M + 4
vfam = 107_400 * M + 1
zfam = M**2
Efam = sp.expand(
    (ufam**5 - 4 * vfam**5) * zfam**2
    - 5 * (ufam**3 - 4 * vfam**3) * zfam
    + 4 * (ufam - 4 * vfam)
)
assert sp.rem(Efam, M, domain=sp.ZZ) == 0
assert sp.expand(100 * ufam - 131 * vfam) == 53_700 * M + 269
assert sp.expand(132 * vfam - 100 * ufam) == 53_700 * M - 268
assert sp.expand(4 * vfam - ufam) == 537**2 * M

for modulus in range(1, 101):
    uu = int(ufam.subs(M, modulus))
    vv = int(vfam.subs(M, modulus))
    zz = modulus * modulus
    assert gcd(uu, vv) == 1
    assert 131 * vv < 100 * uu < 132 * vv
    assert (
        (uu**5 - 4 * vv**5) * zz**2
        - 5 * (uu**3 - 4 * vv**3) * zz
        + 4 * (uu - 4 * vv)
    ) % modulus == 0


# Nonsingular finite-field points at several primes.  For p>=13 the chosen
# points also have nonzero block product, so they are not zero-product points.
local_witnesses = {
    3: (0, 1),
    5: (1, 2),
    7: (1, 2),
    11: (1, 2),
    13: (4, 5),
    17: (3, 12),
    19: (3, 8),
    23: (3, 4),
    29: (4, 13),
    31: (4, 10),
}


def Pprime(a):
    return 5 * a**4 - 15 * a**2 + 4


for prime, (xx, yy) in local_witnesses.items():
    assert (P(xx) - 4 * P(yy)) % prime == 0
    assert Pprime(xx) % prime != 0 or (-4 * Pprime(yy)) % prime != 0
    if prime >= 13:
        assert P(yy) % prime != 0


print("discriminant identity: OK")
print("square-cover identity: OK")
print(f"affine smoothness resultant: {smooth_resultant}")
print("target real branch signs: -1411751880, 83141520")
print("d=1..4 overlap/telescope exclusions: OK")
print("primitive square-z congruence family (sampled M=1..100): OK")
print("nonsingular local witnesses at p=3,5,7,11,13,17,19,23,29,31: OK")
