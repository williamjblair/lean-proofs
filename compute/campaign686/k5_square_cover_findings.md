# Erdős 686, k = 5: discriminant square-cover audit

Date: 2026-07-10

Verdict: imposing that the quadratic root `z` is a positive square does not
produce a lower-genus curve.  It reconstructs the original smooth plane
quintic, a genus-6 double cover of the genus-2 discriminant curve.  The only
rational automorphism quotient detected is the known sign quotient; the
complementary Prym is a Q-simple fourfold by an exact good-reduction test, so
there is no elliptic factor to exploit.  A useful arithmetic descent survives:
the square `z=g^2` divides `4(4v-u)` and hence `25g^2 < 269v` in the required
ratio window.  This is a genuine restriction but not a contradiction.

## 1. Exact equivalence and genus

Let

```text
P(T) = T(T^2-1)(T^2-4) = T^5-5T^3+4T.
```

For a putative positive integral solution write `X=gu`, `Y=gv`,
`gcd(u,v)=1`, and `z=g^2`.  Dividing `P(X)=4P(Y)` by `g` gives

```text
A z^2 - 5 B z + 4 C = 0,
A=u^5-4v^5,  B=u^3-4v^3,  C=u-4v.
```

Its discriminant is exactly

```text
D(u,v) = 25B^2-16AC
       = 9u^6+64u^5v-200u^3v^3+64uv^5+144v^6.
```

Put `t=u/v=X/Y` and `q=Y=gv`.  The condition that the quadratic root is
the square `z=g^2` is equivalent to

```text
C6: (t^5-4)q^4 - 5(t^3-4)q^2 + 4(t-4) = 0.             (1)
```

After `X=tq`, `Y=q`, (1) is precisely `P(X)=4P(Y)`.  Its smooth projective
model is the plane quintic

```text
X^5-5X^3Z^2+4XZ^4 - 4Y^5+20Y^3Z^2-16YZ^4 = 0.         (2)
```

The involution `sigma:[X:Y:Z] -> [-X:-Y:Z]` has six geometric fixed points:
`[0:0:1]` and the five points at infinity `Z=0, X^5=4Y^5`.  On `Y != 0`,
the quotient coordinates are `t=X/Y` and `s=Y^2`; the quotient equation is

```text
(t^5-4)s^2 - 5(t^3-4)s + 4(t-4) = 0.
```

With

```text
y = 2(t^5-4)s - 5(t^3-4),
```

this becomes the supplied genus-2 curve

```text
y^2 = 9t^6+64t^5-200t^3+64t+144.                       (3)
```

Conversely `s=(y+5(t^3-4))/(2(t^5-4))`, away from the usual finite chart
exceptions.  Thus adjoining `q=sqrt(s)` is the degree-2 cover (2) -> (3).
Riemann-Hurwitz with six branch points gives

```text
2g(C6)-2 = 2(2*2-2)+6 = 10,
g(C6)=6.
```

This is not a new cover of lower complexity: it is the original genus-6
integral-point problem in birational coordinates.

Exact local reproduction:

```bash
python3 compute/campaign686/k5_square_cover_verify.py
```

The script checks the discriminant and cover identities symbolically.  It also
checks smoothness in the affine chart by the nonzero elimination resultant

```text
Res_Y(Res_X(F,F_X),F_Y)
= 5632423289562096797315084845056000000000000000000000000
= 2^76 * 3^12 * 5^24 * 139^2 * 349^2.
```

At infinity, `F=X^5-4Y^5` and its `X,Y` derivatives cannot vanish together
at a projective point in characteristic zero.

Magma V2.29-8 independently returned:

```magma
Q:=Rationals();
P2<x,y,z>:=ProjectiveSpace(Q,2);
F:=x^5-5*x^3*z^2+4*x*z^4-4*y^5+20*y^3*z^2-16*y*z^4;
C:=Curve(P2,F);
IsNonsingular(C);
Genus(C);
IsAbsolutelyIrreducible(C);
```

```text
true
6
true
```

## 2. Automorphisms and the Jacobian obstruction

The characteristic-zero automorphism computation exceeded the public
calculator's 60-second limit.  Exact good-reduction computations gave:

```magma
for p in [7,11,13,17] do
  K:=GF(p);
  P2<x,y,z>:=ProjectiveSpace(K,2);
  C:=Curve(P2,x^5-5*x^3*z^2+4*x*z^4
              -4*y^5+20*y^3*z^2-16*y*z^4);
  print p, IsNonsingular(C), #AutomorphismGroup(C);
end for;
```

```text
7  true 2
11 true 2
13 true 2
17 true 4
```

In particular, reduction at both 7 and 11 has automorphism group of order 2.
The specialization kernel for automorphisms of a good-reduction genus-at-least-2
curve is a p-group.  Applying this at both primes shows that the Q-rational
automorphism group has order dividing both `2*7^a` and `2*11^b`, hence order
at most 2.  It contains `sigma`, so it is exactly `C2`.  Therefore there is no
second quotient arising from a Q-rational automorphism.

The sign cover gives the expected isogeny

```text
Jac(C6) ~ Jac(C2) x Prym(C6/C2),
dimensions 6 = 2 + 4.
```

The local L-polynomials make the remaining obstruction precise.  The Magma
command below was run at `p=7,11,13`:

```magma
K:=GF(p);
P2<x,y,z>:=ProjectiveSpace(K,2);
C:=Curve(P2,x^5-5*x^3*z^2+4*x*z^4
            -4*y^5+20*y^3*z^2-16*y*z^4);
R<t>:=PolynomialRing(K);
B:=HyperellipticCurve(9*t^6+64*t^5-200*t^3+64*t+144);
LC:=LPolynomial(C); LB:=LPolynomial(B);
Factorization(LC);
LB;
Factorization(ExactQuotient(LC,LB));
```

At `p=11` it returned

```text
LB = 121*x^4 + 55*x^3 + 15*x^2 + 5*x + 1

LPrym = 14641*x^8 + 10648*x^7 + 3993*x^6 + 1474*x^5
        + 523*x^4 + 134*x^3 + 33*x^2 + 8*x + 1.
```

Both displayed factors are irreducible over Z.  The degree-8 Prym factor was
also irreducible at `p=7` and `p=13`.  Consequently the Prym fourfold is
Q-simple, and the degree-4 base factor is Q-simple as well.  In particular
`Jac(C6)` has no Q-elliptic quotient: an elliptic quotient would contribute a
degree-2 integral factor to the good-reduction L-polynomial at 11, but none
exists.  Thus the square lift does not expose an elliptic Chabauty shortcut.

## 3. Exact square-divisor descent

Assume positive integers `u,v,z`, `gcd(u,v)=1`, `z` a nonzero square,

```text
131v < 100u < 132v
```

and `Az^2-5Bz+4C=0`.  Set

```text
a=4v^5-u^5, b=4v^3-u^3, c=4v-u.
```

Then `b,c>0`.  Also `v>=2`, `3u<4v`, and

```text
5b > 5*(44/27)v^3 > 16v > 4c.
```

If `A>=0`, the original left side is
`Az^2+5bz-4c >= 5b-4c > 0`, impossible.  Hence `A<0`, so `a>0` and

```text
a z^2 - 5b z + 4c = 0,
z(5b-az)=4c.                                             (4)
```

Therefore, with `h=5b-az`,

```text
z h = 4c,  h>0,  a z+h=5b,
z | 4(4v-u).
```

Since `100u>131v`, `100c<269v`; hence

```text
25z < 269v.
```

For `z=g^2`, this is the exact bound `25g^2<269v`.  If `d=X-Y=g(u-v)`,
then `25(u-v)<8v`, and squaring and combining gives

```text
15625 d^2 < 17216 v^3.                                  (5)
```

There is also a nearly-coprime factorization.  From `gcd(u,v)=1`,

```text
gcd(b,c) | 60,
gcd(a,b) | 60.
```

For example, modulo a common divisor of `b,c`, one has `u=4v` and hence
`b=-60v^3`, while `v` is invertible.  The second claim follows from

```text
(-T^2-4T-1)(4-T^5)
+(T^4+4T^3+T^2+4T+16)(4-T^3) = 60.
```

Equation (4) then gives

```text
gcd(z,h) | 1200.
```

Thus away from `2,3,5`, the square factor `z` and its cofactor `h` in
`4(4v-u)` are coprime.  This is a genuine descent input, but proving that no
such factorization also satisfies `az+h=5b` remains a global integral-point
problem; no contradiction was obtained from it.

## 4. Congruence and local audit

No finite congruence obstruction can close the reduced square problem, even
with primitivity and the real ratio window imposed.  For every modulus
`M>=1`, take

```text
v = 107400 M + 1,
u = 141231 M + 4,
z = M^2.
```

Then

```text
100u-131v = 53700M+269 > 0,
132v-100u = 53700M-268 > 0,
4v-u = 537^2 M.
```

Any common divisor of `u,v` divides `4v-u=537^2M`, but `v` is congruent to
1 modulo both `537` and `M`; hence `gcd(u,v)=1`.  The value of
`Az^2-5Bz+4C` is divisible by `M`: its first two terms contain `M^2`, and
`C=u-4v=-537^2M`.  Thus every finite collection of congruence tests (replace
`M` by their product) has a primitive square-z survivor in the exact target
window.

The verification script also checks nonsingular points modulo
`3,5,7,11,13,17,19,23,29,31`.  At `p>=13` it uses nonzero-product points:

```text
p=13: (X,Y)=(4,5)    p=17: (3,12)   p=19: (3,8)
p=23: (3,4)          p=29: (4,13)   p=31: (4,10).
```

The curve has rational zero-product points such as `(0,1)` and `(1,2)`, so
it has Q_p-points at every prime, including the bad prime 2.  The real target
component is nonempty: at `Y=100`,

```text
P(131)-4P(100) = -1411751880,
P(132)-4P(100) =    83141520,
```

so continuity gives a real point with `1.31<X/Y<1.32`.

## 5. Telescope check

For the overlapping cases `d=1,2,3,4`, the ratio `P(Y+d)/P(Y)` is strictly
decreasing for `Y>2`, since it is a product of five strictly decreasing
positive factors `1+d/(Y+j)`, `j=-2,...,2`.  The exact sign pairs are

```text
d=1: F(3)=  240, F(4)=  -360
d=2: F(6)= 3360, F(7)= -5040
d=3: F(9)=18480, F(10)=-19800
d=4: F(12)=67200,F(13)=-46080,
```

where `F(Y)=P(Y+d)-4P(Y)`.  Hence no positive integer telescope occurs.
For `d=1` the exact factorization is

```text
P(Y+1)-4P(Y) = -Y(Y-1)(Y+1)(Y+2)(3Y-11),
```

so the nontrivial rational telescope is `(X,Y)=(14/3,11/3)`, outside both
the integral domain and the target ratio interval.

## 6. Precise remaining lemma for this route

The square-cover route would close k=5 if one proved the following residual
descent statement:

> For coprime positive integers `u,v` with
> `131v<100u<132v`, there do not exist positive integers `g,h` such that
> `gcd(g^2,h)|1200` and, with
> `a=4v^5-u^5`, `b=4v^3-u^3`, `c=4v-u`,
> `g^2 h=4c` and `a g^2+h=5b`.

This is equivalent to the original reduced k=5 equation in the stated ratio
window (the extra gcd bound follows automatically), so it is **not counted as
progress by itself**.  Its value is diagnostic: it states the exact arithmetic
content exposed by the square condition, namely a nearly-coprime square-divisor
factorization of a linear form coupled to one explicit quintic/cubic identity.
No proof of this quantified lemma was found.  Reducing it back to rational
points on (2) is circular; the genus and Prym computations explain why the
ordinary genus-2 rational-points attempt did not finish it.
