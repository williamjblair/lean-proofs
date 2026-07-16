# Erdős 686, k=5: integral lift and surviving tail

Date: 2026-07-16

## Kernel-banked integral lift

For a centered integral solution

```text
P5(v)=4P5(u),  P5(T)=T^5-5T^3+4T,
```

the weighted-projective coordinates

```text
(A:B:C) =
(v : 10v^3-40u^3-16v+64u : 2u)
```

satisfy the reduced genus-two equation.  In affine coordinates,

```text
X=A/C=v/(2u),
Z=B/C^3.
```

The exact polynomial identity checked in Lean is

```text
B^2 - F(A,C) = -64(4u-v)(P5(v)-4P5(u)).
```

For `u>=3`, Lean also proves that `P5` is strictly increasing and

```text
P5(2u)-4P5(u)=4u(7u^4-5u^2-2)>0.
```

Hence every positive centered solution satisfies

```text
u<v<2u.
```

The same module proves

```text
|B|<46u^3
```

and the exact cubed height form

```text
max(v^3,(2u)^3,|B|)<(4u)^3.
```

Primitive weighted reduction can only decrease the corresponding
multiplicative height.

## Stronger finite exclusion

The new window `d=v-u<u` connects directly to the already kernel-checked
small-core and Farey certificates.  It yields the stronger theorem

```text
u<10^1000, v-u>=5
  -> not P5(v)=4P5(u).
```

Thus the requested `u<=5000` theorem is a strict corollary.  The conditional
`H(P)<=20000` Mordell-Weil sieve remains independently valid, but is not
needed for this stronger finite range.

## Sharp fifth-root approximation

Let

```text
alpha=4^(1/5).
```

For every centered solution with `u>=1425`, Lean proves the rational lower
bracket

```text
1319507*u < 1000000*v
```

and the exact one-sided approximation

```text
|v/u-alpha| <
  (1702608047245783157000000 /
   3031424763402858403856401) / u^2.
```

The rational constant is approximately

```text
0.561652747513535.
```

It is below `0.562` but above `1/2`.  Therefore it does not by itself invoke
the simplest Legendre convergent criterion.  There is no smallest rational
constant obtainable merely by choosing a closer rational lower bracket for
`alpha`; these constants approach the irrational asymptotic coefficient
from above.

## Runge and cover audits

Classical Runge does not apply: the five branches at infinity form one
irreducible rational orbit.  Over the fifth-root field, the explicit
norm-one unit `1+a-a^3` has arbitrarily small positive real powers, blocking
a norm-plus-one-embedding size argument.

The normalized square lift has also already been audited.  It reconstructs
the original smooth plane quintic, a genus-6 double cover of the genus-2
curve.  Its complementary Prym is a Q-simple fourfold, so this cover does
not expose an elliptic quotient.

An attempted degree-10 unordered `3+3` partition field does not factor the
sextic: exact Magma output gives factor degrees `[6]`.  Distinguishing the
two complementary triples requires the associated quadratic extension, so
this does not improve on the existing degree-15 `2+4` pair field.

## Exact remaining k=5 obligation

The only surviving centered range is now

```text
u>=10^1000,
v-u>=5,
P5(v)=4P5(u).
```

In that range the proper-support theorem also applies, forcing all 25
canonical owner cells to be nontrivial.  Since the five positive lower
residuals and the five positive upper residuals each multiply to `G|24`,
Lean now also proves that some lower residual is one and some modified upper
residual is one.  Hence every survivor has a fully owned row and a fully
owned column crossing at a nontrivial cell.  This is not yet a contradiction:
the remaining theorem must combine the finite residual profiles with all
five adjacent row equations, all five adjacent column equations, and the
nine diagonal divisibility capacities.

No global completeness theorem is claimed here.
