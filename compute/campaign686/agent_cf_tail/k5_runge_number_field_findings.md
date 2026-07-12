# Erdős 686, k=5: Runge and number-field descent audit

Status: **exact obstruction/countercertificate, not a tail proof.**  The
classical rational Runge hypothesis fails because the five branches at
infinity form one irreducible orbit.  Separating the real branch in
`K=Q(4^(1/5))` does not give a norm-only height cutoff: an explicit algebraic
unit has positive real value below one, and its 146th power is already below
`10^-166`.

Reproduce:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m \
  compute.campaign686.agent_cf_tail.k5_runge_number_field_verify
lake env lean ErdosProblems/Erdos686K5RungeObstruction.lean
```

## 1. The rational Runge branch count

For

```text
P(T)=T(T^2-1)(T^2-4),
```

the projective closure of `P(X)=4P(Y)` has leading equation

```text
X^5-4Y^5=0
```

at infinity.  Since `Y=0` would force `X=0`, every infinity point has
`t=X/Y` and satisfies

```text
t^5-4=0.                                                   (1)
```

Lean proves `T^5-4` irreducible over `Q` as
`k5_infinity_polynomial_irreducible`; the proof uses the exact 2-adic
valuation contradiction `5*v_2(b)=2`.  Independently, the Python verifier
reduces modulo 11 and checks all 11 monic linear and 121 monic quadratic
possible divisors.  A reducible quintic has a factor of degree at most two,
so this is a complete finite irreducibility certificate.

Thus the five geometric branches are one degree-five closed point over `Q`,
not two rational Galois orbits.  The standard rational Runge condition that
separates distinct infinity orbits is absent.  This is a structural failure,
not a failure to search far enough, so it cannot yield any cutoff—let alone
one at `10^166`.

## 2. Exact number-field unit obstruction

Let `a^5=4`.  In `Z[a]`, put

```text
epsilon = 1+a-a^3,
eta     = 3a^4+4a^3+5a^2+7a+9.
```

The exact polynomial identity is

```text
epsilon*eta - 1 = (-3a^2-4a-2)(a^5-4),
```

so `epsilon*eta=1`.  Lean banks this as `k5_runge_unit_inverse` and banks
the identity for every positive power.  The independent verifier reproduces
the coefficient multiplication exactly.

For the distinguished real root, the integer bracket

```text
131^5 < 4*100^5 < 132^5
```

gives `1.31<a<1.32`.  Exact rational cube bounds then give

```text
0 < 1+1.31-1.32^3 < epsilon
  < 1+1.32-1.31^3 < 9/125 < 1.                       (2)
```

The two rational endpoints in (2) are respectively

```text
627/62500, 71909/1000000.
```

Lean proves positivity, the `9/125` upper bound, and the target-scale
certificate

```text
epsilon^146 < (9/125)^146 < 10^-166.                    (3)
```

The exact verifier also confirms that exponent 145 does not yet make the
coarse bound smaller than `10^-166`, while 146 does.

Consequently an algebraic integer can have norm one and a distinguished
real absolute value far below the newly certified tail boundary.  Any
number-field descent that uses only the norm and smallness at the real branch
has no positive uniform lower bound: the unit powers are an explicit
countercertificate.

## 3. Low-genus quotient check

The existing square-cover audit already determines the quotient geometry:

```text
C: P(X)=4P(Y)                         genus 6,
C/<(X,Y)->(-X,-Y)>                   genus 2,
complementary Prym                   dimension 4.
```

Exact good-reduction automorphism computations at 7 and 11 leave only the
sign involution over `Q`.  The genus-2 factor and the degree-8 Prym factor at
11 are both irreducible; the Prym factor is likewise irreducible at 7 and
13.  Hence no rational automorphism quotient or elliptic Jacobian factor is
available.  The genus-2 quotient plus the square condition reconstructs the
original genus-6 curve, so it is not a lower-strength tail reduction.

## 4. Verdict and precise remaining requirement

This independent route does not supply a `k=5` cutoff.  It gives two exact
negative results:

1. rational Runge cannot start because (1) is one Galois orbit; and
2. branch separation over `Q(a)` cannot be closed by a norm-only estimate,
   because (3) exhibits target-scale unit escape.

A viable number-field continuation would have to retain the coefficient
conditions forcing a unit multiple back into the two-dimensional subspace
`Q+Q*a`, then solve the resulting multi-unit equations with an explicit
linear-forms/logarithms bound below `10^166`.  No such bound is obtained
here.  Replacing those coefficient equations by “the unit exponent is
bounded” would be circular and is not counted as progress.
