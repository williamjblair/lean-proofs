# Hostile audit: simultaneous odd fifth gcd/eliminant probe

## Verdict

This probe does not close the nonreflected exactly-three branch.

It does prove a new simultaneous inequality in 442 of the 1,008 geometries.
For the primitive fifth-leading cross weights described below, all three
weighted normalized numerators have one sign, and exact elimination gives

```text
sum_s |mu_s| P_s^2 <= H_k g^4 d.
```

The six exact row constants `H_k` are listed below.  This is stronger than
three unrelated component bounds, but it is exponent-neutral: weighted
AM-GM turns it into a lower bound on `d`, not an upper bound.

The other two fifth-leading cross orientations are sign-mixed in every one
of the 1,008 geometries.  The third orientation is sign-mixed in the
remaining 566 geometries.  Moreover, the three natural constant-weight
resultant packings are full rank at precisely the degree that would have to
cancel to save a factor of `d`, even after quotienting by the full exact
block-difference polynomial.  The raw triple product has known divisor
degree 14 and polynomial degree 15 and also has zero closing kernel modulo
the exact block equation.

This is a structural obstruction to this fifth-order magnitude/resultant
route, not a proof that every possible higher-order or component-dependent
resultant must fail.

## Exact setup

For a cyclic role `s`, let `P_s` be its cleaned component and let `N_s` be
the normalized fifth numerator constructed by the Lean bridge.  Put

```text
D0 = P_1 P_2 P_3,
d  = g D0.
```

The Lean eliminant identity and the genuine divisibility `P_s | N_s` give

```text
d^4 P_s N_s = g^4 J_s,
J_s = D0^4 P_s N_s = D0^4 P_s^2 L_s
```

for a nonzero integer `L_s`.  The exact polynomial reconstructed by the
verifier is

```text
J_s = 729 C_s^2 [
        -9 C_s X_s (Y_s Z_s)^2
        + delta_s d^2 Y_s Z_s (180 E_s d + 108 D_s)
      ]
      + d^4 (27 K_s + d R1_s).
```

Here `Y_s` and `Z_s` are the two opposite residuals.  Its degree-five part
in the common residual coordinate `U`, where `X_s=U+3s`, is

```text
A_s U^5 + B_s U^2 d^3 + C_s' d^5,

A_s  = -6561 C_s^3,
B_s  = 131220 C_s^2 E_s delta_s,
C_s' = R1_s.
```

The notation `C_s'` in this display is unrelated to the local constant
coefficient `C_s`.

## Dependency tree

1. Direct selected-three Lean bridge
   1. exact decomposition `d=gPQR`;
   2. three exact square residuals;
   3. exact third and fourth quotient identities;
   4. exact normalized fifth identity;
   5. `P_s | N_s` and `N_s != 0`.
2. Exact eliminant reconstruction
   1. local coefficients `C,D,E,F,G`;
   2. reduced fourth coefficient `K`;
   3. reduced fifth linear coefficient `R1`;
   4. sparse polynomial arithmetic in `Z[U,d]`.
3. Target-window sign certificate
   1. adjacent exact rational brackets for `4^(1/k)`;
   2. exact endpoint signs;
   3. exact critical-cube exclusion;
   4. exact lower-degree remainder domination at `d>=10^1000`.
4. Simultaneous cross lattices
   1. the three cross products annihilating `(A,B)`, `(A,C')`, or `(B,C')`;
   2. primitive integer normalization;
   3. all 1,008 triples and 3,024 cyclic positions.
5. Pairwise-packing rank probes
   1. raw `J_s`;
   2. opposite-packed `X_t X_u J_s`;
   3. pair-packed `X_s J_t J_u`;
   4. the raw triple product `J_1 J_2 J_3`.
   5. quotient by every admissible polynomial multiple of the full exact
      block-difference polynomial.
6. Falsification replay
   1. the 121-digit fourth-order Hensel fixture;
   2. the 121-digit fifth-order Hensel fixture;
   3. the 1,004-digit fifth-order Hensel fixture;
   4. a small coarse-short fifth-order fixture.

## Per-node verdicts

| Node | Verdict | Reason |
| --- | --- | --- |
| Eliminant formula | exact-reproduced | Rebuilt from sparse integer polynomials; its homogeneous part is checked independently. |
| Target signs of `N_s` | exact-certified | Fractions only; endpoint, critical point, and lower-degree remainder are all checked. |
| Leading determinant | nonzero in all 1,008 cases | Exactly 504 positive and 504 negative. |
| `(A,B)` cross orientation | sign route fails | Mixed in all 1,008 cases. |
| `(A,C')` cross orientation | sign route fails | Mixed in all 1,008 cases. |
| `(B,C')` cross orientation | partial success | One-sided in 442 cases; mixed in 566. |
| One-sided simultaneous bound | proved on paper plus exact finite certificate | The algebraic derivation below is uniform; all finite constants and signs are exact-reproduced.  It is not yet Lean-formalized. |
| Raw constant-weight cancellation | fails in this family | Rank three on all monomials of degree at least four in all 1,008 cases. |
| Opposite-packed cancellation | fails in this family | Rank three on all monomials of degree at least six in all 1,008 cases. |
| Pair-packed cancellation | fails in this family | Rank three on all monomials of degree at least ten in all 1,008 cases. |
| Exact block-equation quotient | fails in these families | All four closing kernels are zero in all 1,008 cases after allowing every multiplier degree capable of affecting the cutoff. |
| Arbitrary higher-order/component-dependent resultant | not tested | No claim is made about this larger class. |
| Full exactly-three branch | open | The proved bound retains one full factor of `d`. |

## The new one-sided inequality

Take the primitive cross product of the `B` and `C'` columns:

```text
mu = B x C'.
```

It annihilates the `U^2 d^3` and `d^5` leading terms, leaving the `U^5`
term.  In 442 geometries the exact target-window certificate gives a common
sign for all three integers `mu_s N_s`.  Since `P_s>0`,

```text
|sum_s mu_s P_s N_s| = sum_s |mu_s| P_s |N_s|.
```

Write `S(U,d)=sum_s mu_s J_s(U,d)`.  From `J_s=D0^4 P_s N_s`,

```text
D0^4 sum_s mu_s P_s N_s = S(U,d).
```

The target residual bound gives `|X_s|<=36d`.  Since
`U=X_s-3s`, `s<=15`, and `d>=1`, one has the explicit bound

```text
|U| <= 81d.
```

For

```text
S(U,d) = sum_(a,b) c_(a,b) U^a d^b,
```

define

```text
H(S) = sum_(a,b) |c_(a,b)| 81^a.
```

Every monomial has `a+b<=5`, so

```text
|S(U,d)| <= H(S) d^5.
```

Using `d=gD0` and the nonzero divisibility `P_s|N_s` gives

```text
sum_s |mu_s| P_s^2
  <= sum_s |mu_s| P_s |N_s|
   = |S(U,d)| / D0^4
  <= H(S) d^5 / D0^4
   = H(S) g^4 d.
```

Taking the largest `H(S)` in each row gives:

| `k` | one-sided geometries | `H_k` | digits |
| ---: | ---: | ---: | ---: |
| 5 | 2 | 281977658168593580928 | 21 |
| 7 | 10 | 64756146619640142341307629568 | 29 |
| 9 | 34 | 19998831987650954057717903628603755593728 | 41 |
| 11 | 68 | 1697446799463578737674770682177308518186824499200 | 49 |
| 13 | 124 | 79620649493943859271436554905870151542650622317881720832000 | 59 |
| 15 | 204 | 131443214186113056779275329051984784346429689046767891479303458232729600000 | 75 |

The smallest absolute primitive weight occurring in each row is respectively

```text
203,
10543,
12339295,
164430032,
103538921875,
47767948526030.
```

These numbers are certificate outputs, not asymptotic constants.

## Why the new inequality does not close

Weighted AM-GM gives

```text
3 (|mu_1 mu_2 mu_3|)^(1/3) (PQR)^(2/3)
  <= H_k g^4 d.
```

Cubing and using `PQR=d/g` yields an inequality of the form

```text
constant <= H_k^3 g^14 d.
```

This is a lower bound on `d`.  It is automatically compatible with the
target range.  The phrase "simultaneous bound" must therefore not be read as
"two component bounds independent of `d`."

## Exact resultant-degree obstruction

The following three natural expressions really do pack the three
component squares:

```text
J_s,
X_t X_u J_s,
X_s J_t J_u.
```

Their exact degree/divisor ledgers are:

| Family | known power of `D0` | polynomial degree | degree needed for an upper bound on `d` | exact high-term rank |
| --- | ---: | ---: | ---: | ---: |
| `J_s` | 4 common | 5 | at most 3 | 3 on degrees at least 4 |
| `X_t X_u J_s` | 6 | 7 | at most 5 | 3 on degrees at least 6 |
| `X_s J_t J_u` | 10 | 11 | at most 9 | 3 on degrees at least 10 |

Every rank is three in every one of the 1,008 geometries.  Thus no nonzero
constant-weight combination in any of these families reaches the required
degree drop.

This conclusion survives use of the exact block equation.  With
`U=3n-d`, its `3^k`-cleared polynomial is

```text
E_k(U,d)
  = product_(j=1)^k (U+4d+3j)
    - 4 product_(j=1)^k (U+d+3j).
```

For a packing family of polynomial degree `r` and closing cutoff `c`, the
verifier includes every monomial multiplier `Q` of degree at most `r-k` and
computes the kernel of

```text
sum_s lambda_s F_s - Q E_k
```

after projecting to all monomials of degree at least `c`.  A nonzero kernel
would be exactly a constant-weight family combination whose use of the full
block equation drops below the closing cutoff.  The kernel dimension is zero
for the raw, opposite-packed, pair-packed, and triple-product families in
all 1,008 geometries.  Multiplier degrees above `r-k` cannot help: their
product with the nonzero degree-`k` polynomial `E_k` has degree above `r`.

The direct triple product has

```text
D0^14 | J_1 J_2 J_3,
deg(J_1 J_2 J_3)=15.
```

The missing one degree is exactly the factor of `d` seen in the magnitude
bound.  The exact block-equation quotient check shows that this particular
product cannot recover the missing two-degree saving either.  Merely
multiplying the three fifth restrictions is not progress.

## Falsification record

### Small coarse-short fifth fixture

The verifier independently reconstructs

```text
k=5,
owners=(1,2,3),
(P,Q,R)=(2,5,3),
g=30,
d=900,
n=3423,
(X_1,X_2,X_3)=(9372,9375,9378),
(a,b,c)=(2343,375,1042).
```

It has pairwise-coprime components, exact square residuals, owner
divisibility, all local lifts through fifth order, all composed lifts through
fourth order, all three normalized fifth divisibilities, and nonzero named
quotients.  It satisfies

```text
5d < X_s < 14d.
```

It deliberately fails both the narrow target residual-ratio interval and
the block equation.  Thus it refutes any claim that the cyclic fifth package
plus the old coarse window is itself contradictory.

### Historical large fixtures

The exact replays give:

| Fixture | gap digits | highest replayed order | normalized remainders | upper target window | block equation |
| --- | ---: | ---: | --- | --- | --- |
| historical fourth Hensel | 121 | 4 | not applicable | false | false |
| fifth Hensel, exponent 20 | 121 | 5 | `(0,0,0)` | false | false |
| fifth Hensel, exponent 166 | 1,004 | 5 | `(0,0,0)` | false | false |

Both fifth fixtures also have all `z_s,w_s,N_s` nonzero.  They continue to
falsify congruence-only closure, but they are not counterexamples to the
target because they fail the residual window and the equation.

## Boundary and circularity checks

- Exactly the six rows `5,7,9,11,13,15` are scanned.
- Exactly the 1,008 imported nonreflected triples are scanned.  Centered
  reflected triples belong to the already-closed determinant branch.
- All three cyclic owners are included, for 3,024 position checks.
- The target sign proof uses `d>=10^1000`; the small fixture is not passed
  through that sign proof.
- No cancellation assumes `g` is coprime to a component.  Shared prime
  factors between `g` and `P,Q,R` are allowed.
- Unit components do not break the algebra, although the target
  exactly-three branch has nonunit cleaned buckets.
- The row constants bound the displayed one-sided polynomials only.  They do
  not claim an upper bound for `d`.
- Full rank rules out constant weights in the three displayed packing
  families.  The quotient scan also rules out multiplying the exact block
  equation by an arbitrary polynomial of every degree that could affect the
  closing cutoff.  It does not rule out component-dependent weights, sixth
  order, a new arithmetic gcd theorem, or a different eliminant family.
- The small and Hensel fixtures all fail the block equation; none is claimed
  to be an Erdős 686 counterexample.

## Exact remaining quantified gap

A sufficient genuinely new input is the following two-component gcd/magnitude
lemma.  Let `G_k` be the banked row loss bound and set

```text
C_k = floor((10^1000-1)/(36 G_k^10)).
```

For every target exactly-three nonreflected configuration, prove that two
distinct roles `r,s` satisfy

```text
P_r^2 P_s^2 <= C_k g^8.
```

Indeed, the remaining residual has `P_t^2 < 36d`; using
`d=gP_rP_sP_t` gives

```text
P_t < 36 g P_r P_s,
d < 36 g^2 (P_rP_s)^2
  <= 36 C_k g^10
  <= 36 C_k G_k^10
  < 10^1000,
```

contrary to the target cutoff.  The present fifth-order inequality does not
prove this lemma because its right side is `H_k g^4 d`.

## Reproduction

```text
python3 -m pytest -q \
  compute/campaign686/agent_odd_fifth_gcd_eliminant/test_odd_fifth_gcd_eliminant_verify.py

python3 -m \
  compute.campaign686.agent_odd_fifth_gcd_eliminant.odd_fifth_gcd_eliminant_verify
```
