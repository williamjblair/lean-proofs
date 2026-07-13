# Hostile audit: Erdős 686 quotient-zero ledger and fifth normalization

Date: 2026-07-12

Verdict: **PASS as an equation-facing ledger correction and exact
dead-route certificate; FAIL as a proof of the live joint-nonzero residual.**

## Dependency tree

```text
N0  full Erdős 686 contradiction                                  OPEN
|
+- N1 exact-ratio three-bucket obstruction nonvanishing           BANKED
|  `- actual block equation, exact decomposition, d>=10^120
|
+- N2 obstruction identities T_s=P_s^2*z_s                        INPUT
|  `- N1 + N2 imply z_1,z_2,z_3 are all nonzero                   PASS
|
+- N3 historical noncentral two-zero scan                         PASS
|  +- 2,603 placements reconstructed independently                PASS
|  +- 27 zero-weight contradictions                               PASS
|  +- 2,576 numerical closures at 10^1000                         PASS
|  `- sharp global cutoff has 131 digits                          PASS
|
+- N4 all-owner reflected difference packs both buckets           FAIL
|  `- missing cross-divisibilities; exact mod-49 falsifier         PASS
|
+- N5 reduced fifth coefficient has a new fixed constant          FAIL
|  `- R5(0)=27*K4 identically                                      PASS
|
`- N6 normalized fifth quotient lift                              PASS
   `- P | 27*w + (d/P)*S1*g^4; w remains unbounded                 OPEN USE
```

N2 is not a new mathematical premise in applications: it is the definition
of the named third quotient.  The quotient-nonzero theorem does not cancel
`P^2`, assume `P>0`, or use primality; substituting `z_s=0` makes the named
obstruction zero directly.

## Exact finite scope

The historical scan covers exactly

```text
{(k,{i,j,l},{two zero positions}):
  k in {5,7,9,11,13,15},
  1<=i<j<l<=k,
  neither zero owner is the center}.
```

Its cardinality is 2,603.  A zero remaining primitive weight occurs exactly
for a reflected triple `(center-r,center,center+r)` with both endpoints zero,
giving `(k-1)/2` cases per row and 27 total.  Every other case is checked by
the exact strict integer inequality.  No floating-point estimate certifies a
closure.

## Failed all-owner reflected-pair inference

On the full odd grid the identities

```text
Delta_i=C_i,
F_i=C_i*H_i,
H_i-H_j=24*D_i*3^(k-1)*g^2
```

for reflected `j=k+1-i` are correct.  Gcd stripping gives divisibilities
`q_i|H_i` and `q_j|H_j`.  The proposed step

```text
q_i*q_j | H_i-H_j
```

is false: coprimality of `q_i,q_j` does not give `q_i|H_j` or `q_j|H_i`.
The existing exact full-grid window fixture

```text
k=5, n=25177, d=6790, g=97,
(P_1,...,P_5)=(2,7,5,1,1)
```

satisfies gap reconstruction, pairwise bucket coprimality, the short
residual window, the step-three progression, and all composed second/third
divisibilities.  For the reflected pair `(2,4)`,

```text
q_2=49,
q_4=1,
H_2-H_4=-91455480 == 31 (mod 49).
```

Thus the load-bearing divisibility fails inside the intended algebraic
scope.  Replacing the product by a gcd or lcm does not recover the escaped
factor 49.

## Fifth-order audit

Expanding the public definitions over signed integers gives

```text
R5(d)=27*K4+d*S1+d^2*S2.
```

This is proved in Lean as a polynomial identity and reproduced on exact
signed fixtures.  With `d=P*M`, the `d^2` term is divisible by `P^2`, but
the constant is precisely 27 times the old fourth coefficient.  After
writing the fourth numerator as `P*w`, cancellation yields only

```text
P | 27*w+M*S1*g^4.
```

The 121-digit fifth Hensel/CRT fixture satisfies the local and composed
fifth lifts, squared and reduced quotient congruences, nonzero third
obstructions, and the third-quotient lattice.  It fails the exact block
equation and short window.  It therefore falsifies a congruence-only fixed
resultant while remaining outside the equation-facing theorem.

The same construction at exponent 166 has a 1,004-digit gap and again
satisfies the congruence package while failing the equation and upper
window.  Hence the upgraded cutoff does not by itself turn the local
congruences into a contradiction.

## Boundary matrix

| Boundary | Verdict |
|---|---|
| center reduced-fourth coefficient `K=0` | quotient-zero branch still excluded by exact-ratio nonvanishing |
| 27 reflected zero-weight placements | exact lattice contradiction in historical scan; superseded equation-facing |
| unit buckets | retained literally as `1`; never counted as live support |
| primes 2 and 3 | included through the unchanged aggregate-loss construction |
| `k=9,n=2,d=1` and `k=15,n=4,d=1` | exact equations outside `d>=10^120` |
| 121/130/1,004-digit CRT fixtures | congruence fixtures; fail equation and short window |
| nonreflected all-nonzero triples | not closed by this checkpoint |
| support cardinality at least four | not closed by this checkpoint |

## Final quantified gap

The exact odd residual is to prove that no target-row equation at
`d>=10^1000` admits an all-owner certificate whose nonunit support is one of
the 1,008 nonreflected triples or has cardinality at least four.  Merely
postulating a bound on the new fourth quotients would be a new missing lemma;
no such bound is asserted here.  The independent large-row residual remains
unchanged.
