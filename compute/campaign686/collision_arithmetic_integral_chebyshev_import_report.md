# Erdős 686 collision arithmetic and integral Chebyshev import report

Date: 2026-07-16

## Accepted claims

### k=5 opposite-secant/tangent gcd layer

Lean module:
`ErdosProblems/Erdos686K5OppositeSecantTangentGCD.lean`

Accepted interfaces:

- `coprime_cofactor_determinant_gcd_dvd`
- `local_tangent_opposite_secant_gcd_dvd_coefficient`
- `local_tangent_opposite_secant_gcd_zero_or_le_coefficient`
- `k5_proper_global_opposite_secant_tangent_determinant_gcd`

The local theorem never inverts a secant quotient. It therefore retains the
zero-coefficient branch exactly. The proper-global theorem combines the
opposite-secant cofactor equality with the banked tangent relation, but its
displayed determinant remains an unbounded expression in the global
parameters.

SHA-256:
`e4e67667e73894f3dcc1a000b5e486c82bf3c8fd6bb8be1c0ca53b1bc84ae203`

### large-k two-regular arithmetic layer

Lean module:
`ErdosProblems/Erdos686LargeOwnerTwoRegularArithmetic.lean`

Accepted interfaces:

- exact row-aggregate and row-cofactor factorizations;
- exact identity between the product of all row cofactors and the complete
  `k`-small-prime part of the lower block;
- cancellation of a common owner from the row/diagonal/column secant
  relation;
- exact cancellation of one copy of a nonzero composite owner from the
  normalized owner-square congruence;
- canonical partner extraction and tangent specialization.

SHA-256:
`b85afcda71db160677d3c8933628b0f35429e0ee10705a75ccf574e322763002`

### contiguous integral Chebyshev tail

Lean module:
`ErdosProblems/Erdos686MatchingTailIntegralChebyshev.lean`

Accepted interfaces:

- `integral_one_div_log_sq_le_at_512`
- `integral_one_div_log_sq_le_five_halves`
- `integral_theta_div_log_sq_le_five_halves`
- `eight_mul_primeCounting_lt_of_million_le`

The base integral is split into the eight adjacent dyadic intervals
`[2,4],...,[256,512]`. The differential comparison uses
`F(x)=(5/2)x/log(x)^2` and the exact implication
`log(x)>10/3 -> 1/log(x)^2 <= F'(x)`. Abel summation, the formal Chebyshev
theta bound, and `2^33<10^10` prove
`8 * Nat.primeCounting k < k` for every `k>=10^6`.

An independent proof audit recomputed the dyadic rational margin, the
derivative comparison, and the final coefficient margin. All acceptance
conditions are exact; no floating-point comparison is used.

SHA-256:
`23176fcdb06c775aa7cb1a9971b0e3b525f66c38a4b25cc330325ecb1fec113f`

## Repaired claims

The previous report correctly stated that the direct square-root Chebyshev
split only became useful far above `10^6`. The analytic gap is repaired here
by replacing that split with the dyadic integral estimate. No
Rosser--Schoenfeld import or finite table extension is needed.

## Rejected or still-open claims

- The k=5 determinant theorem does not make its proper-global determinant a
  fixed constant.
- The large-k local cofactor relations alone do not exclude a two-regular
  support. Their cofactors remain unbounded.
- The local large-owner congruences are CRT-compatible when separated from
  the exact global cofactor-product and small-prime-mass identities.
- The prime-counting theorem closes the analytic threshold interval but does
  not by itself prove `LargeKSmoothHypothesis`.

## Trust and verification

All public theorem axiom reports contain only:

- `propext`
- `Classical.choice`
- `Quot.sound`

The modules contain no `sorry`, `admit`, `native_decide`, or new axiom.
