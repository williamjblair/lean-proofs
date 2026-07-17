# Erdős 686 full-mass and exceptional-global import report

Date: 2026-07-16

This checkpoint audits six ordinary-kernel Lean modules. It does not close the
`k=5` tail or the large-`k` hypothesis.

## Accepted

- Exact composite-modulus normalization:
  `P^2 / gcd(P^2,q) | F` follows from `P^2 | qF`.
- Pairwise-coprime owner normalization losses combine into one common bound,
  rather than one bound per support cell.
- The complete canonical grid square divides `((k-1)!)^3` times one common
  osculation evaluation.
- An explicit bounded independent family gives the corrected lower dimension
  `N_r-4m+1`.
- A bounded fixed-divisor degree budget follows when a separate
  quotient-space dimension upper bound is supplied.
- The G=12 owner cells split exactly into uncovered, diagonal, and controlled
  parts, yielding a cofactor-free nine-gap-window divisor.
- The signed nine-gap window has an exact polynomial division identity modulo
  the original centered quintic equation.
- The G=24 primitive coordinates give exact global cubic quotient identities
  and a valid characteristic-five cube lift.
- The two exceptional five-owner placement tables are exact.

## Repaired

- The owner normalization loss is a single common multiplicative loss. The
  rejected projected estimate with an `n^(2*pi(k))` factor is not used.
- The bounded osculation matrix has two conditions per support cell. The
  `N_r-4m+1` count comes from the bounded cube/fiber argument, not from
  pretending the matrix has four rows per cell.
- The bounded fixed-divisor theorem is conditional on an explicit
  quotient-space upper bound. No full-jet-space bound is silently transferred
  to the bounded space.
- The G=12 aggregate divisor is identified as a consequence of a
  profile-independent polynomial identity, rather than as a new independent
  modular restriction.

## Rejected

- A gcd or common factor of selected osculation polynomials does not
  automatically inherit every support value and tangent jet.
- The total-degree coefficient `(c+v)^k-4v^k` is not automatically the actual
  leading coefficient in a degree-drop branch.
- Coprime residual polynomials plus abstract Bézout finiteness do not provide
  an effective integral enumeration without a concrete resultant certificate.
- From a divisor of an additive difference `A | 5B-h`, one cannot cancel
  `gcd(A,5B)` to infer `A/gcd(A,5B) | h`.
- The aggregate G=12 nine-gap divisor is not treated as a second global
  equation: the original k=5 product equation already implies it.
- Modulo 625 does not exclude any G=24 five-owner placement.

## Kernel-checked interfaces

- `ErdosProblems/Erdos686FullMassNormalization.lean`
- `ErdosProblems/Erdos686BoundedOsculationDegree.lean`
- `ErdosProblems/Erdos686K5G12UncoveredAllocation.lean`
- `ErdosProblems/Erdos686K5WindowDivisorCancellation.lean`
- `ErdosProblems/Erdos686K5ExceptionalEquationFacing.lean`
- `ErdosProblems/Erdos686K5ExceptionalFivePlacement.lean`

## Source hashes

```text
dedce9cf74c9fdeafc14968065c7dabc0d40510b2a90832beac7930587c7dc27  ErdosProblems/Erdos686FullMassNormalization.lean
59d55efae2887fdf99007a2b66e4a2275c344d14283512fa06d442a82a68faec  ErdosProblems/Erdos686BoundedOsculationDegree.lean
d81787b8ad12a9f9835992b4c5cc9ab94417037754fb2bbbae6a59a852c82258  ErdosProblems/Erdos686K5G12UncoveredAllocation.lean
390da7e7132a3e75fb53b556a61905997e609c08e7cebb897554e803e14444c7  ErdosProblems/Erdos686K5WindowDivisorCancellation.lean
4921cdb6a570ec57648f2e477057cdc07f197364ea2b621d7cc9d34ca4e849b6  ErdosProblems/Erdos686K5ExceptionalEquationFacing.lean
4987ebce11fed9b834d620252ea77c5ee965066a1aa367fae217790ef59a2522  ErdosProblems/Erdos686K5ExceptionalFivePlacement.lean
```

## Certificate-backed

- The exact G=24 residue tables are proved by ordinary Lean reduction in the
  theorem modules.
- The repository hostile matching-tail verifier remains an independent exact
  arithmetic gate and is rerun at checkpoint time.

## Still unclaimed

- A support-sparsity or fixed-divisor theorem strong enough to bring the
  large-`k` effective degree below the available evaluation-size bound.
- An owner-level G=12 relation independent of the profile-free nine-gap
  identity.
- A G=24 contradiction combining the cube lift with simultaneous row and
  column equations.
- Completion of the genus-two rational points, all remaining odd tails, the
  large-`k` hypothesis, and the unconditional terminal theorem.
