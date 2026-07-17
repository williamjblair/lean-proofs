# Erdős 686 Primitive-Split and Canonical-Cycle Import Report

Date: 2026-07-16

Status: four symbolic advances are kernel-checked. They narrow the live k=5
and large-k branches but do not close either branch.

## Lean module hashes

- `Erdos686K5G12PrimitiveComplementSplit.lean`:
  `d44cc666bfa404fb56023a4336993d6522d670bf726e9a9bd6044ff8d013c5cf`.
- `Erdos686K5G12EvenCofactor.lean`:
  `71ff1ca998f6fbe25d43dfde57972fde9087cc388fd03d1e1062eb72df8e6ebf`.
- `Erdos686K5PrimitiveRemainderSplitting.lean`:
  `d7e4bec34d9970fbfb2bf717c84001980453eb7aefce6592bec24860d9a1d730`.
- `Erdos686CanonicalLargeOwnerFourCycleTangent.lean`:
  `5519f9360090539032e65bbf4b44a273b35cdc79e9ac61045b8caa972d42d45a`.

## Accepted

- The exceptional complement sum and exterior gap quotient have gcd exactly
  two; their halves are coprime.
- Independent row-one and column-four equations force the remaining fixed
  cofactor to be exactly twice an odd integer. The six-value list is reduced
  to `J = 2` or `J = 10`.
- The primitive scale quotient is coprime to the reduced denominator. The
  nonlinear scale resultant therefore loses its variable `v^3` factor:
  `t | 60*(5-17*g^2*v^2)`.
- Every prime divisor of the normalized Euclidean remainder away from
  `2,3,5` makes `85` a square modulo that prime.
- The abstract normalized-square four-cycle tangent theorem is instantiated
  on an actual canonical large-owner four-cycle, with prime support,
  coefficient coprimality, row/diagonal factorizations, and quotient
  witnesses discharged.

## Repaired

- The interrupted canonical wrapper originally rewrote row-index equalities
  through owner-cell indices and failed type checking. The final proof
  rewrites only the full cast lower-term and diagonal-term expressions.
- The fixed-cofactor parity theorem now proves the exact two-adic valuation,
  not merely evenness.

## Rejected

- The reduced-resultant filter is not an all-index continued-fraction
  exclusion.
- Canonical four-cycle instantiation is not cycle coverage and does not bound
  the nonzero tangent product.
- Neither result closes k=5 or the large-k tail.

## Kernel-checked

- One primitive complement theorem.
- One two-value fixed-cofactor theorem.
- Five primitive remainder/resultant theorems.
- Ten canonical large-owner four-cycle theorems.
- Printed dependencies are subsets of
  `[propext, Classical.choice, Quot.sound]`.

## Certificate-backed

- No new external certificate is used by these modules.

## Still open

- Exclude `J=2` and `J=10` using another independent global equation.
- Prove an effective all-index exclusion for the strengthened primitive
  convergent filter.
- Bound the canonical tangent product and cover components without a
  four-cycle.
- `OddThueTail1000Hypothesis`, `LargeKSmoothHypothesis`, and the final
  unconditional theorem.
