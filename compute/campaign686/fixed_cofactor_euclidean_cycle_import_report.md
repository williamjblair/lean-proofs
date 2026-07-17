# Erdős 686 Fixed-Cofactor, Euclidean, and Cycle Import Report

Date: 2026-07-17

Status: three independent symbolic advances are kernel-checked. None is
reported as k=5 or large-k closure.

## Lean module hashes

- `Erdos686K5G12FixedCofactorWindow.lean`:
  `c54fad7895ea6c56c75811a43ab4575adb5b32731bb03a0d3fce4e9a994e1d73`.
- `Erdos686K5PrimitiveEuclideanConstraint.lean`:
  `48c15dff4f05a2417852b7cbb6fe81ae3961ac74b99056d39f7f41953d25b5b0`.
- `Erdos686RowDiagonalFourCycleTangent.lean`:
  `c0840302bd15fb7ebb501f8db048860957fa187fcc1be9955b383ae8ac780e61`.

## Accepted

- In the complete-support `G=12` branch, the remaining complement quotient
  `J` is coprime to three, divides twenty, and is one of
  `{1,2,4,5,10,20}`.
- The same branch satisfies the exact complement factorization and narrow
  window. Substituting the six possible cofactors gives
  `n+4 < 10*P^2*Q*A*B`.
- Primitive centered k=5 coordinates satisfy the exact quadratic power-gap
  identity. Euclidean division of `5*A3` by `A5` has quotient `g^2` and
  remainder `4*t`.
- The odd primitive convergent branch therefore passes a scale-free
  computable filter: its quotient is an odd square at least four, its
  remainder is positive and divisible by four, and the associated gcd lies
  in `{1,3,5,15,25,75}`.
- A genuine row-diagonal four-cycle has four independent upper-quotient
  additive equations. The normalized owner-square congruences force either
  a tangent-product bound or repeated-owner crowding in the diagonal
  product.

## Repaired

- The old fixed divisor `J | 23040` is sharpened by exact 2-adic and 3-adic
  arithmetic. In particular, eight never divides `J`; this is what permits
  the exact divisor `J | 20`.
- The primitive continued-fraction statement is no longer only a
  convergence reformulation. It now exposes an exact quotient/remainder
  test computable from each candidate convergent.
- The cycle theorem uses the four actual upper equations and direct tangent
  defects. It does not use the tautological complementary-product
  common-modulus lift.

## Rejected

- Comparing the controlled eight-owner product directly with the fixed
  cofactor. Those owners are already absorbed by the same three gap factors.
- Treating the Euclidean filter as an all-index exclusion. No effective
  theorem presently rules out the filter for every later convergent.
- Treating row/diagonal capacity alone as enough to exclude two-regular
  support. Exact abstract examples attain the exponent-two endpoint.

## Kernel-checked

- Five fixed-cofactor theorems, including the exact six-value classification
  and constant-ten owner bound.
- Seven primitive Euclidean theorems, including the solution-facing power
  window and scale-free convergent filter.
- Nine four-cycle theorems, including the exact additive system, direct
  owner tangent divisors, and repeated-owner crowding alternative.
- All printed theorem dependencies are subsets of
  `[propext, Classical.choice, Quot.sound]`.

## Certificate-backed

- No new external certificate is used by these three modules.
- The already banked exact matching-tail threshold certificate remains
  independently verified at minimal suffix `K0=18986`; its global use is
  still conditional on the missing weighted matching stability theorem.

## Still open

- Eliminate all six `J` values using an additional independent row/column
  equation, or close the other complete-support k=5 profiles.
- Prove an effective all-index theorem excluding the primitive Euclidean
  filter for convergents of `4^(1/5)`.
- Instantiate the four-cycle tangent theorem canonically, bound the nonzero
  tangent product, and cover all two-regular components.
- `OddThueTail1000Hypothesis`, `LargeKSmoothHypothesis`, and the final
  unconditional theorem.
