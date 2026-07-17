# Erdős 686 Cycle and Zero-Secant Import Report

Date: 2026-07-16

Status: symbolic arithmetic banked; neither the k=5 tail nor the large-k
branch is claimed closed.

## Kernel-checked modules

- `Erdos686K5ZeroSecantGCDLower.lean`
  (`6689286abafd448b5d8f691cd808bee00d590c2d3be4ccb99d69ded49fef1eb6`)
- `Erdos686K5G12SecantComplement.lean`
  (`8afe8c36d0df85756578954ad769966a11567e0e99c1a4b31fd5140d6701c850`)
- `Erdos686TwoRegularCycleMonodromy.lean`
  (`49239965dd06a3a7e18ca4fd9f416a59a7043c03a63c1aaa2ee41850936b64be`)
- `Erdos686RowDiagonalFourCycle.lean`
  (`e12299dbcff032b9ad2ec58c697af1954d473fa9ac567d857cc33a1fecfc779f`)

## Accepted

- In the exceptional `G=12` k=5 residual profile, the zero tangent
  coefficient does not destroy the argument. Exact square cancellation and
  the residual congruences force the complete crossing owner into the
  minus-secant quotient.
- The same profile makes that owner coprime to `24`, so no coefficient part
  remains after cancellation.
- For the exact row and column complements `R,C`, the crossing product `P*Q`
  divides `R+C`, is coprime to `R*C`, and satisfies
  `R<C`, `2*C<3*R`, `2*(P*Q)<5*R`, and `15<=P*Q`.
- A genuine common-modulus cyclic transfer has the expected monodromy
  resultant and a nonzero absolute-value lower branch.
- A row/signed-diagonal four-cycle has a non-tautological secant
  factorization. In its zero branch, the two opposite owner squares enter
  the diagonal cofactors, yielding the exact crowding divisor
  `ownerMass*(crossProduct)^2 | y1*y2`.

## Repaired

- A zero k=5 fixed coefficient is treated by exact coefficient-gcd
  cancellation and the residual profile, not by selecting a supposedly
  universal nonzero coefficient.
- Cycle monodromy is split into a true common-modulus theorem and the actual
  varying-owner specialization.

## Rejected

- Complementary-product lifting of each local owner congruence to the total
  owner modulus is not a large-k resultant. For every cycle with at least two
  pairwise-coprime owners, the lifted coefficient is already divisible by
  the total modulus before the arithmetic equations are used.
- The new k=5 S-unit-style relation is not itself a contradiction.
- The four-cycle crowding divisor is not yet a global stability theorem.

## Still unclaimed

- A second independent relation that eliminates the exceptional k=5
  `P*Q | R+C` branch.
- A decomposition showing that the nonzero four-cycle bounds or zero-cycle
  crowding bounds cover enough of every diffuse canonical support.
- `OddThueTail1000Hypothesis`, `LargeKSmoothHypothesis`, or the final
  unconditional Erdős 686 theorem.
