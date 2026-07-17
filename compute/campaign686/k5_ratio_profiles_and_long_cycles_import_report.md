# Erdős 686 k=5 Ratio/Profile and Large-k Long-Cycle Import Report

Date: 2026-07-16

Status: exact symbolic advances banked; no odd-tail or large-k closure is
claimed.

## Kernel-checked module hashes

- `Erdos686K5OppositeSecantTangentRatio.lean`:
  `cfada38809c67d8dd20683d5610cce9dacb952a85c5f47d1721bc4e6216983cf`
- `Erdos686K5OppositeSecantTangentBound.lean`:
  `82f0152915022bcd1df03838d4a5b6c23d0f77a2c33b15fa17256a4e10890e8a`
- `Erdos686K5SecantSquareCountermodel.lean`:
  `a5e3841f994b0db64972c96f0b0935bdee2283ea14c6fd9a9260982b1702a8e3`
- `Erdos686K5ResidualProfileDispatch.lean`:
  `366315a1cf2cf8ab375ebba106dd8000262a221b7c7a8b9e2fe0fa329e182bf9`
- `Erdos686K5G12PrimitiveQuotient.lean`:
  `e7ec027c3a675b9f1a4c1c45744aa5b5014335ef4de97f118a2a7ea78fb4803e`
- `Erdos686K5G12CharacteristicFive.lean`:
  `fc30c6e80274079bb302380cc9764dd33104c61bcffa655d39a995189f396ad3`
- `Erdos686RowDiagonalFourCycleObstruction.lean`:
  `09a1eda7a5f28e5c5857cccfe0aa1638b65e805bf51c23a14fe3fc683622c5ef`
- `Erdos686RowDiagonalSixCycle.lean`:
  `47a598067a56891fd5046b668f58a4513d2238bbbcfdbd7848817d70a0ca443d`
- `Erdos686K5ExceptionalProfileClassification.lean`:
  `f6a328ec2e965a2146d106b8c7dd2678005fceb54ee02b9954393634d169117a`
- `Erdos686K5G12DiagonalOwners.lean`:
  `d00c68ab7e50c2271a82d3d21e4478c2ab66f7c4a92d1d4779a03fca96ecd660`
- `Erdos686K5G12ResidualWeightedGap.lean`:
  `cd976f62603ae151e5174b5e4bbc9665b853dbdee2abe0cdb2de8313a996cc32`
- `Erdos686K5G12DiagonalMatchingTangent.lean`:
  `850f3bac20dc6ab494664d32539e9fc40ab9b404d16f81c7929d501f8c6e61bc`
- `Erdos686CanonicalLargeOwnerSixCycle.lean`:
  `648f0d23c4e0498acb2026ee208d2aa27d8c088d32181eafbdace2af74a14c12`
- `Erdos686CanonicalAlternatingComponents.lean`:
  `8ec462b744503124330e1c084ad0a214b2464fba9e679f099b88d577c5f3cdf8`
- `Erdos686RowDiagonalCyclicSecant.lean`:
  `b18a7725a0bf36c9da1f31c25bc31490efb198d1354004fb994ed8b0282e636d`
- `Erdos686CanonicalLargeOwnerCyclicSecant.lean`:
  `5c5efa6a650f6c6ead56c3f2e0c91f1636b1feba4fc9d0a1c122625f4be227ee`
- `Erdos686CanonicalGlobalCyclicSecant.lean`:
  `3b1c07b7867f422748b9be1d3f42294728eaf9eeb5f3f83c8ecf512be4feef35`

## Accepted

- The k=5 equation itself supplies `40*d<13*n` for `n>=662`.
- After exact removal of the distinguished factor four, an ordinary-kernel
  finite proof covers all 400 ordered row/column pairs. Restoring the five
  distinguished positions proves the actual tangent coefficient nonzero in
  all 2,000 solution-facing configurations for `n>=2811`, `d>=5`.
- Composing nonvanishing with the opposite-secant determinant theorem removes
  its zero branch and gives the exact gcd divisor and height bound.
- The residual-profile dispatch is exhaustive. It produces either a proper
  nonzero-tangent 2x2 grid outside the exceptional G=12 profile, that exact
  G=12 profile, or a G=24 one-unit residual profile on at least one side.
- In the G=12 primitive quotient, exact adjacent equations and an independent
  tangent congruence prove `gcd(Q,K)|5`.
- If the characteristic-five branch has `5|Q` and `5|K`, then `25` does not
  divide `K`; its 5-adic valuation is exactly one.
- A row/signed-diagonal C6 has an exact cyclic secant product. Its nonzero
  branch bounds the square of one alternating owner mass, while a zero local
  quotient forces a middle owner square and both neighbours into two
  diagonal cofactors.
- Every G=24 simultaneous exceptional class now has a complete five-owner
  primitive row system. All five owner squares divide explicit designated
  targets, the full row square divides their product, and exact remainder
  tables forbid cross-allocation for owners coprime to six.
- In the G=12 branch, two anti-diagonal owners divide the primitive quotient
  K, ten distinct cells are covered by K and three normalized shifted gaps,
  and the five uncovered diagonal owners form an almost-unitary divisor M of
  d with `gcd(M,d/M)|432`.
- The row/diagonal C6 theorem is instantiated on actual canonical owners.
  More generally, every raw degree-two canonical support produces an
  alternating component, and an arbitrary finite cyclic secant theorem
  handles C8 and all longer components.
- On the whole degree-two support, the canonical partner permutation yields
  one global theorem: either the square of the complete large-owner mass is
  bounded by the global cyclic secant product, or an actual component forces
  an enlarged owner-square crowding divisor into two shifted-diagonal terms.

## Repaired

- The broad cone-only tangent nonvanishing claim is false. The compiled proof
  uses the sharper equation-derived cone `40*d<13*n` and the exact threshold
  `n>=2811`.
- The intended binary residual dispatch must include the still-live G=24
  one-unit profile unless that branch is independently excluded.
- The relevant G=12 local coefficient is `160`, not `56`; it leaves a real
  characteristic-five branch.

## Rejected

- No crossing owner is universally forced back into the product of the two
  secant quotients by the four local square defects and the ratio cone alone.
  A kernel-checked witness has owners `5,7,11,13`, exact row/column and secant
  factorizations, all four square defects, and quotient-product gcd `1`.
- Two-regular row/signed-diagonal diffuseness gives no positive four-cycle
  packing. The explicit all-k long-cycle support has degree two at every row
  and used offset but contains no four-cycle.
- Neither `gcd(Q,K)|5` nor exact `v5(K)=1` is a contradiction.
- The global cyclic secant height still has n-degree `2k`, while the available
  mass lower bound after small-prime loss has n-degree
  `2k-2*pi(k)`. The theorem `8*pi(k)<k` does not repair that exponent loss.
- Exact G=24 remainder tables prevent cross-allocation but allow every owner
  square to remain on its own designated target.

## Still unclaimed

- Elimination of the G=24 one-unit residual branch.
- A second relation closing either branch of the G=12 primitive quotient.
- A global cover/decomposition that applies the C6 or longer-cycle arithmetic
  with an additional `n^(-2*pi(k))` saving, fewer effective secants, or a
  global signed-diagonal cofactor mass identity.
- `OddThueTail1000Hypothesis`, `LargeKSmoothHypothesis`, or the final
  unconditional theorem.
