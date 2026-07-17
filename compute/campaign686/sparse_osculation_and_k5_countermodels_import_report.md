# Erdős 686 Sparse Osculation and k=5 Nonlinear Import Report

Date: 2026-07-16

Status: symbolic checkpoint. The listed theorems are kernel-checked, but this
package does not close the k=5 tail or the dense large-k branch.

## Lean module hashes

- `Erdos686FullGridOneVectorOsculation.lean`:
  `8cfe42ae3182ce15ae0dfe6e6d4ce29975b3e57bc6b4e1eb58d45d7a48e9e0e0`.
- `Erdos686K5G12AntidiagonalUnitaryOverlap.lean`:
  `1183d6bdd076067dad572945f59a6093a6492d6edf65bf37a7816c3441435794`.
- `Erdos686K5ExceptionalFiveAdicCountermodel.lean`:
  `68eaa299cd7c512671b605f8de452f44e1c21178206ac5388c07b78df9bcf59a`.
- `Erdos686K5G12CenteredSumResultant.lean`:
  `84d92db57ddd7f98e3c192f27221636a71cb1166bf5c56d212894209e96492b4`.
- `Erdos686K5PrimitiveScaleResultant.lean`:
  `c2fc30cf53a1dbbfbcd81c4635bc5715d805ad82a190b9bd75eb255f9c3c50c5`.

## Accepted

- A `q` by `N` integer matrix with `q<N` has `N-q` rationally independent
  integral kernel vectors with coordinate bound `(N*H+1)^q` under an
  entrywise bound `H`. This is a separate large-radius theorem and does not
  alter the earlier finite-cube `N-2q+1` theorem.
- The degree `2k-1` complete-grid normalized osculation matrix has exactly
  `k` guaranteed independent bounded kernel polynomials.
- Under `4m<3k^2+k`, one such polynomial lies outside the degree-`k`
  equation-multiple subspace.
- The complete `k` by `k` grid is outside that sparse regime for every
  `k>=2`.
- In the G=12 profile, the antidiagonal quotient has unitary overlap bounded
  by `180`.
- The actual five-block equation gives
  `2*n+d+5 | 5*(d-3)^2*(d-1)*(d+1)*(d+3)`.
- After cancelling four forced G=12 owners, the remaining complement
  quotient `J` divides
  `5*((d-3)/P)^2*((d-1)/A)*((d+1)/Q)*((d+3)/B)`.
- Primitive centered k=5 coordinates satisfy the independent exact
  divisibilities
  `z | 4*t+300*v^3` and
  `t | 60*v^3*(5-17*z*v^2)`.
- Under `gcd(u,v)=1`, these imply `gcd(z,t)|300`, sharpened to `75` when
  `z` is odd.

## Repaired

- The stronger `N-q` family is attributed to its own large-radius
  affine-fiber argument. It is not described as the earlier bounded-cube
  family from the corrected osculation package.
- A low-degree kernel polynomial is not called arithmetically useful merely
  because it is nonzero. The candidate equation polynomial can be a common
  osculation factor, and every bounded multiple vanishes at the target
  solution.
- The common-component escape statement is restricted to sparse support and
  an explicit degree-bounded equation-multiple subspace.

## Rejected

- Reflection does not compress the complete owner grid into duplicate
  osculation rows. For odd `k` the coefficient data agree but the diagonal
  coordinate moves; for even `k` the directional coefficient also changes.
  A kernel-checked `k=3` counterexample rejects the proposed duplication.
- The G=12 linear aggregate is not a scale bound. An exact infinite CRT
  family satisfies all of the currently aggregated linear constraints.
- The G=24 five-adic cube lift is not a local contradiction. The noncrossing
  placement `(j,i,c)=(2,2,4)` has compatible full nine-cell owner-square CRT
  models modulo every power of five.

## Kernel-checked

- All fifty public theorems imported from the five modules above.
- Direct module builds and the repository axiom audit.
- No `sorry`, `admit`, `native_decide`, or new `axiom` occurs in the five
  modules.

## Certificate-backed

- The existing exact matching-tail verifier remains unchanged and reports
  threshold `K0=18986`.
- The corrected bounded-osculation and cancellation certificates remain
  unchanged and independently verified.

## Still unclaimed

- Any arithmetic consequence from an arbitrary full-grid degree `2k-1`
  kernel polynomial in the dense branch.
- A dense-support theorem escaping or exploiting the common equation
  component.
- A contradiction from the new G=12 degree-five quotient divisor.
- A bound on either primitive scale parameter from `gcd(z,t)|300`.
- k=5 closure, any remaining odd-tail closure, `LargeKSmoothHypothesis`, or
  the terminal theorem for Erdős 686.
