# Erdős 686 Primitive Convergent and Dense-Jet Import Report

Date: 2026-07-16

Status: kernel-checked symbolic checkpoint. It sharpens the k=5 tail and
identifies an exact dense large-k no-go, but it does not close either branch.

## Module hashes

- `Erdos686K5PrimitiveApproximation.lean`:
  `cfb7b0640447805d4f72ddf5275537d57b10d53863e6bceddf5b86d27b9bbaf2`.
- `Erdos686K5G12ResultantGCDClosure.lean`:
  `f3223343bc2f883e710a3e1bb37dcfe05d64f741e66277b7ff6fd37c2ebcc4ce`.
- `Erdos686DenseCommonComponentNoGo.lean`:
  `8bcc76a826d220fa5f7860755b44586f4ff58c91b38468a6d3c324e58435e139`.

## Accepted

- Removing a centered common scale `g` improves the approximation constant
  by exactly `g^2`.
- For `g>=2`, a coprime primitive k=5 ratio lies in the strict Legendre
  regime and is an actual continued-fraction convergent of `4^(1/5)`.
- On the odd-scale branch,
  `gcd(g^2,t)` is one of `1,3,5,15,25,75`.
- In the G=12 complete-support tail, the remaining complement quotient `J`
  has gcd bounds `2,24,2,24` against the four normalized factors of the
  centered resultant and consequently satisfies `J|23040`.
- The actual rational polynomial
  `E(X,Y)=4*prod_h(X-h)-prod_h(X+Y-h)` has the advertised value and partial
  derivative formulas at every complete-grid cell.
- Every multiple `E*P` satisfies all first-order value and normalized tangent
  jets for arbitrary `P`. Under the block equation it also vanishes at the
  target `(-n,-d)`.

## Repaired

- The dense common-component warning is no longer only dimensional or based
  on closed-form surrogate derivatives. The module connects the exact
  `MvPolynomial.pderiv` evaluations to the local formulas.
- The G=12 fixed bound is stated only for `J`. It is not transferred to the
  eight controlled owners.

## Rejected

- The conclusion `J|23040` does not close G=12 by comparing eight nonunit
  owners with `23040`. The banked allocation states
  `E8 | J*((d+1)/2)*(d-1)*((d+3)/2)`; those owners are already absorbed by
  the three gap factors, so `E8` need not divide `J`.
- Full-grid first-order jets, even combined with target base-locus vanishing,
  cannot force a nontrivial divisor of the cofactor. Taking `P=1` is an exact
  kernel-checked countermodel.
- Convergent status is not an all-index exclusion theorem. The existing
  finite Farey certificate does not rule out every later convergent.

## Kernel-checked

- All twenty-four public theorems imported from the three modules.
- Direct and focused Lean builds.
- No `sorry`, `admit`, `native_decide`, or new `axiom` occurs in these
  modules.

## External exact diagnostics

- The public Magma V2.29-8 calculator exposes the required elliptic-Chabauty
  intrinsic, but both cover-one `RankBounds` and
  `PseudoMordellWeilGroup` computations exceeded its 60-second limit.
- PARI `nfsubfields` found no nontrivial subfield of the degree-15 pair
  field. These diagnostics are not Lean theorems and are not used by any
  accepted claim.

## Still unclaimed

- An all-index exclusion for convergents satisfying the six overlap cases.
- A terminal contradiction from `J|23040`.
- Any independent dense-grid global equation or transverse higher-jet
  divisor.
- k=5 closure, any remaining odd-tail closure, the large-k closure, or the
  terminal Erdős 686 theorem.
