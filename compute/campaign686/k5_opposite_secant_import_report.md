# Erdős 686 k=5 Opposite-Secant Cofactor Import Report

Date: 2026-07-16

Status: symbolic relation banked; k=5 remains open.

## Accepted

- The two opposite secant forms multiply to the difference of the row and
  column quadratic products.
- Each opposite product of two canonical crossing owners divides its signed
  secant, with composite-modulus coprimality stated explicitly.
- For two fully owned rows and two fully owned modified columns, the exact
  four-crossing gcd produces coprime natural cofactors `a,b`.
- The corresponding integral secant quotients satisfy
  `Uplus*Uminus=r^2*mu1*mu2*b-s^2*a`.

## Repaired

- The quotient identity is stated only after the common crossing product is
  proved nonzero and both opposite secant divisibilities have supplied
  integral quotients.
- The upper quadratic product carries the two exact distinguished-column
  multipliers; no implicit division by four is used.

## Rejected

- No claim is made that the cofactor identity alone bounds `n`, `d`, or the
  cofactors.
- No tangent-product resultant is reused: that eliminant is already
  kernel-checked to be a structural syzygy.
- No claim is made that the proper-global or complete k=5 tail is closed.

## Kernel-checked interfaces

- `opposite_secant_product_identity`
- `opposite_secant_quotient_cofactor_identity`
- `canonicalOwner_k5_opposite_crossing_products_dvd_secants`
- `k5_fullyOwned_opposite_secant_cofactor_identity`

All four audited headlines depend only on the allowed logical axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Module hash

- `Erdos686K5OppositeSecantCofactor.lean`:
  `68d2feb4d09e574acc09c1838691514c06bd71755d0f413ac639097ca41743b7`.

## Still open

- Bound or classify the integral solutions of the opposite-secant cofactor
  identity under the exact residual profiles and shifted-diagonal owner
  divisibilities.
- Treat zero or exceptionally small secant quotients without dividing by
  them.
- Combine the new relation with the tangent-defect system to close the
  proper-global residual profile.
- Close the exceptional profile and hence the full k=5 tail.
