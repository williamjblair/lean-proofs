# Erdős 686 two-regular and four-crossing import report

Date: 2026-07-16

## Accepted large-k claims

Lean module:
`ErdosProblems/Erdos686LargeOwnerTwoRegularArithmetic.lean`

The exact upper-column analogue of the lower-row cofactor factorization is
now kernel-checked. When the four-removed upper block equals the lower block,
the product of all column cofactors is exactly the same `k`-small-prime mass.

In the row-and-column degree-two regime Lean proves:

- the support-weighted row cofactor product is `smallPart^2`;
- the support-weighted column cofactor product is `smallPart^2`;
- their joint product is `smallPart^4`;
- the product of all row-partner owner products is the full large mass `M`;
- `M <= collisionDefect`;
- `M^2 <= collisionProduct`.

SHA-256:
`d113e0c1d599a3d682262526367d1e327fb1710998537789ac583aaa261a73da`

## Large-k sharpness verdict

The new collision inequality has the wrong direction for a diffuse-support
contradiction and is sharp. Pairwise-coprime two-regular grid
configurations can attain `collisionDefect=M`, and fully row/column/diagonal
two-regular configurations can approach that endpoint arbitrarily closely.
Thus exact small-prime cofactor bookkeeping does not repair the
capacity-only exponent loss. A cycle-level additive or tangent resultant
using the common `n,d` equations is required.

## Accepted k=5 claims

Lean module:
`ErdosProblems/Erdos686K5FourCrossingSecantGCD.lean`

Accepted interfaces:

- `k5_proper_global_four_crossing_secant_gcds_dvd_coefficients`
- `k5_proper_global_crossing_product_secant_gcd_dvd_coefficient_product`

At every vertex of a fully owned proper-global crossing grid, the common
part of the owner and the two opposite-secant quotients divides a coefficient
depending only on the four indices. Pairwise coprimality combines the four
local statements into one crossing-product gcd divisor. No quotient is
inverted, so all zero cases remain exact.

SHA-256:
`0d85f0e28655cbdb7c41cce3844f9c8551ff6390970ba9ea06894e6288cb1d68`

## k=5 rejected inference

The fixed coefficient is an upper bound on a gcd, not a lower bound, and it
can vanish. Residual-profile divisibility alone does not guarantee a
nonzero fully owned choice. An exact counterprofile is:

- `G=12`;
- lower residual vector `(2,1,2,1,3)`;
- modified upper residual vector `(1,2,1,2,3)`;
- residues `n=1 mod 24`, `d=3 mod 24`, `t=4`.

The only unit rows are `{2,4}` and the only unit columns are `{1,3}`. The
corresponding four local factors are `[-96,-56,-40,0]`. Therefore a
universal nonzero-pair selector cannot be proved from `G|24` and the existing
residual divisibility statements alone.

The separate proper-global determinant is also not nonzero on the full cone
`5<=d<n`: exact zeros occur at `(n,d)=(2996,989)` and `(1120,369)` for
valid index choices and the required mod-four condition. The live repair is
to use the sharper solution ratio before any nonvanishing claim.

## Trust surface

All public theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The modules contain no `sorry`,
`admit`, `native_decide`, or new axiom.
