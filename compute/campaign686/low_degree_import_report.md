# Erdős 686 Low-Degree Osculation Import Report

Date: 2026-07-16

Status: symbolic package audited and banked. The corrected matrix, full
bounded independent family, Taylor square divisor, cancellation bridge,
algebraic specialization split, repaired barycentric degree/root interfaces,
and residual divisor are kernel-checked. The effective intersection bound,
the final `v!=0` root rearrangement, and the canonical full-large-part
specialization remain explicitly unclaimed; no support enumeration has
started.

## Source

`/Users/williamblair/.codex/attachments/c0052e31-0a62-413c-b9c1-9d6a9c63e841/pasted-text.txt`

SHA-256:

`4768a8cc552cbed96c23fe83be6a5fc87b83a04777809e94feaef3df41f2388d`

## Lean module hashes

- `Erdos686LowDegreeOsculation.lean`:
  `2e857af4b1ce631dc0d9823250359bf57281ac23da87b751e9de17b772f52413`.
- `Erdos686OsculationKernel.lean`:
  `af380ecc1f13689b94a9906fdf3500644fbff1fce1daf3745fd203f980db306a`.
- `Erdos686OsculationTaylor.lean`:
  `b12b456e47d6c44058fbdc8ad3a2b84d285015ac018afed2165f2f3add01cc4e`.
- `Erdos686OsculationDichotomy.lean`:
  `f8a44bb2fb5cb7b29406d7a9f2ea0ccf306338a1a0f5e867bc11c639bb6c5b64`.
- `Erdos686BarycentricMatching.lean`:
  `0134d565c5f707a73b14b574c79d3a0bad64565b65e0e5dc67150c7671789e0a`.
- `Erdos686ResidualDivisor.lean`:
  `5079e23a995cc660d68b916ec06a0360a9a2d734cfe43f3efbec90f3c56c41d9`.

## Phase gate

### Imported unchanged

- `N_r = binom(r+2,2)`.
- The monomial family consists of all `X^a Y^b` with `a+b <= r`.
- There is one value constraint and one normalized directional-derivative
  constraint at each support point.
- The cancellation integer inequality is numerically valid for every
  `44 <= k <= 224`, `2 <= m <= k`, and admits an exact symbolic tail from
  `k >= 225`.

### Repaired

- The osculation matrix has `2m` rows, not `4m` rows. The guaranteed bounded
  independent family has size `N_r-4m+1` because the cube/fiber proof applied
  to `q=2m` rows yields `N_r-2q+1`.
- The finite-cube proof must be separated from the arithmetic matrix. For a
  row `l1` bound `L`, a radius `D` satisfying
  `(D+1)^2 > D*L+1` yields the claimed independent family. The advertised
  radius `12*N_r*r*2^k*k^(r-1)` is safe but conservative.
- `(c+v)^k-4v^k` is the coefficient at degree `m*k`, not the polynomial's
  `leadingCoeff` in the vanishing branch.
- Cancellation requires `M` to contain the full `>k` lower-block part, or an
  explicit mass lower bound of equal strength. It is not valid for an
  arbitrary matching subset product.

### Rejected

- The bounded-family conclusion for an arbitrary `4m × N_r` integer matrix.
  The matrix `[I_(4m) 0]` has nullity only `N_r-4m`, so it cannot contain
  `N_r-4m+1` independent kernel vectors.
- Calling `(c+v)^k-4v^k` the actual leading coefficient when it vanishes.

### Kernel-checked

- `OsculationMonomial.totalDegree_le`.
- `osculationMonomialBasis_card`.
- `osculationDegree_spec` and `osculationDegree_minimal`.
- `osculation_value_row_dotProduct`.
- `osculation_direction_row_dotProduct`.
- The exact matrix interface has `2m` rows: one value row and one normalized
  directional-derivative row per support point.
- The translated finite-cube image is encoded into exactly
  `(D*L+1)^q` boxes.
- Equality of finite-cube image codes is equivalent to equality of matrix
  images.
- The strict cardinal inequality constructs a nonzero integer kernel vector
  with coordinatewise absolute value at most `D`.
- The corrected hypotheses `0<q`, `2q<N`, and
  `D*L+1 < (D+1)^2` imply that strict cardinal inequality.
- Restriction to a coordinate set of size `t`, when injective on a finite
  cube subset, bounds that subset by `(D+1)^t`.
- Every rational coordinate subspace has exactly `finrank` pivot coordinates
  on which restriction is injective.
- Consequently, a finite affine fiber whose difference space has rank `t`
  contains at most `(D+1)^t` cube points.
- The generic finite-cube theorem extracts
  `N-2q+1` rationally independent bounded integer kernel vectors from a
  `q × N` matrix.
- Its exact `q=2m` specialization produces the required
  `N-4m+1` independent family for the corrected osculation matrix.
- `osculationMonomialDX_natAbs_le` and
  `osculationMonomialDY_natAbs_le`.
- `osculationMonomialValue_natAbs_le`.
- `osculationDirectionEntry_natAbs_le` and
  `osculationValueEntry_natAbs_le`, giving the exact
  `3*r*2^k*k^(r-1)` entry envelope from the reduced-binomial coefficient
  bounds.
- The entrywise envelope feeds the finite-cube theorem and gives the exact
  advertised coefficient radius
  `12*N_r*r*2^k*k^(r-1)`.
- Exact univariate and bivariate first-order Taylor congruences modulo
  `P^2`.
- The local owner theorem uses the audited displacement
  `(-n-j,-d-rho)` and cancels the reduced-binomial coefficient modulo the
  composite `P^2` only through explicit coprimality.
- Pairwise coprimality then proves
  `(product_e P_e)^2 | F(-n,-d)`.
- The exact cancellation bridge proves `F(-n,-d)=0` whenever the certified
  upper bound is strictly below `M^2`.
- A primitive integral common-factor presentation now gives the exact
  specialization split: the common factor vanishes, or both residual
  quotients vanish.
- If the common factor is a unit, only the quotient-pair branch remains.
- Rational quotient factor-coprimality is formalized without incorrectly
  strengthening it to multivariate comaximality.
- The barycentric node-value identities and denominator-cleared derivative
  system.
- The coefficient of degree `k*|S|` in `Phi_S` is exactly
  `(c+v)^k-4v^k`; this coefficient vanishes over `Z`, for `k>=3`, exactly
  when `c=v=0`.
- Assuming the already required `W_S^2` factorization, the quotient has
  degree exactly `|S|(k-2)` in the nonzero branch and at most
  `|S|(k-2)-k` in the zero branch (`k>=4`).
- The root identity
  `c=sum_j w_j(d+rho_j)/(n+j)` is kernel-checked over `Q`.
- Every support fraction has the strict
  `(2k-1)/(n+1)` deviation envelope, yielding the weighted root bound.
- In the `v=0,c!=0` branch Lean proves
  `n+1 < (2k-1)*sum|w_j|/|c|`.
- The exact nonzero-branch identity
  `Lambda*(U(-n)+dV(-n))=(-1)^m*M*S_S`.
- From the unscaled global square divisor and `M!=0`, Lean proves `M|S_S`
  without requiring coprimality between `Lambda` and `M`.
- The row-cofactor smoothness statement is explicitly conditional on each
  selected owner containing the entire `>k` part with multiplicity.
- The exact residual height bound is
  `|S_S| <= (|gamma|+sum|omega_j|)*B^m`.

### Externally certified

- Independent exact audits found all 24,073 comparisons in
  `44 <= k <= 224`, `2 <= m <= k` pass.
- The exact optimal uniform threshold is `k=44`; `k=40` and `k=42` are
  isolated all-`m` successes below it.
- `cancellation_threshold_certificate.json`:
  `f50149fea6f62f43b4df3fbd9632bc2bfa84b8c5d90bef627b7cadee0af18a2a`.
- `verify_cancellation_threshold.py`:
  `7899faf9e37ffe293b62f14377f02151b7130e6d2d25eacc1b48453f4ef61e7c`.
- `osculation_kernel_certificate.json`:
  `d309ddcd8f747dfceb6a506851ce1647e7aad478016f32f1921e85443d3f269e`.
- `verify_osculation_kernel.py`:
  `169e5356ee9296364d3d9e050e4e7b0106100b20ce2e15f5f26bd0c84a48c379`.
- Both verifiers use exact integer arithmetic only and pass independently.

### Still unclaimed

- The arithmetic specialization of the cancellation theorem still requires
  the explicit hypothesis that `M` contains the full `>k` lower-block part;
  it is not claimed for an arbitrary matching product.
- The effective Bézout/intersection theorem needed to bound the coprime
  quotient-pair branch by `r_m^2` complex intersections. The current
  kernel theorem deliberately calls this the quotient-pair branch, not
  “zero-dimensional,” until that result is imported.
- The explicit `v!=0` negative-root bound in terms of `mu=c/v` and
  `kappa=sum|w_j|/|v|`; its common deviation estimate is banked, but the
  final rearrangement was not retained without a completed kernel proof.
- A proof from the canonical matching construction that every selected
  owner in the intended support actually contains the entire `>k` part of
  its row. Smoothness is not inferred from a partial owner.
- Any support-by-support enumeration.
