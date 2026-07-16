# Erdős 686: audit of the 2026-07-16 GPT Pro handoff

Date: 2026-07-16

Status: the main structural updates are valid and kernel-banked.  The full
canonical owner matrix is now formalized and audited; the terminal
odd-support and large-k contradictions remain open.

## Normalized local jets

The exact identity is correct. If

```text
n+j       = A*R,
n+d+i     = A*C,
B_k(n+d)  = 4*B_k(n),
```

then cancelling `A` gives

```text
C*Q_i(n+d+i) = 4*R*Q_j(n+j),
```

where `Q_h(Z)=product_{r!=h}(Z+r-h)`. Its rational ratio form is a lower
local quotient divided by an upper local quotient. Therefore a formal
owner-adic logarithmic expansion is a row term minus a column term at every
order.

This closes normalized cell-local higher-jet rectangle and minor searches.
It does not apply to the global punctured-grid interpolation certificates,
which combine simultaneous vanishing conditions in one global polynomial
space.

Lean modules:

- `Erdos686NormalizedJetCoboundary.lean`
- theorem `owner_shiftedLocalQuotient_coboundary`
- theorem `owner_shiftedLocalQuotient_ratio`

## Canonical owner cleaning

The required one-block valuation theorem was already present as
`exists_blockProduct_factorization_concentration`.

The handoff's `p=2` allocation is valid as stated. If `S` is the lower total
valuation, the upper total is `S+2`, and `F` is the selected original upper
maximum, then

```text
S-(F-2) = (S+2)-F.
```

Thus matching against `F-2` uses exactly the original upper omitted-valuation
bound. A modified upper maximum need not be reselected. The exact arithmetic
is now banked in `Erdos686CanonicalOwnerCleaning.lean`.

Lean also proves:

- every length-`k>=4` upper block contains a term divisible by four;
- dividing one such term by four changes the quotient-four equation into
  equality of two ordinary products.

That remaining construction is now complete in
`Erdos686CanonicalOwnerMatrix.lean`.  The theorem
`exists_canonicalOwnerSystem` chooses the distinguished column and proves
simultaneously:

```text
G | (k-1)!,
product_j r_j = product_i s_i = G,
n+j = r_j * product_i A_ji,
n+d+i = c_i*s_i*product_j A_ji,
c_t=4 and c_i=1 for i!=t,
A_ji | d+i-j,
G * product_{j,i} A_ji = B(k,n),
```

with distinct cells pairwise coprime.  The focused build, 807-theorem
manifest, repository-wide axiom audit, and attestation regeneration all
pass.  The theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

## High-prime and small-prime mass

The following results are now kernel-banked in
`Erdos686CanonicalOwnerMass.lean`:

```text
B_{<=k}(k,n) <= (k-1)! * (n+k)^pi(k),
```

with `pi(k)` represented exactly by `(k+1).primesBelow.card`;

```text
B(k,n) = B_{<=k}(k,n) * B_{>k}(k,n);
```

and the cross-multiplied high-prime lower bound

```text
B(k,n) <= (k-1)! * (n+k)^pi(k) * B_{>k}(k,n).
```

For each prime `p>k` occurring in the lower block, Lean also constructs one
unique lower-upper owner cell carrying the entire lower-block `p` exponent
on both sides.

## Numerical correction

The handoff's `k=5` statement that the worst basis norm has 187 digits is
stale. The current saturated-and-LLL-reduced all-puncture audit gives a
70-digit worst norm, after exact local denominator clearing. All 175
denominator multipliers are one, and the exact height inequality retains
882 decimal orders.

## Live frontier after integration

- All 25 `k=5` punctures are ordinary-kernel banked. The aggregate theorem
  `no_k5_tail_solution_of_proper_support` proves that any target-size
  hypothetical solution has complete canonical owner support. The hostile
  verifier, full repository build, manifest audit, axiom gate, and
  attestation regeneration pass.
- Global puncture certification remains active for `k=7,9,11,13,15`.
- Complete odd support must use simultaneous adjacent row and column unit
  equations, not normalized local jets.
- Large `k` now has its concentration, full canonical matrix, high-prime
  uniqueness, and mass estimates.  The near-permutation/diffuse
  mass-structure dichotomy and its arithmetic elimination remain open.

## Direct k=5 genus-two lane

The new handoff identifies the genus-two quotient

```text
y^2 = 9x^6 + 64x^5 - 200x^3 + 64x + 144
```

as a separate target-strength route. Existing repository work banks the
exact quotient identity and the inverse-map exceptional-point audit.

The proposed 2-Selmer dimension four is false. The frozen exact Magma
certificate gives

```text
Sel^(2)(J/Q) = (Z/2Z)^5,
J(Q)_tors = 0,
J(Q) = Z^5,
proved = true,
rank_bound = 5.
```

The five supplied point differences have determinant `-1` in the proved
Magma basis, so they form a basis of the full Mordell-Weil group. Rank,
finite-index generation, and saturation are completely resolved.

The two-cover frontier is also frozen and independently verified.
`TwoCoverDescent` gives eight locally soluble classes. The pair-sum
resultant has an irreducible degree-15 factor of multiplicity two; over its
number field the sextic factors in degrees `2+4`, and all eight elliptic
quartic covers are constructed with known points. The 34 known affine points
occupy the eight classes with sorted counts `[2,4,4,4,4,4,6,6]`.

`RationalPointsGenus2` still reports `proved_all=false`. The sole remaining
`k=5` arithmetic-geometry obligation is therefore an exhaustive analysis of
the eight elliptic covers or a high-rank Mordell-Weil sieve proving that the
36 known projective points exhaust `C(Q)`. A bounded point search is not
treated as completeness.

The custom high-rank sieve now has fourteen exact packets. All 36 known
projective vectors are certified in the fixed reduced-model basis and survive
every packet. The combined HNF lattice has index
`42343330413030424784735169272832000000`; exact primary-component
contraction leaves `516168751624777728` cosets, with density
`5383303927/441613360315210220469081750000`. The height matrix has a
certified rational lower eigenvalue `43/200`. The exact upper bridge is now
banked from Magma's Kummer embedding and duplication quartics:
`hhat([P-P0]) <= 3*log(H(P))+log(32)+log(1077517601)/3`. The normalization,
special fibres, five basis generators, and eight curve-point differences are
audited. At `H(P)<=20000`, exact enumeration of the resulting
`sum m_i^2<=280` ball leaves precisely the 36 known vectors. The missing
global node is now an independent absolute bound for `H(P)` or an equivalent
exhaustive integral-point/two-cover bound; modular density alone is not
completeness.
