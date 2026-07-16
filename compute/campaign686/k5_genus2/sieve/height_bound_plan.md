# Erdős #686, k=5: rigorous height-reduction plan

Date: 2026-07-16

Status: the Mordell-Weil lattice lower bound and the global upper comparison
from a curve point to its Jacobian canonical height are certified. An
independent absolute curve-height bound remains open.

## Certified lattice lower bound

The 60-digit Magma height-pairing matrix is frozen in
`height_certificate.json`. Magma verifies every entry lies within `1/1000`
of the rational center matrix.

Exact rational Sylvester tests prove

```text
center_matrix - (11/50) I
```

is positive definite. An entrywise error of at most `1/1000` has spectral
norm at most `5/1000`. Therefore the true canonical-height matrix `H`
satisfies

```text
lambda_min(H) > 11/50 - 5/1000 = 43/200.
```

Consequently, for every lattice vector `m in Z^5`,

```text
canonical_height(m1 G1 + ... + m5 G5)
  >= (43/200) * ||m||_2^2.
```

This is the exact lower inequality needed to convert a canonical-height upper
bound into a finite coefficient radius.

## Correct use of `HeightConstant`

The computed constant is

```text
7.8144270562185764398936470553098535883618188483213819664447037...
```

Its documented direction is

```text
h_K(D) <= canonical_height(D) + c.
```

It is not a symmetric absolute difference bound and does not by itself give
an upper bound on `canonical_height(D)` from `h_K(D)`. The internal
Mordell-Weil message `height-difference bound: 3.8026` is not substituted
for this theorem without a separately documented interface.

## Certified upper comparison

For a primitive weighted-projective curve point `P=(A:B:C)` and
`D=[P-P0]`, Magma's exact Kummer model gives

```text
kappa(D) = (A^2*C : A^3 : 0 : 6*B+8*A*C^2+18*C^3).
```

The exceptional `P=(0:-3:1)` and the two points at infinity are separately
audited. Primitive normalization of Kummer coordinates can only lower the
naive height. Therefore

```text
h_K(D) <= 3*log(H(P)) + log(32).
```

The four exact duplication-quartic coefficient L1 norms are

```text
[25186676, 25439912, 14117360, 1077517601].
```

Hence `h_K(2D) <= 4*h_K(D)+log(1077517601)`, and iteration gives

```text
canonical_height(D)
  <= 3*log(H(P)) + log(32) + log(1077517601)/3.
```

`CanonicalHeight(G1)`, `HeightPairing(G1,G1)`, and the Kummer doubling limit
use the same normalization; there is no factor of two.

## Sieve-height reduction

For a supplied absolute bound on `H(P)`, the inequality gives

```text
canonical_height([P-P0]) <= Hmax
```

is available, the lattice lower bound gives

```text
||m||_2^2 <= (200/43) * Hmax.
```

For each surviving combined coset `c+L`, reduce the quadratic form

```text
(c + Lz)^T H (c + Lz)
```

by exact rational LLL/Fincke-Pohst bounds. A coset is eliminated if its
minimum exceeds `Hmax`. Surviving bounded vectors are then checked against:

```text
[P-P0] in J(Q),
P in C(Q),
the inverse-square relation,
n>=0,
d>=5.
```

The combined HNF has very large diagonal scales, so even a moderate
coefficient bound may collapse most of the `5.16e17` symbolic cosets without
enumerating them.

At `H(P)<=20000`, the deliberately coarse exact estimates
`20000<2^15`, `1077517601<2^31`, and `log(2)<1` give
`sum m_i^2<=280`. Enumeration of all `6,944,265` integer vectors in this
ball leaves exactly the 36 known projective vectors; packets through `p=23`
already suffice.

## Exact next computational obligation

Prove an independent absolute upper bound for `H(P)`, or replace it by an
equivalent exhaustive integral-point bound on the eight two-covers. Without
that input, the bounded lift audit is not global rational-point
completeness. If another full packet is later useful, the invariant-only
scout ranks `p=107` first.

Reproduction:

```bash
python3 -m compute.campaign686.k5_genus2.sieve.height_certificate_verify
python3 -m compute.campaign686.k5_genus2.sieve.height_certificate_verify --online
python3 -m pytest -q \
  compute/campaign686/k5_genus2/sieve/test_height_certificate_verify.py
```
