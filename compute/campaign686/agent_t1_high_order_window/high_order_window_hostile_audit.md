# Hostile audit: sixth/seventh short-window route for Erdős 686 Target 1

Date: 2026-07-12

## Frozen inputs

```text
3bdb1a9711c083af0567de19c992d1315e704a64217da1042d3d033d7aedaf84  high_order_window_verify.py
d6529a07e644cba20e6ab0723bc756dc6c578247f92d82f99076c7be975f26f5  test_high_order_window_verify.py
c7ca78cf2777d70287cca9d084a72949c4b4f0b5ef402fe4a622622223b119cf  high_order_window_findings.md
```

The paths are relative to this directory.  The verifier consumes no output
from `Erdos686FifthLocalLift.lean`; it reconstructs all cofactor coefficients
and all formulae independently.

## Claim under audit

The package claims only:

1. the displayed sixth and seventh local and cyclic formulae are exact;
2. the verified short window makes `W6` nonzero in all 6,210 ordered views;
3. the resulting sixth/seventh magnitude bounds are weaker than the banked
   `P^2<U_kd` bound; and
4. the only fixed two-column seventh leading determinant is mixed in every
   exact lambda cell.

It does **not** claim Target 1, a target-scale pseudo-witness, a Lean theorem,
or a reason that order eight must also fail.

## Dependency tree and node verdicts

```text
N0 reconstruct signed local cofactor coefficients                         PASS
 |
 +-- N1 binomial expansion after 3X-M=aP                                  PASS
 |    +-- exact L6 formula                                                PASS
 |    `-- exact L7 formula                                                PASS
 |
 +-- N2 exact opposite-square product B                                  PASS
 |    +-- retain remainder of (bc)^3 L6 below P^5                        PASS
 |    `-- retain remainder of (bc)^3 L7 below P^6                        PASS
 |
 +-- N3 exact residual-window products                                   PASS
 |    +-- L^3 g^2d <= t < U^3 g^2d                                      PASS
 |    `-- bc < U^2g^2P^2 and P^2<Ud                                     PASS
 |
 +-- N4 explicit W5 quotient majorant                                    PASS
 |    `-- no unquantified O(d^2) phrase enters a verdict
 |
 +-- N5 W6 leading-term domination at 10^120                             PASS
 |    `-- monotone extension to every larger d                           PASS
 |
 +-- N6 W6/W7 modulus-to-size comparison                                 PASS, NO CUTOFF
 |
 `-- N7 seventh leading determinant                                      PASS, ALL MIXED
      +-- all 1,035 row matrices rank two                                PASS
      +-- all exact rational root cells                                  PASS
      `-- 0 one-sided open cells or rational boundaries                 PASS
```

### N1 and N2

SymPy expands polynomial identities over the rationals, not sampled values.
The separate integer grids then check 9,000 local and 74,520 cyclic signed
fixtures.  The cyclic verdict is congruence modulo `P^5` or `P^6`; it does not
mistake a remainder identity for literal equality before the exact
opposite-square relation is imposed.

### N3 and N4

Every upper-bound term is represented by an explicit integer constant in
`_arch_constants`.  In particular, the term `3bc W5/P^4` in `W6/P^4` is
retained through

```text
bc <= U^2 g^2P^2,
|W5/P^4| <= BW5 g^4d^2/P^2.
```

Thus the sixth-order sign conclusion does not silently discard the previous
quotient.

### N5

The worst exact right/left ratio is stored as an unreduced rational string,
not compared in floating point.  Its view is `(9,2,8,9)`.  The code checks
strict positivity at `d=10^120`; the left-minus-right polynomial has positive
degree-three leading coefficient and nonpositive lower-degree subtractions,
so increasing `d` preserves the inequality after division by `d^2`.

### N6

From nonzero `W6` and `P^5|W6`, the exact majorant gives only

```text
P <= C6 g^6d^3.
```

Outside the seventh leading-root cells, nonzero `W7` and `P^6|W7` give only

```text
P^2 <= C7 g^6d^3.
```

The verifier substitutes the maximum row loss `G_k` and compares both exact
right sides with `U_kd` at the target boundary.  Both are already larger,
and their ratio only grows with `d`.  Therefore neither is a packing gain.
No statement is made when a cyclic obstruction could be zero unless its
nonvanishing was separately proved.

### N7

The lambda interval is partitioned at exact `Fraction` roots.  Samples are
exact midpoints of rational cells.  All roots and both endpoints are then
tested separately.  Equal roots are retained: there are 33 equal pairs, two
inside the window.  Zero primitive weights are removed only when testing the
signs of nonzero terms, exactly as required for a one-sided sum.  Every open
cell is mixed; 2,138 rational boundaries are mixed and the two repeated-root
boundaries are all zero.  No boundary is one-sided.

## Boundary and falsification matrix

| boundary | verdict |
|---|---|
| all 6,156 generic ordered views | included |
| all 54 center-reflected ordered views | included |
| component base 3 | 3,000 local and 49,680 cyclic fixtures contain it |
| component base 2 | included in the cyclic fixture grid |
| negative component/opposite/cofactor data | included in the local grid |
| negative grouped loss | 37,260 cyclic fixtures |
| `k=5` absent degree-five/six coefficients | checked literally zero |
| `k=7` top degree-six coefficient | checked literally one |
| seventh rational root inside the window | 144 views retained, no sign claim |
| repeated seventh roots | 33 pairs retained |
| target-scale window-respecting pseudo-fixture | not found and not claimed |
| pre-existing out-of-window Hensel family | consistent; this package does not use it as a window falsifier |

## Final verdict

**PASS as an exact negative route audit.  FAIL as a Target 1 closure.**

The sixth-order nonvanishing is quantitatively real, but its fifth-power
modulus is paired with a cubic gap term and yields a weaker bound than the
existing residual square bound.  Seventh order has the same cubic scale; its
fixed leading determinant is mixed in all 1,105 cells.  Continuing this
specific higher-local-order lane is not justified without a new global
relation that controls the quotient lattice.
