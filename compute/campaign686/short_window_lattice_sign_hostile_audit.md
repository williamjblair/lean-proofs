# Erdős 686 short-window lattice-sign hostile audit

Audit date: 2026-07-10.

## Verdict

**PASS as a partial package.** The nine generic Lean theorems are safe to
integrate. The exact Python scan independently reproduces the producer's
finite arithmetic. The package does **not** close the three-owner branch or
Erdős 686.

The exact live scope is:

- 2,381 mixed weighted-term open cells;
- ten positive one-zero boundaries; and
- one unproved two-component size lemma, stated exactly below.

The finite 1,035-triple enumeration is not wrapped in a kernel theorem, so it
is not attestation-ready. The producer audit importer contains numerical
`example` checks plus `#check` and `#print`, but declares no independent
theorem. The hostile Lean module repairs that audit-independence gap for all
nine generic theorem surfaces; it does not pretend to kernel-wrap the finite
scan.

## Frozen producer boundary

The hostile verifier recomputed and matched all six SHA-256 digests before
using producer results:

| file | SHA-256 |
|---|---|
| `ErdosProblems/Erdos686ShortWindowLatticeSign.lean` | `1085863ae92e0d98841da3d667fa12de774ec843fe2a97988173f414dd8c905c` |
| `ErdosProblems/Erdos686ShortWindowLatticeSignAudit.lean` | `f89374d984a160b8fded04c9062a073ef8b2594cde75715c021ec7a2da6a0142` |
| `compute/campaign686/short_window_lattice_sign_attack.py` | `d66bbe0222141513156c5b277eaa971444e80436865dd69c30bc931f8d6587fc` |
| `compute/campaign686/test_short_window_lattice_sign_attack.py` | `a9c06f32dbc081b6491b33906c914cc94b2a78937be91257150ab253e02104dc` |
| `compute/campaign686/short_window_lattice_sign_findings.md` | `25730c340d97e95855b37d266394b71ce826c945c15ecfaccab1355ce9082560` |
| `docs/plans/2026-07-10-erdos686-lattice-sign-attack.md` | `04cdd6d53bbb5ef75318bb1480c2c49047aecc401726002eb7a9b3e015f9d448` |

No producer file was changed during this audit.

## Dependency tree and per-node verdict

```text
N0  Frozen six-file producer boundary                              PASS (SHA-256)
├─ N1  Nine generic arithmetic theorem statements                 PASS (Lean)
│  ├─ N1a producer proofs obey allowed axiom gate                 PASS
│  └─ N1b hostile fresh-name reproofs obey allowed axiom gate     PASS
├─ N2  Third-quotient threshold formula                           PASS (exact)
│  └─ N2a ordering stable for every d >= 10^120                   PASS (exact)
├─ N3  Primitive weights and Gamma for all 1,035 triples          PASS (exact)
├─ N4  Every open and zero-boundary sign cell counted             PASS (exact)
├─ N5  Nine positive strict slivers                               CLOSED
├─ N6  Eighteen positive one-zero boundaries
│  ├─ eight boundaries                                           CLOSED
│  └─ ten boundaries                                             OPEN
├─ N7  Uniform sign-only closure                                  FALSE
│  ├─ target-scale coefficient counterfixture                    PASS (exact)
│  └─ two realized local/composed fourth-lift fixtures            PASS (exact)
├─ N8  Two bounded components in every remaining target case     OPEN
└─ N9  Three-owner branch / Erdős 686                             NOT CLOSED
```

No node marked `OPEN` is used to prove a node marked `PASS` or `CLOSED`.

## Independent reconstruction

The hostile Python verifier imports no producer Python module. It generates
the coefficient of `z^r` in

```text
prod_{j != owner} (z + j - owner)
```

as the elementary symmetric sum of degree `k-1-r` in the offsets. This is a
different coefficient-generation algorithm from the producer's iterative
polynomial multiplication.

For each owner `s`, the hostile verifier then reconstructs

```text
T_s / (g^2 d)
  = -9 C_s lambda + 180 E_s delta_s + 108 D_s delta_s / d,
threshold_s
  = 20 E_s delta_s / C_s + 12 D_s delta_s / (C_s d).
```

It rebuilds the primitive cross-product weights from the `t` and `g^2 d`
coefficient columns and checks the remaining column exactly. No floating
point arithmetic is used.

## Ordering and weight audit

Across every owner root, every unequal root pair, and both short-window
endpoints, the minimum nonzero separation is

```text
247/3960.
```

The maximum correction magnitude is

```text
1171733/165.
```

The verifier checks by exact rational comparison that

```text
2 * (1171733/165) / 10^120 < 247/3960.
```

Hence no unequal thresholds can reorder or cross a window endpoint for any
`d >= 10^120`. There are exactly 27 equal-root pairs. Each occurs in a triple

```text
(h, (k+1)/2, k+1-h),
```

the center weight is zero, and the equal outer roots have opposite
corrections. This explicitly covers the equal-root and zero-weight boundary
case.

The 1,035 raw `Gamma` values have signs

```text
514 positive, 521 negative, 0 zero.
```

After orientation to `Gamma > 0`, the 3,105 weight components are

```text
1,539 positive, 1,539 negative, 27 zero,
```

with

```text
2,160 <= Gamma <= 4,070,625,913,172,821,209,661,440.
```

## Complete sign-cell reproduction

| `k` | triples | zero weights | mixed open | positive open | mixed boundaries | positive boundaries |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 10 | 2 | 15 | 1 | 4 | 2 |
| 7 | 35 | 3 | 69 | 1 | 33 | 2 |
| 9 | 84 | 4 | 167 | 1 | 82 | 2 |
| 11 | 165 | 5 | 378 | 2 | 211 | 4 |
| 13 | 286 | 6 | 674 | 2 | 386 | 4 |
| 15 | 455 | 7 | 1,078 | 2 | 621 | 4 |
| **total** | **1,035** | **27** | **2,381** | **9** | **1,337** | **18** |

There are no negative-only or zero-only weighted-term cells. The underlying
quotient-sign cells, before multiplying by the oriented weights, are:

```text
open:     1,847 mixed, 285 positive, 258 negative, 0 zero;
boundary:   699 mixed, 369 positive, 287 negative, 0 zero.
```

## One-sided exclusions

The hostile scan reproduces exactly these nine positive open slivers:

```text
(5;  1,3,5)
(7;  1,4,7)
(9;  1,5,9)
(11; 1,6,11)  (11; 2,6,10)
(13; 1,7,13)  (13; 2,7,12)
(15; 1,8,15)  (15; 2,8,14).
```

In each case the center weight is zero, the outer weights have absolute value
one, and both nonzero weighted terms are positive. The hostile Lean module
reproves the generic implication

```text
P^2 z_P + R^2 z_R = Gamma g^2
and Q^2 < A d
imply d < A Gamma^2 g^6,
```

under the producer's displayed positivity and factorization hypotheses. It
also repeats all nine exact `A * Gamma^2 * G^6 < 10^120` checks. Thus all nine
strict slivers are excluded.

There are two zero boundaries per sliver. The hostile reconstruction of the
fixed fourth coefficient, gcd factor, and bound

```text
d < A * K^2 * Gamma * g^10 / gcd(K^2, Gamma)
```

closes both boundaries for exactly

```text
(5;1,3,5), (7;1,4,7), (9;1,5,9), (11;2,6,10).
```

Therefore eight boundaries are excluded and ten remain live. A current upper
bound exceeding `10^120` is not treated as a witness or as an exclusion.

## Falsification of uniform positivity

The target-scale coefficient fixture is independently reproduced at

```text
k=5, owners=(1,2,3), d=10^120, g=1, lambda=188,
weights=(4,26,15), Gamma=57240.
```

Its weighted terms have signs `(-,+,-)` and sum exactly to `57240`. This is a
coefficient-identity fixture only; it is not described as a square or lift
fixture.

The hostile verifier separately reconstructs every local second, third, and
fourth lift, every composed second, third, and fourth lift, the reduced fourth
remainder, overlap divisibilities, and the lattice identity for:

| components | `g` | `d` | `lambda` | weighted-term signs | block equation |
|---|---:|---:|---:|:---:|:---:|
| `(3,5,2)` | 24 | 720 | `108317/576` | `(-,+,-)` | false |
| `(4,3,11)` | 87 | 11,484 | `34914989/15138` | `(-,+,-)` | false |

Both fixtures satisfy all local and composed lift checks and the short window.
Neither is an Erdős 686 counterexample because each fails the block equation.
They are exact counterexamples to a uniform sign-only deduction from the
banked local/composed lift conditions.

## Exact remaining quantified lemma

For each row `(k,A_k,G_k)`, define

```text
H_k = floor_sqrt(floor((10^120 - 1) / (A_k G_k^6))).
```

The exact values are:

| `k` | `H_k` |
|---:|---:|
| 5 | 212160590605173551323281417403147323796233912863684428 |
| 7 | 57046695925872527128812620336999351280253887202763 |
| 9 | 82747175828911780468168027732812182306888441 |
| 11 | 106758606375800441629531020205561424117038 |
| 13 | 13022519011656599698255286636722720 |
| 15 | 24979064466336593021876736560 |

For a target solution in one of the 2,381 mixed open cells or ten live
positive zero boundaries, orient the primitive lattice so `Gamma > 0`, and
for each of the three owners define

```text
V_s = P_s^2 * max(1, |w_s z_s|).
```

The exact missing lemma is:

> There exist two distinct owners `r` and `s` such that
> `V_r <= H_k g^2` and `V_s <= H_k g^2`.

This lemma would imply `P_r^2,P_s^2 <= H_k g^2`; the already reproved generic
short-window bridge would then give

```text
d < A_k H_k^2 g^6 <= A_k H_k^2 G_k^6 < 10^120.
```

The lemma is unproved. It is not counted as progress, and no claim is made
that its proof is easier than the remaining branch.

## Lean and test gates

The following all pass:

```text
8 producer pytest tests
8 hostile pytest tests
Python byte compilation for producer and hostile modules
Lean compilation of producer, producer importer, and hostile audit module
```

All producer and hostile theorem surfaces report only the allowed axioms

```text
[propext, Classical.choice, Quot.sound]
```

or a subset. No `native_decide`, `sorry`, or custom axiom is used. Lean emits
one non-blocking linter warning in both parallel proofs: the positivity
hypothesis `hS` in the generic lcm bound is redundant. This does not affect
the statement or proof.

## Integration recommendation

Integrate the nine generic Lean theorem surfaces and retain the exact scan as
audited external evidence. Do not mark the finite row scan attested, the
three-owner branch closed, or Erdős 686 solved. The only honest next proof
obligation is the quantified two-owner `H_k g^2` bound above, with separate
attention to the 2,381 mixed cells and ten live one-zero boundaries.
