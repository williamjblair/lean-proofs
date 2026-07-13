# Erdős 686 tail-1000 center/reflected packing slice

Status: **all 27 numerical packing pairs are Lean-closed at the
`10^1000` cutoff; the conclusion is scoped to a supplied exact
center/reflected three-bucket decomposition.**

This is a proper odd-tail restriction.  It does not construct an exactly-three
decomposition from the full owner assignment, discard additional live owners,
or close `OddThueTail1000Hypothesis`.

## Exact supplied slice

Fix

```text
k in {5,7,9,11,13,15},
1 <= r < (k+1)/2,
m = (k+1)/2,
i = m-r,
l = m+r,
X = localResidual n d m = 3(n+m)-d.
```

The equation-facing headline surface is
`no_four_solution_of_exact_center_reflected_three_bucket_tail1000`.  Its
inputs are the exact equation

```text
blockProduct k (n+d) = 4 * blockProduct k n,
10^1000 <= d,
```

together with supplied positive naturals `g,P,Q,R`, a supplied cleaned-gap
factorization and loss bound

```text
d = g*P*Q*R,
g <= targetAggregateLoss k,
```

the center, left, and right ownership divisibilities

```text
P | n+m,
Q | n+i,
R | n+l,
```

and exact square-residual identities for supplied natural cofactors `a,b,c`:

```text
X       = a*P^2,
X - 3*r = b*Q^2,
X + 3*r = c*R^2.
```

The theorem derives the center cubic and endpoint-square bounds; neither is a
headline assumption.  No pairwise-coprimality premise is used by the packing
algebra.  The pure numerical interface is already kernel-checked as
`no_reflected_three_bucket_tail1000_of_packing_bounds`.

## Exact constants

The row residual ceiling is

```text
U_k = targetReflectedResidualCeiling k
    = (14,17,23,26,29,35)
```

for `k=(5,7,9,11,13,15)`.  The cleaned loss is

```text
G_k = targetAggregateLoss k
    = (108,1620,136080,1224720,242494560,18914575680).
```

The exact lower residual ratio used to exclude a zero endpoint determinant is

```text
R_k*d < H_k*X,

(R_k,H_k) =
  (268048,31951),
  (278097,21902),
  (283346,16653),
  (286567,13432),
  (288745,11254),
  (290316, 9683).
```

The center and determinant constants are definitions, not asymptotic
majorants:

```text
HC(k) = (((k-1)/2)!)^2 * U_k,

KD(k,r) = 54*r*(|C|*U_k^3 + 8*|D|*U_k*r + 40*|E|*r^2),
```

where `(C,D,E)` are the exact local coefficient tables at `i=m-r`.

## Determinant packing

Let `t=a*b*c`.  The three exact residual identities and
`d=g*P*Q*R` give

```text
t*d^2 = g^2*X*(X^2-9*r^2).                              (1)
```

At the two reflected endpoints, the composed third obstructions are

```text
T_- = -9*C*t + 216*D*g^2*r^2 + 360*E*g^2*r^2*d,
T_+ = -9*C*t - 216*D*g^2*r^2 + 360*E*g^2*r^2*d.
```

The local third lift and the exact three-bucket composition give

```text
Q^2 | T_-,
R^2 | T_+.
```

The residual-weighted determinant is exactly

```text
(X-3*r)*T_+ - (X+3*r)*T_-
  = 54*r*(C*t - 8*D*X*g^2*r - 40*E*g^2*r^2*d).          (2)
```

Its left side is divisible by `Q^2*R^2`.  Equation (1), the exact ratio lower
bound, and `X<U_k*d` prove that the parenthesized factor in (2) is nonzero.
The exact triangle bound therefore yields

```text
Q^2*R^2 < KD(k,r)*g^2*d.                                (3)
```

The raw center lift supplies

```text
P^3 < HC(k)*d.                                           (4)
```

Squaring (4), cubing (3), substituting `d=g*P*Q*R`, and using `g<=G_k`
gives the strict packing inequality

```text
d < HC(k)^2 * KD(k,r)^3 * G_k^12.                       (5)
```

## The 27/12/15 cutoff table

The historical `10^120` theorem closed 12 of the 27 unordered reflected
pairs.  The tail-1000 certificate closes the other 15 because every exact
right side of (5) is below `10^200`, hence below `10^1000`.

| `k` | allowed `r` | total pairs | closed below `10^120` | newly closed | maximum cutoff digits |
|---:|:---:|---:|---:|---:|---:|
| 5 | `1..2` | 2 | 2 | 0 | 49 |
| 7 | `1..3` | 3 | 3 | 0 | 71 |
| 9 | `1..4` | 4 | 4 | 0 | 104 |
| 11 | `1..5` | 5 | 3 | 2 (`r=4,5`) | 125 |
| 13 | `1..6` | 6 | 0 | 6 | 163 |
| 15 | `1..7` | 7 | 0 | 7 | 197 |
| **total** |  | **27** | **12** | **15** | **197** |

The largest value occurs at `(k,r)=(15,7)` and is exactly

```text
11610649631876010113370868874524711316149061611358461908894511083104857723748854881520596258670412448220700825805753753896747417216907729085457360108954666243725838628597792768000000000000000000000.
```

This integer has 197 digits and is strictly less than `10^200`.  The kernel
theorem `target_reflected_packing_cutoff_certificate_tail1000` quantifies over
all six target rows and every `r` in the displayed range; it does not infer a
limit from the maximum row.

## Boundary fixtures

- The exact telescopes `(k,n,d)=(9,2,1)` and `(15,4,1)` are preserved.  They
  violate the explicit premise `10^1000<=d`.
- The 121-digit CRT gap with components
  `(101^20,103^20,107^20)` is below `10^1000`.  Its frozen representative
  fails fifth order; its Hensel extension satisfies the fifth-order
  congruence package but has a nonzero block difference and fails every
  coarse upper residual window.  It also uses owners `(1,2,4)` at `k=5`, not
  a center plus a reflected pair.  It is not in the headline scope.
- Unit components are not cancelled.  The generic packing theorem assumes
  `0<P,Q,R`, so a supplied unit component `1` is an admitted algebraic
  boundary.  An empty all-owner bucket is literally such a unit; this slice
  does not relabel it as a live cleaned owner.
- Both endpoint distances are included: `r=1` and
  `r=(k-1)/2`.  The latter is exactly the strict endpoint
  `r<(k+1)/2` in an odd row.
- The 27 pairs are unordered center/reflected placements.  Swapping the two
  endpoints gives 54 oriented views, but it does not create 54 independent
  packing cases.

## Exact scope and remaining gap

The result excludes only a supplied factorization with exactly the center
owner and the reflected pair `m-r,m+r`.  It does not prove any of the
following:

1. that an arbitrary exact equation has exactly three cleaned components;
2. that three owners extracted from a larger all-owner assignment exhaust
   the gap;
3. that arbitrary three distinct owners are center/reflected;
4. that four-or-more live owners can be discarded or regrouped into this
   slice;
5. `OddThueTail1000Hypothesis`, Target 1, or Erdős #686.

The live odd-tail problem is therefore the complementary owner geometry and
the arbitrary-owner/all-owner short-window branch, not another cutoff
calculation for these 27 pairs.

## Shared campaign documents needing a later update

No shared registry is edited by this findings artifact.  After the headline
theorem and metadata gates are final, update these precise sections:

- `compute/campaign686/approach_registry.md`, **Target 1 routes**, row
  `T1-5L`: record that all 54 center/reflected oriented views close only in
  the supplied exactly-three slice at `d>=10^1000`; retain the Hensel/CRT
  verdict for generic congruence-only fifth order.
- `compute/campaign686/audit.md`, after **Dependency tree: three cleaned
  residual buckets**: add the center/reflected determinant-packing dependency
  tree and the `27=12+15` exact cutoff split.
- `PROGRESS_Erdos686.md`, **0. Executive status** near the three-bucket and
  reflected-sliver paragraphs, and **8. Current proof obligations**: remove
  center/reflected exactly-three placements from the tail-1000 subcase while
  retaining arbitrary owners and extra-owner configurations.
- `FRONTIER.md`, **Erdős #686** in the three-bucket ledger around the
  reflected sliver discussion: add the supplied center/reflected tail-1000
  closure with the same scope warning.
- `compute/campaign686/final_residual_hostile_audit.md`, **Dependency tree**
  and **Per-node verdicts**, only if the final residual ledger explicitly
  imports this restriction; do not imply that the odd arm itself is closed.
- `compute/campaign686/agent_t1_all_owner/reflected_three_bucket_findings.md`
  and its hostile audit: retain the historical `10^120` 12-pair result and
  add a pointer to this separate tail-1000 upgrade rather than rewriting its
  frozen 12/15 record.
- Integration metadata: `ErdosProblems.lean`, `Audit.lean`, `proofs.yaml`,
  and `attestations.json` must name only the actual public Lean theorems and
  their kernel-axiom reports.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t1_all_owner/test_reflected_three_bucket_verify.py
python3 -m \
  compute.campaign686.agent_t1_all_owner.reflected_three_bucket_verify \
  --compact
lake env lean ErdosProblems/Erdos686ReflectedThreeBucketDeterminant.lean
```

The focused exact test currently reports `2 passed`.  The Lean module reports
only `[propext, Classical.choice, Quot.sound]` on
`target_reflected_packing_cutoff_certificate_tail1000`,
`no_reflected_three_bucket_tail1000_of_packing_bounds`, the equation-facing
endpoint divisibilities, and the headline
`no_four_solution_of_exact_center_reflected_three_bucket_tail1000`.
