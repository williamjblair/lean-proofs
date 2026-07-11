# Erdős 686 short-window lattice-sign audit

Audit date: 2026-07-10.

## 0. Verdict

The lattice-sign route gives a proper new exclusion, but it does not close the
three-owner core.

- All 1,035 target owner triples were scanned with exact rational arithmetic.
- After orienting the primitive cross product so that `Gamma > 0`, the 3,105
  weight components split exactly as 1,539 positive, 1,539 negative, and 27
  zero.  Every `Gamma` is nonzero; before orientation 514 are positive and 521
  are negative.
- The short window does not make the third quotients uniformly positive.  The
  2,390 open quotient-sign cells split as 1,847 mixed, 285 all positive, and
  258 all negative.
- Weighted lattice terms are mixed in 2,381 of the 2,390 open cells.  The only
  nine one-sided open cells are narrow reflected-center slivers.  Each of
  those nine forces `d < 10^120`, by an exact size bound whose generic bridge
  is proved in Lean.
- There are 18 one-sided zero boundaries.  The current quotient and coprime
  packing bounds exclude eight of them; ten remain.
- Every other coefficient cell permits cancellation.  A target-scale exact
  coefficient fixture and two genuine short fourth-lift fixtures show that a
  sign-only closure is false.

The exact remaining gap is the single quantified two-term size lemma in
Section 7.  It is not proved here and is not counted as progress.

## 1. Frozen dependency and exact normalization

This audit consumes the frozen quotient package and verifies its six SHA-256
digests before any scan.  The digests are embedded in
`short_window_lattice_sign_attack.py`; a mismatch aborts the computation.

For owner `s`, write

```text
T_s = P_s^2 z_s
    = -9 C_s t + 180 E_s delta_s g^2 d + 108 D_s delta_s g^2,
lambda = t / (g^2 d).
```

Since `C_s` is nonzero in every target row,

```text
T_s / (g^2 d)
  = -9 C_s (lambda - r_s - c_s/d),
r_s = 20 E_s delta_s / C_s,
c_s = 12 D_s delta_s / C_s.
```

Thus every quotient sign change occurs at the exact rational threshold
`lambda = r_s + c_s/d`.  The short window supplies

```text
125 < lambda < A_k^3,
d >= 10^120.
```

For the primitive cross-product weights, oriented so that `Gamma > 0`, the
frozen Lean identity is

```text
sum_s w_s P_s^2 z_s = Gamma g^2.
```

No division by `C_s`, `g`, `P_s`, or a weight enters the lattice identity.

## 2. Dependency tree and per-node verdict

```text
N0  Close the three-owner branch from the quotient lattice                OPEN
 ├─ N1  Exact third-quotient affine formula and lattice identity        LEAN-PROVED
 ├─ N2  Threshold ordering for every d >= 10^120                     EXACT-PROVED
 ├─ N3  All 1,035 weight/Gamma/sign cells                            EXACT-SCANNED
 ├─ N4  Two bounded component squares imply d < A H^2 g^6            LEAN-PROVED
 ├─ N5  Nine strict reflected one-sided slivers                       CLOSED
 ├─ N6  Eighteen reflected one-zero boundaries
 │   ├─ eight boundaries                                             CLOSED
 │   └─ ten boundaries                                               OPEN
 ├─ N7  Ordinary mixed-sign cells                                      OPEN
 └─ N8  Uniform sign/positivity closure                               FALSE
     ├─ target-scale coefficient fixture                              EXACT
     └─ two short local/composed fourth-lift fixtures                  EXACT
```

`N2`, `N3`, `N5`, `N6`, and `N8` are exact Python arithmetic, not
kernel-enumerated finite theorems.  `N1` is in the frozen quotient module.
`N4`, the generic reflected-boundary lcm packing, all nine numerical
strict-sliver cutoffs, and the four numerical closed-boundary cutoffs are
independently imported and checked in Lean.

## 3. Threshold stability and weight audit

Across all roots, unequal root pairs, and window endpoints, the minimum
nonzero separation is

```text
247/3960.
```

Across all owner occurrences, the maximum correction magnitude is

```text
1171733/165.
```

For every `d >= 10^120`, exact integer cross multiplication verifies

```text
2 * (1171733/165) / d
  <= 2 * (1171733/165) / 10^120
  < 247/3960.
```

Therefore no unequal threshold can cross another threshold or a window
endpoint at target size.  Exactly 27 root pairs are equal.  All 27 occur in
a reflected triple

```text
(h, (k+1)/2, k+1-h),
```

and in every such triple the center weight is zero.  The two equal roots are
split by opposite corrections `+c/d` and `-c/d`.  This handles centers and
reflections explicitly rather than treating them as a generic limiting case.

The exact scan totals are:

| `k` | triples | zero weights | mixed open cells | positive open cells | mixed boundaries | positive boundaries |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 10 | 2 | 15 | 1 | 4 | 2 |
| 7 | 35 | 3 | 69 | 1 | 33 | 2 |
| 9 | 84 | 4 | 167 | 1 | 82 | 2 |
| 11 | 165 | 5 | 378 | 2 | 211 | 4 |
| 13 | 286 | 6 | 674 | 2 | 386 | 4 |
| 15 | 455 | 7 | 1,078 | 2 | 621 | 4 |
| **total** | **1,035** | **27** | **2,381** | **9** | **1,337** | **18** |

There are no negative-only or zero-only weighted-term cells.  This is not a
contradiction: with `Gamma > 0`, every ordinary cell has both positive and
negative terms, while each exceptional reflected cell has positive terms.

The correction satisfies

```text
2160 <= Gamma <= 4070625913172821209661440
```

after orientation.  Both extrema are exact scan outputs.

## 4. The nine one-sided reflected slivers

The complete list is below.  In each row the one-sided interval is exactly

```text
r - c/d < lambda < r + c/d.
```

The two nonzero weights have absolute value one, the center weight is zero,
and both weighted endpoint terms are positive.

| `k` | owners | `Gamma` | `r` | `c` | digits of `A Gamma^2 G^6` | target cutoff |
|---:|:---:|---:|:---:|:---:|---:|:---:|
| 5 | (1,3,5) | 86400 | 700/3 | 200 | 24 | yes |
| 7 | (1,4,7) | 6858432 | 812 | 2646/5 | 35 | yes |
| 9 | (1,5,9) | 757444608 | 118124/63 | 36528/35 | 50 | yes |
| 11 | (1,6,11) | 114789312000 | 885665/252 | 36905/21 | 61 | yes |
| 11 | (2,6,10) | 4587466752 | 1804/7 | 73744/105 | 58 | yes |
| 13 | (1,7,13) | 23117159669760 | 6706804/1155 | 1032252/385 | 79 | yes |
| 13 | (2,7,12) | 870772032000 | 703105/924 | 279955/231 | 76 | yes |
| 15 | (1,8,15) | 6000400823316480 | 30946717/3510 | 8202131/2145 | 95 | yes |
| 15 | (2,8,14) | 211129881108480 | 23590132/15015 | 9427596/5005 | 92 | yes |

Here `G` is the row loss bound.  The proof of the cutoff is exact.  If the
endpoint components are `P,R` and the center component is `Q`, then

```text
P^2 |z_P| + R^2 |z_R| = Gamma g^2,
P^2 <= Gamma g^2,
R^2 <= Gamma g^2.
```

The center residual has positive cofactor and satisfies `Q^2 < A d`.  Since
`d = gPQR`, cancellation of positive `Q` gives `Q < AgPR`.  Consequently

```text
d = gPQR < A g^2 P^2 R^2 <= A Gamma^2 g^6 <= A Gamma^2 G^6 < 10^120.
```

The generic implication is theorem
`reflected_one_sided_short_window_gap_lt_cutoff`; the nine final numerical
inequalities are `norm_num` checks in the independent audit importer.

## 5. Exact zero boundaries

At either endpoint of a positive sliver, one endpoint quotient is zero and
the other satisfies

```text
R^2 |z_R| = Gamma g^2.
```

For the zero endpoint, the frozen fourth reduction gives

```text
P | K g^4.
```

Because `P` and `R` are coprime,

```text
P^2 R^2 | lcm(K^2 g^8, Gamma g^2).
```

Put `S = gcd(K^2,Gamma)`.  Factoring the common `S g^2` gives the exact upper
bound

```text
lcm(K^2 g^8, Gamma g^2) <= K^2 Gamma g^8 / S,
d < A K^2 Gamma g^10 / S.
```

Substitution of the row loss bound closes both boundaries for four triples:

```text
(5; 1,3,5), (7; 1,4,7), (9; 1,5,9), (11; 2,6,10).
```

Their exact bound sizes are respectively 43, 66, 100, and 115 decimal
digits.  The ten boundaries still live are both boundaries of

```text
(11; 1,6,11),
(13; 1,7,13), (13; 2,7,12),
(15; 1,8,15), (15; 2,8,14).
```

The corresponding current bounds have 121, 159, 152, 196, and 187 decimal
digits.  These are failures of the current bound, not witnesses.

The generic packing and cutoff are theorems
`coprime_square_product_dvd_lcm`, `reflected_boundary_lcm_bound`, and
`reflected_one_zero_short_window_gap_lt_cutoff`.  The four displayed closed
cutoffs are independent `norm_num` checks.

## 6. Exact counterfixtures to uniform positivity

### 6.1 Target-scale coefficient counterfixture

Take `k=5`, owners `(1,2,3)`, `d=10^120`, `g=1`, and `t=188d`, so
`lambda=188` lies strictly inside `(125,14^3)`.  Orienting gives

```text
w = (4,26,15),
Gamma = 57240,
(w_s T_s) =
  (-112032 d + 43200,
    240552 d + 14040,
   -128520 d).
```

The `d` coefficients cancel exactly and the three terms sum to `57240`.
Their signs are `(-,+,-)`.  This is an exact target-scale fixture for the
coefficient identity only; it is not claimed to satisfy square divisibility
or the local lifts.

### 6.2 Realized short fourth-lift counterfixtures

The frozen validator rechecks every local lift, composed lift, reduced fourth
congruence, overlap divisor, quotient bound, and lattice identity.

For the explicit `p=2,p=3` fixture

```text
k=5, owners=(1,2,3), (P,Q,R)=(3,5,2), g=24, d=720,
X=(4122,4125,4128), lambda=108317/576,
z=(-1290418560,153537120,-888518160),
w P^2 z=(-46455068160,99799128000,-53311089600).
```

The weighted sum is exactly `32970240 = 57240*24^2` and has signs
`(-,+,-)`.

For the largest recorded small short fixture

```text
k=5, owners=(1,2,3), (P,Q,R)=(4,3,11), g=87, d=11484,
X=(151728,151731,151734), lambda=34914989/15138,
z=(-2638048706388,1194199415568,-60940558008),
w P^2 z=(-168835117208832,279442663242912,-110607112784520).
```

The weighted sum is exactly `433249560 = 57240*87^2`, again with signs
`(-,+,-)`.  Both fixtures are below `10^120` and fail the block equation, so
neither is a counterexample to Erdős 686.  They are exact counterexamples to
deducing a one-sided lattice merely from the short window and the banked four
local/composed lifts.

The `d=1` telescopes `(k,n)=(9,2)` and `(15,4)` are also reproduced exactly.

## 7. Single quantified remaining sign/size lemma

For each row define

```text
H_k = floor_sqrt(floor((10^120-1)/(A_k G_k^6))).
```

The exact values are:

| `k` | `H_k` | maximum `Gamma` in row |
|---:|---:|---:|
| 5 | 212160590605173551323281417403147323796233912863684428 | 369360 |
| 7 | 57046695925872527128812620336999351280253887202763 | 2874916800 |
| 9 | 82747175828911780468168027732812182306888441 | 66846911212800 |
| 11 | 106758606375800441629531020205561424117038 | 8697763038159360 |
| 13 | 13022519011656599698255286636722720 | 119431440241402798080 |
| 15 | 24979064466336593021876736560 | 4070625913172821209661440 |

For every row, exact arithmetic verifies

```text
Gamma < H_k,
A_k H_k^2 G_k^6 < 10^120.
```

Orient the primitive lattice so `Gamma>0` and define the nonnegative proxy

```text
V_s = P_s^2 * max(1, |w_s z_s|).
```

The single remaining lemma is:

> For every target solution left after the proved one-sided cutoffs, there
> exist two distinct owners `r,s` such that
> `V_r <= H_k g^2` and `V_s <= H_k g^2`.

This is fully quantified and has no asymptotic or unqualified uniformity.  It
immediately gives two component-square bounds; the Lean theorem
`two_component_short_window_gap_lt_cutoff` then yields

```text
d < A_k H_k^2 g^6 <= A_k H_k^2 G_k^6 < 10^120,
```

contradicting the target hypothesis.

For a mixed cell with at least two nonzero weighted quotients, a sufficient
form is the negative-mass inequality

```text
U_s = w_s P_s^2 z_s,
N = sum_s max(0,-U_s),
N <= (H_k-Gamma) g^2.
```

Indeed the positive mass is `N+Gamma g^2 <= H_k g^2`, so every nonzero term
has magnitude at most `H_k g^2`.  On the ten live reflected zero boundaries,
the lemma reduces exactly to the missing `H_k g^2` square bound for the
zero-quotient endpoint; the other endpoint already has square at most
`Gamma g^2`.

The target-scale coefficient fixture in Section 6 violates the displayed
negative-mass sufficient inequality at coefficient level.  Thus coefficient
signs alone cannot prove the size lemma; a proof must use additional square,
divisibility, or higher-lift information.

## 8. Reproduction and kernel gate

Run:

```bash
python3 compute/campaign686/short_window_lattice_sign_attack.py
python3 -m pytest -q compute/campaign686/test_short_window_lattice_sign_attack.py
python3 -m py_compile \
  compute/campaign686/short_window_lattice_sign_attack.py \
  compute/campaign686/test_short_window_lattice_sign_attack.py
lake build ErdosProblems.Erdos686ShortWindowLatticeSign
lake env lean ErdosProblems/Erdos686ShortWindowLatticeSignAudit.lean
```

The public Lean theorems report only

```text
[propext, Classical.choice, Quot.sound]
```

through the kernel axiom audit.  No `sorry`, `admit`, `axiom`, `native_decide`,
or `ofReduceBool` is used.  The finite 1,035-triple scan and the finite
row-coefficient substitutions are exact and tested.  The generic one-sided
size bridges, generic boundary lcm packing, nine displayed numerical
strict-sliver inequalities, and four displayed closed-boundary inequalities
are kernel-checked.  No attestation is claimed for the unresolved remaining
lemma.
