# Erdős 686 three-owner short-window quotient attack

Status: **proper fourth-quotient and lattice restrictions proved; no
target-size short-window pseudo-witness found; three-owner branch remains
open.**

The generic arithmetic is kernel-checked in
`ErdosProblems/Erdos686ShortWindowQuotient.lean`, with an independent importer
in `ErdosProblems/Erdos686ShortWindowQuotientAudit.lean`. Exact target-row
arithmetic and searches are in `short_window_quotient_attack.py`, with focused
tests in `test_short_window_quotient_attack.py`.

The public Lean theorems are behind the required axiom gate. The finite
2,603-case application described in section 6 is exact Python arithmetic plus
a generic Lean packing theorem; it is **not yet an attestation-ready
row-quantified Lean wrapper**. This boundary is intentional and must be
preserved during integration.

## 1. Exact setup and short quotient

For distinct owners `i,j,l`, write

```text
d = gPQR,
X_i = aP^2,  X_j = bQ^2,  X_l = cR^2,
t = abc,
5d < X_s < A_k d.
```

Because `|X_s-X_u|=3|s-u|<=42<d`, the three residuals have one common floor
quotient

```text
q = floor(X_i/d) = floor(X_j/d) = floor(X_l/d).
```

Writing

```text
X_s = qd + P_s y_s,       0 <= P_s y_s < d,
```

gives the exact finite-window normalization

```text
a_s P_s = q g P_u P_v + y_s,                         (1)
P_s y_s - P_u y_u = 3(s-u).                          (2)
```

The small fixture in section 7 has `q=5` and

```text
(P,Q,R)=(3,5,2),   (P y_P,Q y_Q,R y_R)=(522,525,528).
```

Equation (2) is the requested short lattice, not a heuristic approximation.

## 2. Third quotients and fourth cancellation

For one owner `s`, let

```text
delta_s = (s-u)(s-v),       sigma_s = (s-u)+(s-v),
```

and let `C_s,D_s,E_s,H_s` be the constant through cubic Taylor
coefficients. The banked composed obstructions are

```text
O_s = 3(C_s t - 12D_s g^2 delta_s),
T_s = -3O_s + 180E_s g^2 delta_s d.
```

Name the exact third quotient

```text
T_s = P_s^2 z_s.                                      (3)
```

The fourth obstruction is

```text
P_s^3 | 3a_u a_v T_s + P_s^2 J_s,
```

where

```text
J_s = -9D_s t^2
      -108D_s t g^2 sigma_s
      +324E_s t g^2 delta_s
      +6804H_s g^4 delta_s^2.
```

Cancelling `P_s^2` in Lean, without primality, gives the new exact quotient
congruence

```text
P_s | 3a_u a_v z_s + J_s.                             (4)
```

This is proved both generically and directly for the banked
`threeBucketFourthObstruction` surface.

## 3. Fixed-coefficient reduction

Eliminate `t` from `J_s` using `O_s`. Define

```text
K_s = 108 delta_s [
        -108D_s^3 delta_s
        + C_s D_s(-108D_s sigma_s + 324E_s delta_s)
        + 567C_s^2 H_s delta_s].                      (5)
```

Lean proves the signed polynomial identity

```text
9C_s^2 J_s = M_s O_s + K_s g^4                       (6)
```

with the explicit multiplier

```text
M_s = -9D_s(3C_s t + 36D_s g^2 delta_s)
      +3C_s g^2(-108D_s sigma_s + 324E_s delta_s).
```

Combining `P_s|O_s` with (4) and (6) gives

```text
P_s | 27C_s^2 a_u a_v z_s + K_s g^4.                 (7)
```

Therefore every common divisor satisfies

```text
G | P_s and G | z_s   ==>   G | K_s g^4.              (8)
```

In particular, at a noncentral owner the overlap between `P_s` and its third
quotient is supported on one fixed row coefficient and the bounded loss.

The exact scan covers all `6,210` ordered distinct target triples. It finds

```text
K_s = 0  <=>  s is the odd-row center.
```

There are `502` ordered center-owner occurrences. Off center,

```text
min |K_s| = 17,729,280,
max |K_s| =
7,628,070,240,970,929,200,984,341,763,734,527,541,248,000,
```

the maximum occurring at `(k,s,u,v)=(15,1,14,15)`. At a center both odd
Taylor coefficients `D_s,H_s` vanish and hence `K_s=0`; Lean proves this
degeneracy explicitly. No fixed-coefficient conclusion is claimed there.

## 4. Opposite-cofactor overlap

The residual difference itself controls the cofactor overlap. Lean proves
the generic signed statement

```text
G|P_s, G|a_u,
a_s P_s^2-a_u P_u^2=3(s-u)
    ==> G|3(s-u).                                     (9)
```

Consequently

```text
gcd(P_s,a_u) | 3|s-u|,
gcd(P_s,a_v) | 3|s-v|,
gcd(P_s,a_u a_v) | 9|delta_s|.                       (10)
```

This retains the bases `2` and `3`; no unit cancellation is used.

## 5. Exact three-term lattice

Write

```text
alpha_s = -9C_s,
beta_s  = 180E_s delta_s,
gamma_s = 108D_s delta_s.
```

Then (3) is the affine equation

```text
P_s^2 z_s = alpha_s t + beta_s g^2 d + gamma_s g^2.   (11)
```

Let `w=(w_i,w_j,w_l)` be the primitive cross product of the three
`(alpha_s,beta_s)` rows. Lean proves the generic determinant identity

```text
sum_s w_s P_s^2 z_s = g^2 sum_s w_s gamma_s.          (12)
```

The exact target scan checks all `1,035` unordered triples:

- every coefficient matrix has rank two;
- every right-side coefficient `Gamma=sum w_s gamma_s` is nonzero;
- only `27` individual weights vanish;
- `min |Gamma|=2,160` and
  `max |Gamma|=4,070,625,913,172,821,209,661,440`.

Thus the three third quotients cannot all vanish.

The window also gives a proper per-owner quotient bound. Since

```text
t < A_k^3 g^2 d
```

and `5d<a_sP_s^2`, define

```text
B_s = 9|C_s|A_k^3
      +108|D_s||delta_s|
      +180|E_s||delta_s|.
```

Then

```text
5|z_s| < B_s g^2 a_s.                                 (13)
```

The natural-number cancellation behind (13) is Lean-proved. The largest
`B_s` in each row is checked exactly by the verifier.

## 6. Two-zero quotient branch

Suppose two **noncentral** third quotients vanish, say `z_i=z_j=0`. From
(7),

```text
P | K_i g^4,       Q | K_j g^4.
```

Let `L=lcm(|K_i|,|K_j|)`. Pairwise coprimality packs these into

```text
PQ | L g^4.                                           (14)
```

In (12) only the remaining term survives. If its weight is zero, (12)
immediately contradicts `Gamma!=0`. Otherwise its quotient is nonzero and

```text
R^2 |w_R| <= |Gamma|g^2.                              (15)
```

Lean combines (14), (15), and `d=gPQR` into

```text
d^2 |w_R| <= L^2 |Gamma| g^12.                        (16)
```

and provides the corresponding abstract cutoff theorem.

The exact finite scan then obtains:

| `k` | noncentral two-zero cases | zero-weight contradictions | numeric closures | closed |
|---:|---:|---:|---:|---:|
| 5  | 18   | 2 | 16  | 18 |
| 7  | 75   | 3 | 72  | 75 |
| 9  | 196  | 4 | 192 | 196 |
| 11 | 405  | 5 | 400 | 405 |
| 13 | 726  | 6 | 720 | 726 |
| 15 | 1,183 | 7 | 894 | 901 |

Therefore, at target size:

- for every `k<=13`, if two third quotients vanish, at least one zero owner
  must be the center;
- for `k=15`, 901 of the 1,183 noncentral two-zero placements are excluded;
  282 such placements remain, in addition to center-containing placements.

This is a proper restriction, not a reformulation of the original target.
The coefficient/cutoff scan in this paragraph still needs a six-row Lean
wrapper before it can enter `proofs.yaml` or `attestations.json`.

## 7. Pseudo-witness search and falsification replay

No target-size short-window pseudo-witness was found.

The exhaustive exact `k=5`, owners `(1,2,3)` residual search through
`X_1<=200,000` tests `159,959` admissible loss values. It finds `38`
short-window tuples satisfying every local and composed second/third/fourth
divisibility. The largest has

```text
(P,Q,R)=(4,3,11),   g=87,   d=11,484,
(X_1,X_2,X_3)=(151,728,151,731,151,734),
(a,b,c)=(9,483,16,859,1,254),
n=54,403.
```

Every survivor is below `10^120` and fails the block equation. Thus the
short fourth-lift system is genuinely nonempty below the cutoff; no vacuity
argument is available.

The independent target-size Hensel reconstruction with

```text
k=5, (i,j,l)=(1,2,4),
(P,Q,R)=(101^20,103^20,107^20), g=1
```

has a 121-digit gap and satisfies every local and composed lift through
fourth order, together with (7), (8), and (12). It fails the upper short
window by hundreds of quotient digits and fails the exact block equation.
It remains a valid falsifier of congruence-only closure, not a counterexample
to Erdős 686.

Boundary replay:

- owner components `2` and `3` occur together in the exact short fixture
  `(P,Q,R,g,d)=(3,5,2,24,720)`;
- all center and reflected triples occur in the coefficient scan;
- the genuine `d=1` telescopes `(k,n,d)=(9,2,1),(15,4,1)` reproduce and lie
  outside the target-size three-component slice;
- no `native_decide`, `sorry`, `admit`, new axiom, or unsafe declaration is
  used.

## 8. Exact remaining gap

For each target row, exclude positive integers

```text
d,g,P,Q,R,a,b,c
```

and signed integers `z_i,z_j,z_l` satisfying all of:

```text
d >= 10^120,        d=gPQR,         1<=g<=G_k,
P,Q,R>1 pairwise coprime,

aP^2-bQ^2=3(i-j),   aP^2-cR^2=3(i-l),
5d<aP^2,bQ^2,cR^2<A_k d,

O_s != 0,           P_s|O_s,
T_s=P_s^2 z_s,
P_s^3 | 3a_u a_v T_s + P_s^2 J_s,

P_s | 27C_s^2 a_u a_v z_s + K_s g^4,
gcd(P_s,z_s) | K_s g^4,
gcd(P_s,a_u) | 3|s-u|,
5|z_s| < B_s g^2 a_s,

sum_s w_s P_s^2 z_s = g^2 Gamma,
```

cyclically at the three owners, together with the two-zero placement
exclusions in section 6. This quantified lemma omits `n` and the block
equation, so it is stronger than the equation-specific exactly-three-owner
slice. It remains unproved. The live alternatives are the all-nonzero and
one-zero quotient branches, center-containing multi-zero branches, and the
282 surviving noncentral two-zero placements in row 15.

## 9. Reproduction

```bash
python3 -m pytest \
  compute/campaign686/test_short_window_quotient_attack.py -q
python3 compute/campaign686/short_window_quotient_attack.py --pretty
python3 compute/campaign686/short_window_quotient_attack.py \
  --search-limit 5000000
lake build ErdosProblems.Erdos686ShortWindowQuotient
lake env lean ErdosProblems/Erdos686ShortWindowQuotientAudit.lean
```

