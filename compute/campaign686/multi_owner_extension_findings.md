# Erdős 686 multi-owner extension

Status: **generic finite-family second/third composition proved; target-size
zero obstruction excluded uniformly for 4 through 15 owners; the nonzero
branch remains open and the direct size/selection routes are falsified.**

This checkpoint uses the original loss `g`.  No omitted cleaned component is
absorbed into a larger loss.

## Frozen producer artifacts

```text
ErdosProblems/Erdos686MultiOwnerExtension.lean
  eb1672572473b14ab4ffb19a15573e577afa5e6fba093e6559fa781bc7ac051c
compute/campaign686/multi_owner_extension_verify.py
  23c3b0c480278390cbb4d0286221f31862268e0dd9ca3c7771bf19179dadc2d1
compute/campaign686/test_multi_owner_extension_verify.py
  4da0d02ccf15838acb1a3cc25d7656974699c6ec2f50816f0e594d718b5fb97b
docs/plans/2026-07-10-erdos686-multi-owner-extension.md
  d20c7ffe82b6601bc0d8340297d661ed694a887fe3750d6d23a1cc3d28e42b53
```

No shared import registry, theorem manifest, audit root, three-owner
extraction file, or zero-exclusion producer file was changed.

## Exact finite-family algebra

Let `S` be a finite set of `t >= 3` distinct owner indices.  For every
`s in S`, let `P_s` be its cleaned component and `a_s` its positive residual
cofactor.  Assume

```text
d = g * product(P_s, s in S),
X_s = a_s P_s^2,
X_s - X_u = 3(s-u).
```

Put

```text
A       = product(a_s, s in S),
Delta_s = product(s-u, u in S, u != s),
r       = t-1.
```

The opposite square residual product satisfies the kernel-checked
congruence

```text
product(a_u P_u^2, u != s)
  = (-3)^r Delta_s                         (mod P_s^2).       (1)
```

If the second local lift at `s` is

```text
P_s | 3 C_s a_s - 4 D_s (g product(P_u,u!=s))^2,
```

then Lean proves

```text
P_s | O_s,
O_s = 3 C_s A - 4 D_s g^2 (-3)^r Delta_s.                  (2)
```

If the third local lift is

```text
P_s^2 | -3[3 C_s a_s - 4 D_s (g product(P_u,u!=s))^2]
          + 20 E_s P_s (g product(P_u,u!=s))^3,
```

then Lean proves

```text
P_s^2 | F_s,
F_s = -3 O_s + 20 E_s g^2 d (-3)^r Delta_s.                (3)
```

No primality, positivity, coprimality, or block equation is used in the
algebraic proofs of (1), (2), and (3).  The finite-family decomposition is the
only interface they require.

## Uniform zero exclusion

For an exact multiplier-four target-row solution, the banked inequality
`2d < n` gives

```text
X_s = 3(n+s)-d > 5d                                      (4)
```

at every positive owner.  From `d=g product(P_s)` and
`X_s=a_s P_s^2`, Lean proves

```text
g^2 (5d)^t < A d^2.                                      (5)
```

For `t>=4` and `d>=10^120`, (5) implies

```text
K g^2 < A,
K = 4*10^12*3^14*15^14 + 1
  = 558515440794946289062500000000000001.                 (6)
```

For owners in `[1,15]`, Lean also proves

```text
|Delta_s| <= 15^r <= 15^14.                               (7)
```

The target coefficient table supplies `C_s != 0` and `|D_s|<10^12`.
Consequently

```text
|4 D_s (-3)^r Delta_s| < K.                               (8)
```

If `O_s=0`, taking absolute values in (2) gives

```text
3 |C_s| A = |4 D_s (-3)^r Delta_s| g^2 < K g^2,
```

contradicting (6).  The public theorem
`target_multi_owner_second_obstruction_ne_zero` packages (4) through (8) as
explicit hypotheses and proves `O_s != 0` for every `4<=t<=15`.  The proof
does not use the numerical loss ceiling `g<=G_k`; `g>0` suffices because it
cancels on the two sides of the zero equation.

This zero exclusion is strictly weaker than the target.  It says only that
each divisibility in (2) has a nonzero right-hand side.

## Exact target-row scan

The independent verifier enumerates every owner subset of cardinality 4
through `k` in all six rows:

```text
42,274 owner subsets,
309,329 owner slopes,
154,654 positive zero slopes.
```

The maximum positive zero slope `A/g^2` is

```text
1,807,743,205,183,749,120.
```

Every positive slope is below the equation-level lower bound
`5^t * 10^(120(t-2))`, independently reproducing the kernel zero exclusion.

The three-owner statement “at most one obstruction can vanish” does **not**
generalize.  Exactly 327 multi-owner subsets have a repeated positive slope;
the maximum multiplicity is two.  The smallest explicit example is

```text
k=5, S={1,2,4,5},
zero slopes at two reflected owners = 900.
```

This collision does not threaten the target-size result because each
individual zero is already excluded by (4) through (8).  It does rule out
reusing the three-owner pairwise-slope argument as stated.

The signed algebra grid checks 384 loss fixtures across 48 owner families,
including negative losses and losses divisible by 2 and 3.  All 2,776 owner
congruence checks reproduce both (2) and (3).

## Why the nonzero branch does not close by size

The short window `X_s < R_k d`, with `R_k<=35`, gives exactly

```text
A < R_k^t g^2 d^(t-2).                                   (9)
```

Using `|C_s|,|D_s|<10^12`, `t<=15`, and (7), equations (2) and (9) give the
uniform explicit estimate

```text
|O_s| < B g^2 d^(t-2),
B = 3*10^12*35^15 + 4*10^12*3^14*15^14
  = 993167678643731689453125000000000000.                 (10)
```

Since `O_s != 0` and `P_s | O_s`, (10) yields only

```text
P_s < B g^2 d^(t-2).
```

Multiplying this over all `t` owners compares `d/g=product(P_s)` with a
quantity of degree `t(t-2)` in `d`.  The exponent excess over the left side
is

```text
t(t-2)-1 = 7,14,23,34,47,62,79,98,119,142,167,194
```

for `t=4,5,...,15`.  Thus the direct nonzero-divisor size argument becomes
strictly weaker as owner count grows.  This is an exact quantified failure,
not a proof that every possible use of (2) and (3) is dead.

## Why selecting three buckets does not repair the loss

After sorting `4<=t<=15` components, product averaging guarantees at most

```text
product(largest three) >= (d/g)^(3/t) >= (d/g)^(1/5),
product(complement)    <= (d/g)^(4/5).
```

The complement is not bounded.  An exact product-and-window counterfamily is

```text
P_1=2^N, P_2=3^N, P_3=5^N, P_4=7^N, g=1, d=210^N.
```

The components are pairwise coprime, every `P_i^2<=d`, and the complement to
the largest three is `2^N`.  Therefore a three-bucket extraction cannot feed
the existing bounded-loss lemma unless it proves new arithmetic control of
the complement; product pigeonhole and square-size bounds alone do not do
so.

## Four-owner congruence-only falsifier

The verifier constructs the exact deterministic fixture

```text
k=5,
S=(1,2,4,5),
(P_1,P_2,P_4,P_5)=(101^16,103^16,107^16,109^16),
g=1,
d=(101*103*107*109)^16=121330189^16.
```

The gap has 130 decimal digits.  CRT first places the four residuals in one
step-three square progression.  It then solves the free progression
parameter modulo each `P_s^2` so that every third local lift vanishes.  The
resulting exact `n` is printed in the JSON report and has 517 decimal digits.
Direct integer evaluation verifies, at every selected owner,

```text
P_s | n+s,
P_s^2 | X_s,
the second local congruence,
the third local congruence,
P_s | O_s,
P_s^2 | F_s.
```

The block equation is false and the short window is false.  This is not a
counterexample to Erdős 686.  It falsifies only the proposed implication
“four or more square residual owners plus all second/third local congruences
force a bounded gap.”

## Dependency tree and verdicts

```text
target_multi_owner_second_obstruction_ne_zero
|- multi_owner_target_cofactor_product_gt_zero_bound
|  `- multi_owner_cofactor_product_scaled_lower
|     |- d = g product(P_s)
|     `- every a_s P_s^2 > 5d
|- multi_owner_delta_natAbs_le_pow
|- multi_owner_zero_coefficient_natAbs_lt
`- bounded_multi_owner_second_obstruction_ne_zero

multi_owner_third_obstruction_dvd_sq
|- multi_owner_opposite_product_sub_dvd_sq
|  `- multi_owner_opposite_product_modeq_sq
|- d = g P_s product(P_u,u!=s)
`- the assumed third local lift
```

- Finite-product congruence: **PASS.**  Every factor is replaced modulo
  `P_s^2` before multiplication; no cancellation or coprimality is used.
- Second composition: **PASS.**  The proof multiplies the local lift by all
  opposite cofactors and adds a multiple of the product difference in (1).
- Third composition: **PASS.**  The cubic term is exactly
  `g^2 d product(a_u P_u^2,u!=s)`; the correction from the exact product to
  `(-3)^r Delta_s` is still divisible by `P_s^2`.
- Original loss: **PASS.**  Every theorem uses the supplied `g`; there is no
  replacement `g * product(unselected components)`.
- Zero exclusion: **PASS for the stated full finite-family interface.**  The
  lower bound and coefficient ceiling are kernel-checked with all constants
  displayed above.
- Full target closure: **FAIL / not claimed.**  Nonzero obstructions have the
  growth in (10), and the CRT fixture proves that the congruences alone do
  not enforce the short window.

## Exact remaining gap

For a target-size solution with a complete bounded-loss owner decomposition,
all composed second obstructions are now known to be nonzero.  What remains
is to rule out the simultaneous system

```text
P_s | O_s,
P_s^2 | F_s,
5d < a_s P_s^2 < R_k d,
d = g product(P_s),
1 <= g <= G_k,
```

for at least three nontrivial pairwise-coprime owner components.  The
four-owner CRT fixture shows that deleting the upper residual bound and the
exact block equation makes this statement false.  A closing lemma must use
one of those two inputs quantitatively; another bounded-resultant argument
from (2) and (3) alone cannot work.

## Reproduction

```bash
python3 -m pytest compute/campaign686/test_multi_owner_extension_verify.py -q
python3 compute/campaign686/multi_owner_extension_verify.py --pretty
lake env lean ErdosProblems/Erdos686MultiOwnerExtension.lean
```

The focused Python suite has 6 passing tests.  `#print axioms` for all ten
public Lean theorems reports exactly the allowed subset
`[propext, Classical.choice, Quot.sound]`.  The source contains no executable
`sorry`, `admit`, `native_decide`, `axiom`, or `unsafe` declaration.
