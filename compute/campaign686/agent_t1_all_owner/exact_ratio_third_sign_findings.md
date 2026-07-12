# Erdős 686 Target 1: exact-window third-obstruction nonvanishing

Status: **proper new restriction, kernel-checked; Target 1 remains open.**

The previous three-bucket quotient scan used only

```text
5d < X_s < A_k d.
```

The exact equation supplies a sharper input that had not been composed with
that scan: the ratio window pins `n+1` to a width-`k` band.  Exact rational
root brackets turn this into a uniform residual floor.  Together with the
cleaned factorization, that floor makes the leading cofactor-product term of
every composed third obstruction dominate both correction terms.

Consequently:

1. in a supplied exactly-three cleaned-bucket factorization of a target
   equation, **all three composed third obstructions are nonzero**; and
2. on the complete all-owner grid, **every composed third obstruction is
   nonzero**, including at unit buckets.

This removes the one-zero and multi-zero third-quotient branches.  It does
not close the simultaneous all-nonzero lattice cancellation.

## Exact ratio bridge

For each target row use `B=100000` and the strict upper brackets

| `k` | `A/B > 4^(1/k)` | `H=A-B` | `R=4B-A-1` | floor `L_k` |
|---:|---:|---:|---:|---:|
| 5 | 131951/100000 | 31951 | 268048 | 8 |
| 7 | 121902/100000 | 21902 | 278097 | 12 |
| 9 | 116653/100000 | 16653 | 283346 | 15 |
| 11 | 113432/100000 | 13432 | 286567 | 20 |
| 13 | 111254/100000 | 11254 | 288745 | 23 |
| 15 | 109683/100000 | 9683 | 290316 | 29 |

Exact integer arithmetic checks

```text
4 B^k < A^k.
```

The upper ratio-window inequality then gives

```text
B d < (A-B)(n+k).
```

For `i in [1,k]`, put `X_i=3(n+i)-d`.  Since

```text
3(A-B)(k-i) < 10^120 <= d,
```

the preceding linear inequality gives the strict bound

```text
R d < H X_i,
```

and the table checks `H L_k <= R`.  Therefore

```text
L_k d <= X_i
```

for every target-row owner.  Lean proves this directly from the block
equation; no real-number root or asymptotic estimate enters the theorem.

## Exactly-three domination

For distinct owners `i,j,l`, write

```text
X_i=aP^2,  X_j=bQ^2,  X_l=cR^2,  d=gPQR.
```

Multiplying the three residual floors and cancelling positive `d^2` gives

```text
L_k^3 g^2 d <= abc.                                    (1)
```

At owner `i`, with `delta=(i-j)(i-l)`, the composed third obstruction is

```text
T_i = -9 C_i abc
      + 180 E_i g^2 delta d
      + 108 D_i g^2 delta.                              (2)
```

An ordinary-kernel Boolean certificate and an independent Python scan check,
for all 6,210 ordered distinct target triples,

```text
180 |E_i delta| < 9 |C_i| L_k^3,

108 |D_i delta|
  < 10^120 (9 |C_i| L_k^3 - 180 |E_i delta|).          (3)
```

The minimum first margin in (3) is `14832`, at
`(k,i,j,l)=(5,3,1,5)`.  Equations (1)--(3) make the leading term in (2)
strictly larger in absolute value than the two corrections, so `T_i != 0`.
Cyclic relabeling gives all three owners.

The equation-facing Lean headline is

```text
exactRatio_target_three_bucket_all_third_obstructions_nonzero.
```

## Complete-grid domination

For a finite owner family of cardinality `4..15`, the existing exact
cofactor-product lower bound supplies enough extra powers of `d` to dominate
the linear-in-`d` third correction.  The explicit uniform coefficient is

```text
multiOwnerThirdCoefficientBound
  = 56 * 10^12 * 3^14 * 15^14 + 1.
```

The kernel proof establishes

```text
multiOwnerThirdCoefficientBound * g^2 * d
  < product_s a_s,
```

and bounds the correction coefficient by the left coefficient times `d`.
The equation-facing complete-grid headline is

```text
exactRatio_allOwner_third_obstruction_ne_zero.
```

No prime, component, or factor of `3` is cancelled in either proof.

## Exact sign-cell audit

The same strict domination externally fixes

```text
sign(T_i) = -sign(C_i).
```

Reconstructing the primitive lattice independently for all 1,035 unordered
triples gives:

```text
mixed cells     1035
one-sided cells    0
```

Thus the sharper ratio window eliminates all quotient-zero boundaries, but
it does **not** make the weighted lattice one-sided.  This is an explicit
negative result against treating the new nonvanishing theorem as closure.

## Boundary replay

- The genuine `(k,n,d)=(9,2,1),(15,4,1)` telescopes reproduce exactly and
  fail the premise `10^120<=d`.
- The 121-digit exactly-three CRT reconstruction still satisfies its local
  and composed congruences, but fails both the block equation and the coarse
  upper residual window.  It does not contradict the equation-facing result.
- The 130-digit four-owner CRT reconstruction likewise satisfies its local
  and composed congruences while failing the equation and upper window; it is
  also outside the exactly-three theorem.
- Unit buckets, bases `2` and `3`, center owners, and endpoints are retained.

## Exact remaining gap

In the exactly-three slice, only the **all-three-nonzero** quotient branch
remains.  The existing two-small-weighted-component statement may now be
restricted to this branch, but it is still unproved.  The exact sign audit
shows that coefficient signs alone cannot prove it: all 1,035 equation-side
cells remain mixed.

On the complete grid, every second and third composed obstruction is now
nonzero.  The remaining task is still to extract a target-size contradiction
from their simultaneous divisibilities and the exact short window; merely
restating that joint implication would be target-strength.

## Reproduction

```bash
lake build ErdosProblems.Erdos686ThirdObstructionNonzero \
  ErdosProblems.Erdos686ExactRatioThirdSign

PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_t1_all_owner/exact_ratio_third_sign_verify.py

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t1_all_owner/test_exact_ratio_third_sign_verify.py
```

The focused build completed `8,267` jobs.  Every printed new theorem surface
uses only `[propext, Classical.choice, Quot.sound]`.
