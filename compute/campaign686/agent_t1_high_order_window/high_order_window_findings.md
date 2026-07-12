# Erdős 686 Target 1: sixth/seventh lift with the exact short window

Date: 2026-07-12

Status: **the two next local orders are exact and quantitatively audited, but
they do not close any of the 6,156 generic ordered owner views.**  Sixth order
does force a nonzero cyclic obstruction in every one of the 6,210 views.
Its modulus-to-size consequence is nevertheless much weaker than the already
banked residual bound.  Seventh order has the same cubic archimedean scale;
its only fixed leading determinant is mixed in every exact window cell.

No Lean file is supplied because the calculation produces no cutoff and no
new reduction of the open target.  The exact symbolic and integer verifier is
`high_order_window_verify.py`, with six focused tests.

## 1. Exact local orders

Write `P` for the owner component, `M=gQR=d/P`, `aP^2` for its local
residual, and

```text
C,D,E,F,G,H,I
```

for degrees zero through six of the signed local cofactor polynomial.  If
`L=P X` and `3X-M=aP`, the exact reduced local equation is

```text
T = -Ca + sum_{r>=1} c_r P^(r-1)
       ((X+M)^(r+1)-4X^(r+1)).
```

Substituting `X=(M+aP)/3` and clearing the exact powers of three gives the
next two truncations:

```text
L6 = 3 L5 + P^4[-27Ea^3 +216FM^2a^2 +1260GM^4a +1364HM^6],

L7 = 3 L6 +60P^5M^3[30Ga^2 +102HM^2a +91IM^4].
```

The equation implies `P^5 | L6` and `P^6 | L7`.  The verifier derives both
identities symbolically from the cofactor polynomial, rather than fitting
coefficients, and independently checks 9,000 signed exact evaluations.  The
grid includes 3,000 cases with `|P|=3`.  For `k=5`, `H=I=0`; for `k=7`,
`I=1`.  These top-degree boundary cases are reconstructed literally.

## 2. Exact cyclic composition

For the other two cofactors put

```text
A=bc,  t=abc,  s=(i-j)+(i-l),  p=(i-j)(i-l).
```

Starting from the banked `W5`, exact expansion of

```text
(bQ^2)(cR^2)=9p-3asP^2+a^2P^4
```

gives

```text
W6 = 3A W5 +27P^4 K6,

K6 = -E t^3
     +g^2 t^2(12D-36Es+72Fp)
     +g^4 t(-1512Fps+3780Gp^2)
     +36828H g^6p^3,                                  (1)

W7 = 3W6 +1620P^5M g^2 K7,

K7 = t^2(E-4Fs+10Gp)
     +t g^2(-102Gps+306Hp^2)
     +2457I g^4p^3.                                   (2)
```

Thus the exact equation gives

```text
P^5 | W6,       P^6 | W7.                              (3)
```

The symbolic certificate proves that `W6` and `W7` are exactly the
remainders of `(bc)^3 L6` and `(bc)^3 L7` below `P^5` and `P^6`.  An
independent integer grid checks another 74,520 compositions, including
49,680 fixtures containing component `3` and 37,260 negative-loss fixtures.

## 3. The exact short-window scale

The equation-facing window already banked in the repository supplies, for
the row constants `L_k,U_k`,

```text
L_k d <= aP^2,bQ^2,cR^2 < U_k d,
d=gPQR,

(L_k)^3 g^2d <= t < (U_k)^3 g^2d,
bc < (U_k)^2 g^2P^2,       P^2 < U_k d.                (4)
```

The second line is exact: multiply the three residual inequalities and
cancel positive `d^2`; multiply the two opposite inequalities and use
`d^2=g^2P^2Q^2R^2`.

Let `u=W5/P^4`, which is integral under the equation.  Direct triangle
inequalities from the displayed `W5` give an explicit row/view constant
`B5` with

```text
|u| <= B5 g^4d^2/P^2.                                  (5)
```

Combining (1), (4), and (5), the verifier checks the strict inequality

```text
|27E| (L_k)^9 d^3
  > [27|12D-36Es+72Fp|(U_k)^6 +3(U_k)^2B5]d^2
    +27|-1512Fps+3780Gp^2|(U_k)^3d
    +27|36828Hp^3|                                      (6)
```

at `d=10^120`, in every ordered view.  Monotonicity then retains it for all
larger `d`.  Consequently

```text
W6 != 0,             sign(W6)=-sign(E),
P <= C6 g^6d^3.                                         (7)
```

This is a genuine sign theorem at the exact target scale, not a heuristic.
It does not help packing: (4) already gives `P^2<U_kd`, while (7) only gives
a first-power upper bound cubic in `d`.

The worst ratio of the right side of (6) to its leading side occurs at

```text
(k,i,j,l)=(9,2,8,9)
```

and is less than `2.174*10^-117`.  This decimal is descriptive only; the
verifier stores and compares the full exact numerator and denominator.

The exact maximum constants are:

| k | max `C6` | max `C7` | maximizing ordered view |
|---:|---:|---:|:---:|
| 5 | 31,560,952,364,928 | 100,027,008,273,024 | `(1,4,5)` |
| 7 | 8,384,712,940,911,852 | 28,628,149,403,395,476 | `(1,6,7)` |
| 9 | 8,267,780,888,046,475,884 | 28,938,775,634,195,758,452 | `(1,8,9)` |
| 11 | 2,758,680,169,612,813,899,360 | 10,222,338,381,756,931,051,200 | `(1,10,11)` |
| 13 | 1,139,429,210,761,041,601,828,608 | 4,433,315,607,240,657,742,318,464 | `(1,12,13)` |
| 15 | 1,168,644,904,444,759,933,478,206,080 | 4,518,604,044,513,372,125,636,553,600 | `(1,14,15)` |

Here `C7` is the exact triangle-inequality constant in

```text
|W7/P^4| <= C7 g^6d^3.                                  (8)
```

Whenever `W7!=0`, (3) and (8) give only

```text
P^2 <= C7 g^6d^3,                                       (9)
```

again strictly weaker than `P^2<U_kd`.  The verifier compares the exact
right sides at `d=10^120` and `g=G_k` in all six rows; the new bounds remain
weaker thereafter.

## 4. Seventh leading roots

Put the common exact short-window parameter

```text
lambda = t/(g^2d),       (L_k)^3 <= lambda < (U_k)^3.
```

After dividing `W7` by its visible `P^4`, its degree-three part is exactly

```text
g^6d^3 lambda^2[-81E lambda +1620B],
B=E-4Fs+10Gp.                                             (10)
```

Every `E` and every `B` is nonzero in all 6,210 ordered views.  The rational
root `lambda=20B/E` lies inside the retained exact window in 144 views and
outside it in 6,066 views.  The split by row is:

| k | ordered views | root inside | root outside |
|---:|---:|---:|---:|
| 5 | 60 | 4 | 56 |
| 7 | 210 | 24 | 186 |
| 9 | 504 | 0 | 504 |
| 11 | 990 | 16 | 974 |
| 13 | 1,716 | 56 | 1,660 |
| 15 | 2,730 | 44 | 2,686 |

All 144 inside-root views are among the 6,156 generic views.  None of the 54
center-reflected views has an inside root.  Outside the root interval, exact
endpoint separation and the explicit `O(d^2)` remainder prove that (10)
fixes the sign already at `10^120`.  Inside it, rational approximation at
denominator `g^2d` can make the degree-three term only `O(d^2)`, so no
uniform sign follows from seventh order.

## 5. The leading determinant is everywhere mixed

For one unordered owner triple, the three rows `(E_s,B_s)` have rank two in
all 1,035 cases.  Let `w` be their primitive cross product.  It cancels both
degree-three structures in (10):

```text
sum_s w_s E_s = 0,       sum_s w_s B_s = 0.             (11)
```

The verifier partitions each interval `[(L_k)^3,(U_k)^3]` at all exact
rational roots `20B_s/E_s`.  This gives 1,105 exact lambda cells.  In every
one of them the nonzero weighted leading terms

```text
w_s[-E_s lambda+20B_s]
```

have both signs:

```text
mixed open cells          1,105
one-sided open cells          0
mixed rational boundaries 2,138
all-zero boundaries           2
one-sided boundaries           0.
```

There are 33 zero primitive weights, 33 equal-root pairs, and only two equal
root pairs inside the window; those give the two all-zero boundaries.  The
minimum separation of unequal roots is exactly `800/789`.  Thus the only
coefficient-only determinant available at orders six/seven cancels its
leading terms but leaves a mixed quotient lattice, including at every root
boundary.  It cannot supply the missing one-sided magnitude or packing cutoff.

## 6. Verdict and boundary audit

- **All 6,156 generic ordered views:** sixth order is nonzero but its bound
  is weaker than the existing square bound; seventh order has no packing
  gain and 144 leading-root cells.
- **All 54 center-reflected views:** included; none has a seventh leading
  root in the window.  Their separate endpoint-third determinant remains the
  stronger specialized route.
- **Components 2 and 3:** exact composition fixtures include both; no
  inverse of 2 or 3 is used.
- **Top cofactor degrees:** the zero coefficients at `k=5` and the monic
  degree-six coefficient at `k=7` are checked explicitly.
- **Signed algebra:** negative components, opposite quotients, cofactors, and
  losses occur in the local and composition grids.
- **Hensel flexibility:** the new two digits do not alter the fixed-depth
  mechanism already exhibited by the fifth-order target-scale family.  A
  target-scale *window-respecting* pseudo-fixture was not found; none is
  claimed.

The precise result is negative: orders six and seven are algebraically valid,
but their modulus grows more slowly than their exact cubic archimedean
correction, and their only fixed leading determinant has no one-sided cell.
Pushing to order eight by the same route would introduce another quotient
and is not justified by these data.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_t1_high_order_window/high_order_window_verify.py \
  --pretty

PYTHONPATH=. PYTHONDONTWRITEBYTECODE=1 pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t1_high_order_window/test_high_order_window_verify.py
```
