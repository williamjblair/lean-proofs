# Erdős 686 Target 1: joint all-owner resultant audit

Status: **exact negative result; no new Lean theorem and no Target 1 closure.**

The simultaneous full-owner divisibilities do produce a global
product-square-divisible Vandermonde determinant.  Exact elimination shows,
however, that this is the unique determinant of its type, that it cannot
remove the common cofactor product, and that on the full owner grid it is
exactly the third-order truncation already present in the block equation.
After the equation is imposed, its apparent stronger divisibility is
automatic from the fourth-order tail.

## 1. Exact system

For the complete grid `I={1,...,k}`, put

```text
X_i = alpha + 3i = a_i P_i^2,
M   = product_i P_i = d/g,
A   = product_i a_i.
```

Let `C_i,D_i,E_i` be the coefficients of degrees `0,1,2` in

```text
product_{j != i} (z+j-i).
```

For odd `k`, the signed owner delta equals `C_i`, so the banked third
obstruction has the exact form

```text
F_i = C_i H_i,
H_i = -9A + 3^(k-1) g^2 (12D_i+20E_i d),
P_i^2 | F_i.
```

The verifier reconstructs all coefficients from the product and matches all
60 target rows in the Lean tables.  It also checks `P_i^2|X_i` without
cancelling `C_i`, `3`, or any bucket factor.

## 2. The product-divisible resultant

For a subset `S={i_1,...,i_s}`, define

```text
L_S(h) = det [ h_i, X_i, i X_i, ..., i^(s-2) X_i ]_(i in S).
```

Multiplying the first entry in row `i` by
`C_S/C_i`, where `C_S=product_{i in S}C_i`, makes every entry in row `i`
divisible by `P_i^2`.  Hence

```text
product_{i in S} P_i^2 | C_S L_S(H).                 (1)
```

Exact column operations give

```text
L_S(1) = 3^(s-1) V_S,
V_S = product_{i<j in S}(j-i) != 0.                  (2)
```

Thus the `-9A` term survives every such resultant.

This is not an artifact of the chosen columns.  Over `Q`, the annihilator of

```text
(X_i i^r)_(i in S),  0 <= r <= s-2,
```

is one-dimensional.  A generator is

```text
lambda_i = 1 / (X_i product_{j != i}(i-j)),
```

and its moment on the common term is exactly

```text
sum_i lambda_i = (-3)^(s-1) / product_i X_i != 0.    (3)
```

Therefore every nonzero Vandermonde/resultant functional with auxiliary
columns `X_i q(i)`, `deg q<=s-2`, is a scalar multiple of this one and cannot
eliminate `A`.

## 3. Exhaustive subset and circuit scan

Every subset of size `4..k` was enumerated with exact integers:

| `k` | subsets | four-owner circuits | one-sided | zero-weight circuits |
|---:|---:|---:|---:|---:|
| 5 | 6 | 5 | 0 | 0 |
| 7 | 64 | 35 | 0 | 4 |
| 9 | 382 | 126 | 0 | 0 |
| 11 | 1,816 | 330 | 0 | 0 |
| 13 | 7,814 | 715 | 0 | 0 |
| 15 | 32,192 | 1,365 | 0 | 0 |
| **total** | **42,274** | **2,576** | **0** | **4** |

The raw four-owner parameter rows are `(C_i,C_iD_i,C_iE_i)`.  Under the
banked sign `sign(F_i)=-sign(C_i)`, every primitive circuit is mixed.  The
only dependent normalized coefficient triple is

```text
k=7, owners (2,4,6), primitive relation (3,-20,3).
```

It accounts for the four zero-coordinate circuits obtained by adding one of
owners `1,3,5,7`.  It gives no one-sided contradiction.

For every nonzero triple determinant `det[1,D_i,E_i]`, the owner
Vandermonde divides exactly.  The absolute quotient ranges are:

| `k` | minimum | maximum |
|---:|---:|---:|
| 5 | 50 | 350 |
| 7 | 980 | 244,020 |
| 9 | 40,824 | 629,342,784 |
| 11 | 22,302,720 | 4,383,765,492,480 |
| 13 | 28,268,697,600 | 67,621,441,024,051,200 |
| 15 | 24,115,553,280,000 | 2,022,760,403,369,072,640,000 |

The complete degree distributions for all 42,274 subsets are emitted by the
verifier.  On the full grids they reduce to

```text
deg_alpha L(D) = k-2,
deg_alpha L(E) = k-3.
```

## 4. Exact collapse to the block-equation tail

Write `e_r=e_r(X_1,...,X_k)` and `V=V_I`.  Exact polynomial comparison in
all six target rows gives

```text
L_I(D) = 3 V e_(k-2),
L_I(E) = 9 V e_(k-3).                                 (4)
```

Since `A M^2=e_k` and `M=d/g`, equations (2) and (4) imply

```text
M^2 L_I(H)
  = 3^k V [-3e_k + 12d^2 e_(k-2) + 60d^3 e_(k-3)].   (5)
```

But the exact block equation in residual coordinates is

```text
0 = product_i(X_i+4d) - 4 product_i(X_i+d)
  = -3e_k + 12d^2 e_(k-2) + 60d^3 e_(k-3)
    + sum_{r=4}^k (4^r-4)d^r e_(k-r).                 (6)
```

Thus the full resultant is precisely the degree-at-most-three truncation of
(6).  Under the equation,

```text
M^2 L_I(H)
  = -3^k V sum_{r=4}^k (4^r-4)d^r e_(k-r).            (7)
```

Equation (1) for the full grid appears to yield an `M^4` divisibility after
multiplying by `M^2`.  Equation (7) shows why it is empty: every term on the
right contains `d^4=(gM)^4`, hence already contains `M^4`.

The archimedean version fails for the same reason.  Both surviving terms in
`L_I(H)` have size `g^2 d^(k-2)`, while the modulus has size `d^2/g^2`.
The exponent excess is `k-4`, already `1` in the smallest row and increasing
thereafter.  For a proper subset, the certificate supplies no positive lower
bound on its bucket product; omitted owners may carry all nonunit mass.

## 5. Exact window-compatible boundary fixture

The verifier freezes the following full-grid algebraic fixture:

```text
k=5, n=25177, d=6790, g=97,
(P_1,...,P_5)=(2,7,5,1,1),
(X_1,...,X_5)=(68744,68747,68750,68753,68756),
(a_1,...,a_5)=(17186,1403,2750,68753,68756).
```

It satisfies, exactly:

- `d=g product P_i` and `g<=108`;
- pairwise-coprime buckets, including unit buckets;
- `8d<=X_i<14d` and the step-three progression;
- every `P_i|O_i`, `P_i^2|F_i`, `O_i!=0`, `F_i!=0`;
- every sign `sign(F_i)=-sign(C_i)`;
- every subset resultant (1) for `|S|=4,5`.

It fails exactly the two load-bearing target fields:

```text
blockProduct 5 (n+d) - 4 blockProduct 5 n
  = -7091705934067167000000 != 0,
d=6790 < 10^120.
```

This is not a counterexample to the equation-facing certificate.  It is a
hostile witness against cancelling unit buckets, assuming local algebra
implies the equation, or treating the resultant as a cutoff by itself.

The named `d=1` telescopes and the 121/130-digit Hensel fixtures are also
replayed.  The telescopes satisfy the equation but fail the target cutoff;
the Hensel fixtures satisfy their local/composed congruences but fail both
the upper residual window and the block equation.  No target-scale,
window-respecting pseudo-fixture was found or claimed.

## 6. Exact remaining gap

The resultant family studied here cannot close Target 1.  Any successful
joint-owner argument must use information outside the polynomial auxiliary
space

```text
span_Q { (X_i i^r)_i : 0<=r<=|S|-2 },
```

or must exploit a restriction on the quotient vector
`q_i=F_i/P_i^2` not present in `AllOwnerAssemblyThirdNonzeroCertificate`.
Restating such a restriction as an assumption would be target-strength.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_t1_all_owner_resultant/all_owner_resultant_verify.py \
  --compact

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t1_all_owner_resultant/test_all_owner_resultant_verify.py
```

The exact report digest at freeze time is
`2d68ac996adbf8ea8a258556d2f7360eb53d9eb6f6b0f9b71480a5f96d419080`.
The reconstructed 60-row coefficient-table digest is
`2d1a2713f61ec917998c03f2396ef4108e91be0f7fac3bc1625a3441ffa920e4`.
