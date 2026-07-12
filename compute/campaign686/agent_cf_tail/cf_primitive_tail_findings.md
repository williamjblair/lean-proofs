# Erdős 686 Target 1: primitive-scale CF tail findings (historical e166 checkpoint)

> **Historical checkpoint.**  This document and its `e166` artifacts preserve
> the first certified extension from `10^120` to `10^166`.  The canonical
> `Erdos686CFTailBandCert` and `Erdos686CFTailBand` modules have since been
> regenerated at `10^1000`; see `../agent_cf_tail_e1000/findings.md`.  Every
> “remaining gap at `10^166`” statement below describes this frozen checkpoint,
> not the current frontier.

Status: a new finite part of the nominal odd tail is excluded for all six
rows.  The proof below gives

```text
k in {5,7,9,11,13,15},  10^120 <= d < 10^166
    ==> B(k,n+d) != 4*B(k,n).
```

At this historical checkpoint, the scale arithmetic and both named telescope fixtures were Lean-banked in
`ErdosProblems/Erdos686CFTailScale.lean`.  Six generated Stern–Brocot trees
and the combined bounded-band theorem are kernel-banked in
`ErdosProblems/Erdos686CFTailBandCert.lean` and
`ErdosProblems/Erdos686CFTailBand.lean`.  This is a fully Lean-verified
finite-band theorem, not a claim that `OddThueTailHypothesis` is proved.

Reproduce:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_cf_tail/test_cf_primitive_tail_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_cf_tail/generate_e166_certificates.py
lake build ErdosProblems.Erdos686CFTailScale \
  ErdosProblems.Erdos686CFTailBandCert
lake env lean ErdosProblems/Erdos686CFTailBand.lean
```

## 1. Primitive scale and its constant coefficient

Let `k=2r+1`, and for a hypothetical solution put

```text
X = n+d+r+1,  Y = n+r+1,
g = gcd(X,Y),  X=g*u,  Y=g*v,  z=g^2,
A_j = 4*v^j-u^j.
```

Then `gcd(u,v)=1` and `d=g(u-v)`.  Since

```text
P_k(T)=sum_{j=0}^r (-1)^j e_j T^(k-2j),
```

where `e_j` is the `j`th elementary symmetric function of
`1^2,...,r^2`, the exact centered equation is

```text
Q_k(z) = sum_{j=0}^r (-1)^j e_j A_(k-2j) z^(r-j) = 0.       (1)
```

All terms except the last are divisible by `z`; hence

```text
z | e_r*A_1 = (r!)^2*(4v-u).                               (2)
```

This is the global primitive-scale form of the center cubic lift.  The
kernel theorem `scale_constant_dvd` isolates the cancellation needed for
(2).

The ratio is on the lower side of `alpha=4^(1/k)`: for `T>r`,

```text
P_k(T)/T^k = product_{j=1}^r (1-j^2/T^2)
```

is strictly increasing.  Since `X>Y>r` and `P_k(X)=4P_k(Y)`, one gets
`(X/Y)^k<4`.  In particular `v<u<2v`, so

```text
0 < A_1 < 3v.
```

Because a positive divisor is at most its positive multiple, (2) gives

```text
g^2 <= (r!)^2*A_1 < 3(r!)^2*v.
```

Together with `d=g(u-v)<gv`, this yields the explicit denominator bound

```text
d^2 < 3(r!)^2*v^3.                                         (3)
```

For the six rows, `(r!)^2 <= (7!)^2=25,401,600`, so the coefficient in
(3) is at most `76,204,800`.  If `d>=10^120` and `v<10^77`, then

```text
10^240 <= d^2
         < 76,204,800*v^3
         < 76,204,800*10^231
         < 10^240,
```

a contradiction.  Thus every target-size solution satisfies

```text
v >= 10^77.                                                (4)
```

The Lean dependency is

```text
scale_constant_dvd
  -> gap_sq_lt_of_scale_constant
  -> primitive_denominator_ge_ten_pow_77
  -> primitive_denominator_ge_ten_pow_77_of_scale_constant.
```

All four surfaces pass the required axiom gate.

## 2. Signed scale remainder and the uniform floor pin

Write the positive terms of (1) as

```text
T_j = e_j*A_(k-2j)*z^(r-j).
```

For every reduced CF candidate in the range (4), the verifier checks
exactly

```text
2*e_2*A_(k-4) < e_1*A_(k-2),                              (5)
e_j*A_(k-2j) > e_(j+1)*A_(k-2j-2)   for 2 <= j < r.       (6)
```

Since `z>=1`, (6) makes `T_2,T_3,...,T_r` strictly decreasing.  Therefore
the alternating tail

```text
R = T_2-T_3+T_4-...+(-1)^r T_r
```

satisfies `0<R<T_2`.  Equation (1) becomes the signed integer identity

```text
z^(r-1) * (e_1*A_(k-2)-z*A_k) = R.                        (7)
```

Conditions (5), `R<T_2`, and (1) imply

```text
e_2*A_(k-4) < z*A_k,
```

and hence `R<z^(r-1)A_k`.  Applying the kernel theorem
`floor_pin_of_signed_remainder` to (7) gives

```text
z*A_k < e_1*A_(k-2) < (z+1)*A_k,
z = floor(e_1*A_(k-2)/A_k).                               (8)
```

Thus a genuine solution has one possible scale for each reduced pair, and
that integer must be a square.  The coefficient rows used in the exact
checks are

| k | `(e_0,...,e_r)` |
|---:|---|
| 5 | `1,5,4` |
| 7 | `1,14,49,36` |
| 9 | `1,30,273,820,576` |
| 11 | `1,55,1023,7645,21076,14400` |
| 13 | `1,91,3003,44473,296296,773136,518400` |
| 15 | `1,140,7462,191620,2475473,15291640,38402064,25401600` |

This extends the previous `k=5` floor pin uniformly to the finite CF tail
range for every target row.

## 3. Exact CF confinement through row 340

The independent scale script reads the checked-in 341-row artifact for each
`k`.  It
recomputes, with integers only:

1. every declared difference `p_m^k-4q_m^k` and its alternating sign;
2. every adjacent determinant;
3. every CF recurrence using the declared next partial quotient;
4. the exact sign crossing at the next semiconvergent;
5. the SHA-256 of each source artifact.

For a reduced fraction `u/v` with

```text
|alpha-u/v| <= C/(g^2*v^2) <= C/v^2,
```

the verified self-contained confinement theorem gives, in the unique window
`q_m<=v<q_(m+1)`, exactly one of

```text
(u,v)=(p_m,q_m),
(u,v)=a(p_(m+1),q_(m+1))-t(p_m,q_m),
(u,v)=s(p_m,q_m)-a(p_(m+1),q_(m+1)),
```

with the explicit coefficient/window inequalities implemented in
`confinement_candidates`.  The enumeration is a superset because it retains
nonreduced and wrong-side pairs until later exact filters.

For every reduced below-side pair with `v>=10^77`, the script checks (5)-(6),
computes the unique floor (8), requires it to be a square, checks the
constant divisibility (2), and finally evaluates the complete scale
polynomial (1).  The exact counts are:

| k | candidates | below | reduced | `v>=10^77` | positive floor | square floor | square, `g>=2` | constant pass | exact roots |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 433 | 219 | 219 | 118 | 64 | 38 | 2 | 37 | 0 |
| 7 | 529 | 267 | 267 | 154 | 115 | 64 | 5 | 63 | 0 |
| 9 | 648 | 316 | 297 | 183 | 136 | 81 | 14 | 79 | 0 |
| 11 | 853 | 422 | 393 | 211 | 165 | 94 | 14 | 93 | 0 |
| 13 | 996 | 495 | 458 | 266 | 204 | 114 | 20 | 114 | 0 |
| 15 | 1217 | 596 | 533 | 281 | 217 | 120 | 23 | 120 | 0 |

All nontrivial square candidates that also pass (2) are pure convergents,
as independently predicted by the `C/g^2<1/2` branch when `g>=2`.  Every one
has nonzero full scale residual.

Independently, `generate_e166_certificates.py` invokes the repository's
exact Farey-tree generator at exponent 166 for every row.  The six trees
have respectively

```text
k=5:   5,449 nodes,   415 candidate pairs
k=7:  10,027 nodes,   620 candidate pairs
k=9:   7,243 nodes,   767 candidate pairs
k=11: 14,689 nodes, 1,026 candidate pairs
k=13:  6,049 nodes, 1,104 candidate pairs
k=15:  6,547 nodes, 1,312 candidate pairs.
```

The generator rechecks the exact Boolean semantics independently before
emission.  The combined Lean module evaluates all six trees with ordinary
kernel `decide`.

## 4. Conversion to the new gap band

The weakest banked lower ratio among the six rows is the `k=15` inequality

```text
109651*v < 100000*u.
```

It applies here because `d>=10^120` and the already-proved
`d<3(n+1)` puts every row far above its small ratio threshold.  Since
`11*9651-100000=6161>0`, it gives

```text
v < 11(u-v) <= 11d.                                      (9)
```

The theorem `primitive_denominator_lt_eleven_gap` is the kernel proof of
(9).  If `d<10^166`, then `v<11*10^166`.  The smallest final denominator
among the six row-340 artifacts is

```text
q_340(k=15) =
447866243993625241004518869049693492059946478840651857213278178744259507472006710950566016848310118389668638874763495124866111366159576344138264180961901118054616144769,
```

which is greater than `11*10^166`.  Thus the exact enumeration contains the
reduced pair of every hypothetical solution in `10^120<=d<10^166`; its
zero-root result is the desired contradiction.  More directly at kernel
level, the generated Farey trees use the banked row bounds
`Y<=QHI*10^166` and prove all six row theorems.  Their exact assembly is

```lean
theorem no_odd_target_gap_solution_below_e166
    {k n d : ℕ} (hk : k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ))
    (hd : 10 ^ 120 ≤ d) (hB : d < 10 ^ 166) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n
```

and its axiom report is a subset of
`[propext, Classical.choice, Quot.sound]`.

## 5. Mandatory telescope audit

The two exact fixtures are retained:

```text
k=9:  (u,v,g,z,d)=(8,7,1,1,1),
k=15: (u,v,g,z,d)=(13,12,1,1,1).
```

Both have floor value `z=1` and full scale residual zero.  The `k=15`
fixture does not satisfy the deliberately stronger large-denominator
condition (5), which is why the verifier records that condition separately
from the actual floor identity.  Both have `d=1<k`; Lean checks the two
finite block identities with ordinary `decide` and separately proves they
are outside the disjoint-block domain.  No boundary fixture is discarded.

## 6. Exact remaining gap at this historical checkpoint

The full infinite tail was not closed.  At this checkpoint, the single exact
remaining Target 1 lemma was

```text
forall k in {5,7,9,11,13,15}, forall n d,
  10^166 <= d -> B(k,n+d) != 4*B(k,n).                    (10)
```

In CF language, (10) requires controlling confinement windows beyond the
last checked convergent.  Merely generating more finite CF rows moves the
cutoff but cannot prove (10); an infinite signed-remainder or denominator
argument is still required.  No irrationality measure, Baker bound, or
target-equivalent genus claim is used here.
