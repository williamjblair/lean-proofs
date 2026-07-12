# Exact small-prime crossing band: findings

## Outcome

The small-prime valuation system does **not** close every exact crossing band:
four of the 294 structured rows below retain one valuation survivor.  The
proposed extension from a prime-power endpoint to an arbitrary lower position
is also false without a position correction.  Both failures are frozen below.

The corrected analysis yields four kernel-checked surfaces:

1. an exact any-position criterion with the split-factorial premise

   ```text
   v_p((k-1)!) <= v_p(4) + v_p((i-1)!(k-i)!);
   ```

2. an unconditional any-position corollary for every prime base `p>k`;
3. the stronger exclusion `n+i=a*p^A`, `a<=4`, `A>=1`, `p>k`;
4. the original all-prime endpoint theorem.

For every prime `p`, exponent `A`, and `1 <= k <= d < p^A`, the equation

```text
B(k, p^A-k+d) = 4 B(k, p^A-k)
```

is impossible.  Thus a quotient-four solution cannot have its lower block end
at a prime power.  More generally, no lower term can be a prime power whose
prime base exceeds `k`, regardless of its position.  For the target range
`k>=16`, the existing exact ratio-window bound supplies every interval
inequality used by these corollaries.

Lean source: `ErdosProblems/Erdos686SmallPrimeBand.lean`.

## Exact crossing band

For fixed `k,d>0`, the scanner finds the full necessary interval of `n` from

```text
(n+d+k)^k <= 4(n+k)^k,
4(n+1)^k <= (n+d+1)^k.
```

Both endpoints are found by monotone binary search over Python integers, and
the adjacent failing point is asserted.  No root, logarithm, decimal, or
floating-point approximation is used.

When `k>=3` and `d>=k`, this interval has exactly `k-1` integers.  To see this,
let `T` be the least positive integer `x` for which `(x+d)^k<=4x^k`.  The first
inequality starts at `n=T-k`; the second ends at `n=T-2`.  Equality at the
threshold is impossible: after reducing `(x+d)/x=a/b`, equality would give
`a^k=4b^k`, hence

```text
k (v_2(a)-v_2(b)) = 2,
```

which has no integer solution for `k>=3`.  The test suite reproduces the width
for every `3<=k<30` and `k<=d<=5k`.

## Valuation equations

For every prime `p`, the scanner independently computes

```text
v_p(B(k,n+d)) - v_p(B(k,n))
```

in two ways:

1. Legendre floor sums for the two factorial quotients;
2. the explicit sum, over powers `q=p^a`, of

```text
floor((n+d+k)/q) - floor((n+d)/q)
- floor((n+k)/q) + floor(n/q).
```

The necessary quotient-four targets are `2` for `p=2` and `0` for odd `p`.
The two implementations are asserted equal, and small blocks are also checked
against direct integer products.

## Arbitrary-position correction and counterfixtures

Suppose the `i`th lower term is `n+i=p^A`, with `1<=i<=k`, and the target
bound `9d<n` holds.  Translation by `p^A` preserves the valuation of every
nonzero offset in both blocks.  Consequently the exact lower valuation is

```text
A + v_p((i-1)!) + v_p((k-i)!),
```

not `A+v_p((k-1)!)` unless `i` is an endpoint or the intervening binomial
coefficient is a `p`-unit.  The exact upper valuation is

```text
v_p(B(k,d-i)).
```

Two target-shaped fixtures show that the uncorrected any-position claim cannot
be used:

| `p` | `A` | `k` | `d` | `i` | `n=p^A-i` | lower `v_p` | upper `v_p` | discrepancy |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 9 | 33 | 33 | 2 | 510 | 35 | 37 | 2 |
| 3 | 5 | 16 | 19 | 8 | 235 | 9 | 9 | 0 |

Both satisfy `k>=16`, `k<=d`, and `9d<n`.  Their discrepancies are exactly
the quotient-four targets (`2` at `p=2`, `0` at odd `p`).  They are local
valuation fixtures, not full product-equation solutions.

The corrected sufficient condition is

```text
v_p((k-1)!) <= v_p(4) + v_p((i-1)!(k-i)!).
```

The Lean proof shows `(i-1)!(k-i)!` divides the lower local cofactor.  Upper
valuation concentration then loses at most `v_p((k-1)!)`, so the displayed
condition makes the equation valuation impossible.  For `p>k` the left side
is zero, giving an unconditional result at every position.  At `i=1` and
`i=k`, the split factorial equals `(k-1)!`, so the condition holds for every
prime.

## Structured scan and falsification

The exact grid used `16<=k<=64` and `d=m*k` for
`m in {1,2,3,5,8,13}`.  Of 294 rows, 290 had no survivor.  The four surviving
points were exactly:

| `k` | `d` | surviving `n` |
|---:|---:|---:|
| 16 | 80 | 878 |
| 21 | 273 | 3996 |
| 25 | 325 | 5688 |
| 30 | 90 | 1877 |

These are survivors of the crossing-band plus primes-`<=k` valuation filter,
not solutions of the product equation.  They falsify any claim that this
finite prime system uniformly empties every crossing band.

The named row-prefix fixtures replay exactly:

| `(k,n,d)` | exact band | first failed prime | discrepancy |
|---|---|---:|---:|
| `(984,3177026,4480)` | `[3176708,3177690]` | 2 | 0 |
| `(244,48502,277)` | `[48373,48615]` | 2 | -5 |

Both points lie in the exact archimedean band, but neither satisfies even the
necessary 2-adic equation.  No assertion that either is a product-equation
solution is made.

An independent exact trial-division pass finds 63 lower-block prime powers in
the first fixture and 20 in the second.  Every one has exponent `A=1` and
prime base `p>k`; there are no composite prime powers in either lower block.
Thus the any-position large-base theorem also supplies direct prime-owner
obstructions at these points, although the fixtures were never assumed to be
solutions.

## Prime-power endpoint proof

Put `t=p^A` and `n=t-k`.  The proof has four quantified steps.

1. `(k-1)!` divides the descending product immediately before `t`, so
   `t*(k-1)!` divides `B(k,t-k)`.  Therefore

   ```text
   v_p(B(k,t-k)) >= A + v_p((k-1)!).
   ```

2. If `k<=d<t`, every term of the upper block is strictly between `t` and
   `2t`.

3. No integer strictly between `t` and `2t` is divisible by `t=p^A`.
   Hence each upper term has `p`-valuation at most `A-1`.  The banked exact
   valuation-concentration theorem then gives

   ```text
   v_p(B(k,t-k+d)) <= A-1 + v_p((k-1)!).
   ```

4. Factoring the equation at `p` says that the upper valuation equals the
   lower valuation plus `v_p(4)`, hence is at least the lower valuation.  This
   contradicts steps 1 and 3.

The core theorem assumes only `p.Prime` and `1<=k<=d<p^A`.  The target-facing
corollary uses `9d<n` only to obtain `d<p^A`; the valuation argument itself is
independent of `k>=16`.

## Any-position and small-cofactor proofs

For a lower owner `n+i=p^A`, the general core assumes the whole upper block is
inside `(p^A,2p^A)` and the split-factorial condition displayed above.  It
proves

```text
v_p(lower) >= A + v_p((i-1)!(k-i)!),
v_p(upper) < A + v_p((k-1)!).
```

The condition makes the second bound strictly smaller than
`v_p(4)+v_p(lower)`.  The target-facing theorem derives the interval from
`9d<n`.  When `p>k`, `v_p((k-1)!)=0`, so no extra premise remains: no lower
term at any position can equal `p^A`.

A separate owner-transfer theorem is stronger.  If

```text
n+i = a*p^A,  A>=1,  p>k,
a*(d+k-1) < n+i,
```

then the equation transfers `p^A` to one upper owner.  Subtracting owners
forces `p^A<=d+k-1`, contradicting the displayed size condition.  This theorem
is independent of a particular ratio constant.  The current `9d<n` estimate
and `a<=4` imply the size condition, yielding an unconditional target-facing
corollary.  A future sharper ratio window can raise `4` without changing the
owner-transfer proof.  In particular, a future premise `3*k*d<5*n` together
with `10*a<=3*k` would imply the abstract size bound using `d+k-1<2d`; that
window is not assumed or reproved in this module.

## Exact finite replay of both multiplier cases

The focused tests range over `p in {2,3,5,7}`, exponents `1,...,4`, all
`1<=k<min(p^A,15)`, and the lower, midpoint, and upper allowed gaps.  They
assert the two displayed valuation bounds and strict negative discrepancy.
Thus they separately cover:

- `p=2`, where the equation requires discrepancy `v_2(4)=2`;
- odd `p`, where the equation requires discrepancy `v_p(4)=0`.

Further exact tests freeze the two internal counterfixtures, every position
in three `p>k` rows, all coefficients `1<=a<=4` in a representative
small-cofactor row, and the exact large-base prime-owner counts in both named
fixtures.  These finite checks reproduce the theorem arithmetic but are not
used by the Lean proof.
