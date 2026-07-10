# Erdős 686 large-`k` matching compression

Status: new exact ownership-compression lemmas survive both named deep
fixtures and give a non-target-equivalent transition inequality.  They do not
close Target 2.

## Exact lemmas

Define

```text
C(k,d) = lcm(d-k+1, d-k+2, ..., d+k-1).
```

Let `k>=1`, `d>=k`, and suppose the exact equation holds:

```text
B(k,n+d)=4B(k,n).
```

Then

```text
B(k,n) | (k-1)! * C(k,d).                       (1)
```

There is also a row-only fallback.  If every lower row survives,

```text
n+i | product_{j=1}^k (d+j-i)                   (2)
```

for `1<=i<=k`, then

```text
B(k,n) | ((k-1)!)^2 * C(k,d).                   (3)
```

Consequently every hypothetical `N=4`, `k>=16` solution satisfies (1).  A new
exact Bernoulli comparison sharpens the large-`k` ratio window to

```text
k*d < 5*n.
```

It therefore forces the `k`-scaled transition inequality

```text
(k*d)^k < 5^k * (k-1)! * C(k,d).                (4)
```

The earlier fixed comparison remains available as

```text
(k-1)! * C(k,d) > (9d)^k.                       (5)
```

These statements are strictly weaker than Target 2.  Equations (1), (4), and
(5) are proved consequences of the equation, not replacement hypotheses
equivalent to its nonexistence.  Equation (3) follows from the row skeleton
alone, without the product equation, smoothness, or reflection hypotheses.

## One-factorial equation matching

Fix a prime `p`, put `a=v_p((k-1)!)`, and write

```text
V = v_p(B(k,n)).
```

Choose maximum-valuation owners `i_p` in the lower block and `j_p` in the
upper block.  Consecutive-block concentration gives

```text
V <= v_p(n+i_p)+a.
```

The equation makes `B(k,n)` divide `B(k,n+d)`, so a second concentration
application gives

```text
V <= v_p(n+d+j_p)+a.
```

Therefore the owner chunk

```text
p^(V-a)
```

with truncated exponent zero divides both owner terms, hence divides their
positive difference `d+j_p-i_p`.  Chunks belonging to distinct primes are
coprime, so their product divides `C(k,d)`, not merely the product of all
centered differences.  The valuation left outside the chunk is at most `a`,
and one copy of `(k-1)!` supplies that allowance, giving (1).

For the row-only theorem (3), choose a lower owner of exponent `E`.  The first
concentration step gives `v_p(B(k,n))<=E+a`; concentrating its surviving row
costs a second `a` and puts `p^(E-a)` in one centered difference.  This gives
the two factorial losses in (3).

This accounting includes small prime bases.  It does not silently treat
`p^e>k` as if the full power had to occur in one factor of a length-`k`
product.  That naive localization is false: `2^3`, for example, can be
supplied across the factors `2` and `4`.  The second row-only factorial copy
is the uniform allowance that repairs that split-valuation error; direct
matching of the two equation owners avoids it.

## Centered-product absorption

The remaining factorial in (1) is absorbed by the centered interval itself.
More generally, for any `2r+1` consecutive positive integers `x,...,x+2r`,

```text
r! * lcm(x,...,x+2r) | product_{t=0}^{2r} (x+t).     (6)
```

Here is the primewise proof.  Fix `p` and select a term with maximal `p`-adic
valuation `E`; this is the `p`-part of the lcm.  Among the `2r` other positions,
at least `r` consecutive positions lie entirely on one side of the selected
term.  The product of those `r` consecutive positive integers is divisible by
`r!` (it is `r!` times a binomial coefficient).  Hence the product of all
non-owner terms has `p`-adic valuation at least `v_p(r!)`.  Adding the owner's
`E` proves (6) for every prime.

Taking `r=k-1` and composing (6) with (1) gives the exact consequence

```text
B(k,n) | product_{s=-(k-1)}^(k-1) (d+s).             (7)
```

This strengthens the banked lower-**lcm** divisibility to divisibility of the
entire lower block.  It still does not close large `d`: the right side has
degree `2k-1` in `d`, versus degree `k` on the left.  The exact verifier checks
(6) for every start `1..79`, every length `1..39`, and both named large
centered intervals.  The one-factorial compression is Lean-banked; (6) and
(7) are presently exact paper-level consequences, not yet separate audited
Lean surfaces.

## Exact scaled ratio bound

If `5n<=k*d`, then `d>=k` gives the linear comparison

```text
(k+10)(n+k) <= (k+5)(n+d+k).
```

Bernoulli's inequality, used over the rationals with
`a=5/(k+5)`, gives

```text
((k+10)/(k+5))^k >= 1 + 5k/(k+5) > 4
```

for `k>=16`.  Raising the linear comparison to the `k`th power and composing
with the upper ratio window would give the reverse inequality, a
contradiction.  This proves `k*d<5n` with no asymptotics.  Multiplying the
termwise inequalities `k*d<5(n+i)` and applying (1) gives (4).

## Named-fixture audit

The exact verifier reproduces the required boundaries.  Neither point
satisfies the equation, so the one-factorial theorem makes no claim about it;
the independent row-only ledger reaches exactly the recorded failed row.

- `(k,n,d)=(984,3177026,4480)` passes rows `1..16`.  In the full-block owner
  ledger, `7237 | n+17` has owner exponent one and
  `v_7237(983!)=0`; its chunk `7237` has no landing among
  `4464,...,5447`.  This is the exact row-17 failure.
- `(k,n,d)=(244,48502,277)` passes rows `1..15`.  The owner chunk
  `1427 | n+16` has loss zero and no landing among `262,...,505`.  This is the
  exact row-16 failure.

Thus neither prefix survivor is rejected before its recorded boundary, and
neither is treated as satisfying the full-row premise.

The exact owner code also replays the two genuine `d=1` telescopes at
`(k,n)=(9,2)` and `(15,4)`: every one-factorial owner chunk divides both
selected terms and their difference.  Those points are outside `d>=k` and are
used only to audit the matching mechanism.

## Exact obstruction to a size-only finish

The generic upper bound

```text
C(k,d) <= product_{s=-(k-1)}^(k-1) (d+s)
       < (2d)^(2k-1)                              (d>=k)
```

has degree `2k-1` in `d`, whereas the forced lower bounds (4) and (5) have
degree `k`.
After clearing `(k-1)!`, the upper bound already dominates at the first
boundary `k=d=16`, and the exponent deficit is `k-1`; it only worsens as `d`
grows.  Thus (1) cannot finish the large-`d` regime by gross size.  A
successful continuation must use arithmetic correlations among selected
owner landings, or combine them with the reflection matching.

The row skeleton itself has exact full-row survivors outside the ratio window:
for `k=16`, `n=1`, and

```text
d=lcm(2,...,17)=12,252,240,
```

row `i` contains the factor `d` at column `i`.  This is a concrete model
showing that the row-only theorem (3) is not a disguised Target 2 hypothesis.

## Lean surfaces

The standalone module proves:

```text
blockProduct_dvd_factorial_sq_mul_centeredDiffLcm_of_individual_skeleton
blockProduct_dvd_factorial_mul_centeredDiffLcm_four
k_mul_gap_lt_five_mul_n_of_four_solution
k_gap_pow_lt_five_pow_mul_factorial_mul_centeredDiffLcm_four
nine_gap_pow_lt_factorial_mul_centeredDiffLcm_four
```

No assumption-strength placeholder is introduced.

## Reproduction

```bash
python3 -m pytest compute/campaign686/test_matching_compression.py -q
lake env lean ErdosProblems/Erdos686MatchingCompression.lean
```
