# Erdős 730 first-power and short/top attacks

Status: **higher-power budget sharpened; two independent `a=1` attack
families reduced and falsified at their overstrong boundaries; full gate
still open.**

The earlier exact block payment for `2<=a<=r` can be sharpened from
`58/125` to

```text
174/625 < 3/10.                                      (1)
```

After the audited strict-band payment `1/100`, the exact budget remaining
for `a=1` plus short/top is therefore

```text
1-1/100-174/625 = 1779/2500.                         (2)
```

Route A attacks aligned-block discrepancy for `a=1,r>=2`.  Route B treats
the shortest `a=r=1` blocks and the Q/S top boundary separately.  Neither
route is promoted from a finite diagnostic to a theorem.

## 1. Sharpening the proved higher-power payment

Retain the notation

```text
P=p^r, q=p^a, M=(H-1)H^(r-1),
C=#bad(I), N=|I|,
q(N-1)<=X,
CP<=M(N+2P).                                         (3)
```

For `r>=a>=2`, `P>=25`.  The rational atanh certificate proves exactly

```text
log 5 > 8/5.                                         (4)
```

The critical-length hypothesis gives

```text
N >= P(r log p)^2 > (256/25)P >= 10P+6.              (5)
```

Consequently

```text
(N+2P)/(N-1) <= 6/5,                                 (6)
5CqP <= 6MX.                                         (7)
```

Lean proves (7) as `normalized_block_cover_six_fifths`.  Reusing the exact
prime series

```text
sum_p (p+1)/(p(p-1)(2p+1)) < 29/500
```

gives the four-branch payment

```text
4*(6/5)*(29/500)=174/625.                            (8)
```

The verifier evaluates the exact rational certificate obtained from the
finite prime sum plus the `1/1000` tail envelope as approximately `0.277051`;
the decimal is diagnostic only, while (8) is the proof ceiling.  As in the
preceding unit-range artifact, the global prime/root aggregation is a
paper-and-exact-arithmetic result.  Lean proves the conditional cleared
endpoint inequality and the terminal rational comparisons, not the full
family-sieve instantiation.

## 2. Route A: aligned-block discrepancy

For `a=1`, let `A_z` be the number of exact-valuation restricted outputs in
the aligned block

```text
zP <= k < (z+1)P.
```

The exact full-period mean is

```text
mu_(p,r)
 = (H-1)H^(2r-1)/p^r.                               (9)
```

The tempting uniform improvement

```text
A_z <= 2 mu_(p,r)                                    (10)
```

is false.  The worst retained exact counterexample is

```text
branch Q, p=7, a=1, r=3,
max_z A_z=23,
mu=3072/343,
max/mu=7889/3072 > 2.                                (11)
```

Thus replacing the crude low-word block bound by `2*mean` is not a valid
proof route.

A weaker diagnostic boundary

```text
A_z <= (8/3) mu_(p,r)                                (12)
```

survives all 18 exact cases

```text
p=5, r=2,...,5, Q/S;
p=7, r=2,...,4, Q/S;
p=11,r=2,3,     Q/S.
```

The largest ratio remains (11).  Equation (12) is **OPEN**; the scan is
only a falsification boundary.  Even a proof of (12) must still be combined
with the maximal-`r` reciprocal-prime bands rather than summing `1/p` over
all primes without stratification.

## 3. Route B: exact shortest-block reduction

At `a=r=1`, write

```text
G(k)=A p k^2+B k+C.
```

For every integer `u,z`, exact expansion gives

```text
G(u+pz)-G(u)-pzB
 = A p^2(2uz+pz^2).                                  (13)
```

Lean proves the resulting `p^2` divisibility as
`first_power_fixed_upper_slope`; Python checks 588 signed fixtures.  Thus,
inside block `z`, the upper output digit is translated by the same fixed
increment `b z mod p` for every low coordinate `u`.

Let `U` be the low-digit exact-valuation set and let `c(u)` be the upper
digit at block zero.  The count in a complete aligned `r=1` block is
therefore the explicit finite-field correlation

```text
A_z = #{u in U : c(u)+b z mod p in {0,...,H-1}}.      (14)
```

For a consecutive set `J` of complete block indices, its count is exactly
`sum_(z in J) A_z`.  An arbitrary interval has at most two partial endpoint
blocks.  Exact least-digit deletion and the p-adic isometry bound each of
those by `H-1`, so the arbitrary-start reduction is

```text
#bad(I) <= sum_(z in J) A_z + 2(H-1).                 (15)
```

This removes the `p^2` polynomial and the interval translation from the
interior analytic statement; the carry multiset `c(U)` is the only
nontrivial interior object left.  The endpoint term in (15) must still be
paid in the normalized family sum.

### Exact falsification and scan

The uninflated main term already fails at

```text
p=19, branch S, a=r=1,
critical N=165, maximum start=109,
max hits=56,
max/uninflated-main=5054/4125 > 1.                   (16)
```

In fact 291 of the 328 scanned Q/S cases through prime 1000 exceed the
uninflated main.  Therefore the logarithmic allowance is load-bearing.

For the actual target, the verifier uses a rational **upper** bound for
`log p`.  Hence

```text
1+1/log_upper(p) < 1+1/log(p),                       (17)
```

so passing the smaller right-hand side is a rigorous finite check.  No
counterexample occurs in the 328 Q/S cases.  The closest is

```text
p=751, branch S,
critical N=32927, max hits=9095,
certified max/target < 0.958.                         (18)
```

This finite check does not prove the correlation estimate uniformly in
`p`.

## 4. Independent Q/S top-boundary exclusion

The top-range Q/S obstruction has an elementary digit obstruction once the
cofactor `c` is small.  On Q, if

```text
12 low = 7p+41c,    41c<5p,                          (19)
```

then

```text
p < 2 low,    low<p.                                 (20)
```

On S, if

```text
12 low+43c+6=7p,    43c+6<p,                         (21)
```

the same conclusion (20) holds.  Thus `low` is a genuine base-`p` digit
strictly above `(p-1)/2`, so Q/S cannot obstruct in this top subrange.
Lean proves (19)--(21) as `q_top_low_digit_large` and
`s_top_low_digit_large`.

The standard two-digit top hypothesis implies `c^2<p`.  Lean further proves
that this square inequality makes the needed small-cofactor hypothesis
automatic on Q for `p>=66`, and on S for `p>=1856`:

```text
c^2<p, 66<=p    -> 41c<5p;
c^2<p, 1856<=p  -> 43c+6<p.                           (22)
```

These thresholds are sharp as natural-number envelopes without primality:
`(p,c)=(65,8)` and `(1855,43)` respectively falsify their conclusions while
satisfying `c^2<p`.  The kernel theorems are
`q_top_small_cofactor_of_square_lt`,
`s_top_small_cofactor_of_square_lt`, `q_top_two_digit_large`, and
`s_top_two_digit_large`.

This leaves the already identified P/R bad cofactor residue classes and a
finite Q/S prime range below the displayed thresholds.  The present artifact
does not assign the P/R sieve or the finite exceptions a normalized constant.

Nor do these top lemmas delete arbitrary Q/S **short** classes.  The exact
verifier retains the prime `p=30000001` at `X=2^57`, where the Q and S
root-class lengths are both `4803839443`, below the critical length
`8892451300`.  Nevertheless it exhibits genuine restricted-digit
obstructions

```text
Q: x=304699465, c=3867733,
   Phi digits [714754,12202043,290876];
S: x=101483822, c=1288195,
   Phi digits [12883968,343247,32267].
```

Both have `c^2>p`, so the two-digit top lemmas do not apply.  Any exhaustive
short/top cover must retain these Q/S classes.

## 5. Dependency tree and verdicts

```text
F0  remaining a=1 plus short/top budget 1779/2500-delta             OPEN
|
+- F1 sharpen a>=2 endpoint factor 2 -> 6/5                         PROVED
|  `- four-branch higher-power payment <174/625                     EXACT
|
+- F2 aligned a=1,r>=2 discrepancy                                  OPEN
|  +- proposed 2*mean bound                                         FALSE
|  `- 8/3*mean boundary on 18 cases                                 EXACT-CHECKED ONLY
|
+- F3 shortest a=r=1 reduction to correlation plus endpoints (15)  PROVED/PAPER-EXACT
|  +- uninflated main                                               FALSE
|  `- inflated target through p<=1000 Q/S                           EXACT-CHECKED ONLY
|
`- F4 short/top
   +- Q/S two-digit exclusion above explicit finite thresholds      LEAN-PROVED
   +- Q/S finite top exceptions and non-top short classes           OPEN
   `- P/R explicit-class upper-bound sieve                           OPEN
```

## 6. Exact remaining gate, including the partition bridge

The residual labels must first be tied to an exhaustive cover of the actual
campaign obstruction indicators.  Let `BadFamilyCount(X)` count family
parameters `x<=X` with at least one obstruction.  Let
`ObstructionEventCount(X)` count obstruction events with
`(branch,p,a)` multiplicity, so the first-moment inequality is

```text
BadFamilyCount(X) <= ObstructionEventCount(X)
 <= StrictBand(X) + HigherPowerFar(X)
    + FirstPowerFar(X) + ShortTop(X).                 (23)
```

Every term on the right counts events with the same multiplicity.  The first
two are exactly the already audited ranges paid by
`1/100` and `174/625`.  `FirstPowerFar` consists of the actual long root
classes with exact exponent `a=1` and maximal admissible `r`.  `ShortTop` is
the residual campaign cover, counted at least once but not required to be
disjoint, after those three named ranges.  It includes every short class,
the P/R top classes, the finite Q/S top ranges not covered by (22), and any
class whose placement has not yet been bridged to the analytic partition.

With (23) proved, the one numerical residual is to exhibit an explicit
`delta>0` such that

```text
FirstPowerFar(X)/X + ShortTop(X)/X
 <= 1779/2500-delta.                                  (24)
```

Here `FirstPowerFar` includes:

- the `r>=2` aligned-block counts, with arbitrary interval starts; and
- for `r=1`, the exact correlations (14) over the actual consecutive block
  interval together with the two endpoint blocks in (15).

`ShortTop` retains every no-maximal-`r` short class across all four branches,
all relevant primes, and all exact exponents.  It also retains the P/R top
classes and the finite Q/S top prime range not covered by (22); the exact
Q/S witness above shows why these categories cannot be conflated.  A proof
must sum its discrepancy, finite exceptions, or sieve errors with explicit
constants.  The finite `8/3` and `p<=1000` observations may not be inserted
as hypotheses.

Without the explicit indicator bridge (23), (24) is only suggestive notation
and is not sufficient for campaign closure.  With that bridge, it is the
exact remaining numerical gate.  The gate is not yet closed.

## Boundary audit

- The paid `s<r` band is untouched.
- The higher-power payment includes the boundary `a=r>=2`; the sole
  corrected analytic exponent is now `a=1`.
- The overstrong aligned constant first fails on the retained scan at Q,
  `(p,r)=(5,2)`, with ratio `125/54`; its worst retained ratio is (11).
- The shortest admissible prime `p=5` is present in both exact grids.
- The r=1 verdict uses `log_upper`, not `log_lower`, so its tested target is
  conservatively smaller than the true target.
- The uninflated r=1 main is labeled false; the logarithmic term is not
  silently discarded.
- Q/S top exclusion leaves its explicit finite prime ranges and does not
  claim a P/R sieve bound.
- The exact `p=30000001` witness prevents Q/S short classes from being
  silently absorbed into the top two-digit exclusion.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos730FirstPowerRoutes.lean
python3 -m pytest \
  compute730/campaign_uniform/repair/far/test_first_power_routes.py -q
python3 compute730/campaign_uniform/repair/far/first_power_routes.py --pretty
```
