# Erdős #730 corrected gate: near-affine valuation payment

Date: 2026-07-10

Verdict: **PAPER-PROVED and exact-arithmetic audited for the maximal-block
choice of `r`, with explicit constants `C=2` and `eta=1/12`; Lean intake
is pending.**  The normalized first-moment payment of
the whole near-affine band among classes admitting an analytic block
`r>=1` is less than `1/100` for every family cutoff `X>=2^57`.

This result does not prove a far-range Fourier estimate, a top-range sieve
bound, the combined budget, or Erdős #730.  Classes too short to admit even
`r=1` are also outside this module and must be assigned to the separate
short/top-range term.

## 1. Quantifiers and the missing dependence of `r`

The four branches are

```text
P(x)=222138x+11,  Q(x)=380808x+13,
R(x)=148092x+5,   S(x)=380808x+19.
```

Fix an integer cutoff `X>=1`, a relevant prime `p>=5`, a branch `L` whose
slope is a unit modulo `p`, and an exponent `a>=1`.  Put

```text
q=p^a,
N=N(L,p,a;X)=#{1<=x<=X:q divides L(x)},
M=380808X+19.
```

There is exactly one root modulo `q`, so its representatives form one
consecutive `k`-interval and

```text
X/q-1 <= N <= X/q+1,                 (1)
X <= q(N+1).                          (2)
```

For `C=2`, define `r` to be the **largest** integer `j>=1` satisfying

```text
p^j (log p^j)^2 = p^j(j log p)^2 <= N.       (3)
```

Thus

```text
p^r(r log p)^2 <= N
  < p^(r+1)((r+1)log p)^2.                     (4)
```

This is the relationship omitted when `r,p,a,X` are treated as independent.
The analytic block exponent is selected from the actual number `N` of
parameters left after imposing `p^a | L(x)`.

The cofactor/digit scale is controlled by the same `q`.  If `Z` is the
Kummer test integer on the event `p^a || L(x)`, then the exact branch
formulas give

```text
2qZ <= 3M^2.                                      (5)
```

For P and Q, `Z=PQ/q`; for R and S,
`Z=(3RS/q-1)/2`.  If `d` is the base-`p` digit length of `Z`, then

```text
p^(d-1) <= Z < p^d,
p^(d-1) <= 3M^2/(2q).                            (6)
```

Equations (1), (4), and (6) replace the informal independent choices:
up to the displayed one-block and logarithmic losses, `r` is
`log_p(X/q)` while `d` is at most `log_p(3M^2/(2q))+1`.  In particular,
the two scales are both functions of the same valuation `q=p^a`.

If `Z` has all restricted digits, then its first `2r` digits are restricted
even when `d<2r` (the additional digits are zero).  Hence selecting the
largest admissible `r` loses no logical implication needed by the
first-moment upper bound.

## 2. Near band implies a high prime power

Put

```text
H=(p+1)/2,
kappa_p=log_p(p/H),
s=max(2r-a,0),
eta=1/12.
```

For every integer `p>=5`,

```text
8p^2 <= (p+1)^3.                                  (7)
```

Indeed the difference is `p^3-5p^2+3p+1`, which is `16` at `p=5` and
strictly increasing for `p>=5`.  Cubing shows

```text
2p/(p+1) <= p^(1/3),
kappa_p <= 1/3.                                   (8)
```

Therefore the actual near condition

```text
s < (kappa_p+eta)r
```

implies the rational envelope

```text
12s < 5r.                                         (9)
```

If `a<2r`, substitute `s=2r-a` in (9).  If `a>=2r`, the same conclusion
is immediate.  In both cases,

```text
12a > 19r.                                        (10)
```

Since `r>=1`, (10) also proves `a>=2`; no first-power valuation lies in
this near envelope.

Maximality in (4), (2), and `p>=5` give

```text
X < 2q p^(r+1) ((r+1)log p)^2.                    (11)
```

From (10), `r<12a/19`.  Because `a>=2`,

```text
p^(r+1) < q^(12/19+1/2)=q^(43/38).                (12)
```

Let `B=bit_length(M)`.  Since `q<=L(x)<=M`, `log M<B`, and
`r+1<43a/38`,

```text
((r+1)log p)^2 < W_X,
W_X=((43B)/38)^2.                                 (13)
```

Combining (11)--(13) yields the exact powered threshold

```text
X^38 < (2W_X)^38 q^81.                            (14)
```

Equivalently, every near event satisfies

```text
q > Y_X,
Y_X=(X/(2W_X))^(38/81).                           (15)
```

No digit equidistribution estimate is used in this step.

## 3. Explicit normalized first-moment bound

Let `Near(X)` be the sum, over all four branches and every near tuple
admitting the maximal `r`, of the number of actual obstruction parameters
`1<=x<=X`.  Dropping the digit condition and exactness only enlarges the
count.  A residue class modulo `q` contains at most `X/q+1` parameters, so

```text
Near(X)/X
 <= 4 sum_{p prime,a>=2,p^a>=Y_X} p^(-a)
    + 4K(M)/X,                                    (16)
```

where

```text
K(M)=#{(p,a):p prime,a>=2,p^a<=M}.
```

For every real `Y>=1`, the reciprocal prime-power tail satisfies

```text
sum_{p,a>=2,p^a>=Y} p^(-a)
 <= 2Y^(-1/2)+3Y^(-2/3).                          (17)
```

Proof of (17):

- For `a=2`, dominate primes by all integers at least `ceil(sqrt Y)`;
  the integral test gives at most `2Y^(-1/2)`.
- For `a>=3` and `p<=Y^(1/3)`, start the geometric series at
  `ceil(log_p Y)`.  Each prime contributes at most `2/Y`, and there are
  at most `Y^(1/3)` such primes, for `2Y^(-2/3)`.
- For `p>Y^(1/3)`, start at `a=3`; the contribution is at most `2p^(-3)`.
  Dominating primes by integers and integrating gives `Y^(-2/3)`.

Also

```text
K(M) <= sqrt(M)+B M^(1/3).                        (18)
```

The square exponents contribute at most `sqrt M` bases; every exponent
`a>=3` contributes at most `M^(1/3)` bases, and fewer than `B` exponents
are possible.

Substitution in (16) gives the explicit payment

```text
Near(X)/X
 <= 8Y_X^(-1/2)+12Y_X^(-2/3)
    +4(sqrt(M)+B M^(1/3))/X.                      (19)
```

Since `M=380808X+19`, `B=O(log X)`, and
`W_X=O((log X)^2)`, the four terms in (19) are respectively

```text
O(X^(-19/81)(log X)^(38/81)),
O(X^(-76/243)(log X)^(152/243)),
O(X^(-1/2)),
O((log X)X^(-2/3)).                               (20)
```

Thus the maximal-`r` near-affine payment tends to zero.

## 4. Exact uniform one-percent certificate

The exact script gives a simple cutoff valid for every `X>=2^57`.
Write `2^m<=X<2^(m+1)`, so `m>=57`.  Since

```text
M=380808X+19 < 2^19 X < 2^(m+20),
B <= m+20 < m+21,
```

where the first strict inequality follows from
`(2^19-380808)X=143480X>19`, it is safe to use the deliberately looser
bit bound `B<=m+21`.  Consequently

the lower-threshold base

```text
2^m / (2((43(m+21))/38)^2)
```

is increasing in `m`: the ratio of consecutive terms is
`2((m+21)/(m+22))^2>1`.  It is therefore enough to use `m=57`,
`B=78`.  Exact integer powering gives

```text
Y_X >= 1,210,239,
floor(sqrt(1,210,239))=1100,
floor(cuberoot(1,210,239))=106.                   (21)
```

The real threshold in (15) is at least `1,210,239`.  Since every event
has integer `q>Y_X`, in fact `q>=1,210,240`; replacing this by the larger
tail set `q>=1,210,239` in (17) is conservative.

The script verifies (21) by the cleared inequality

```text
1,210,239^81 * (2(43*78/38)^2)^38 <= (2^57)^38.
```

The two boundary envelopes decrease on successive dyadic ranges because

```text
2^10 X^(-1/2)
```

decreases, and

```text
(m+21)2^(20/3-2m/3)
```

has consecutive ratio `((m+22)/(m+21))2^(-2/3)<1` for `m>=57`.
Using ceiling roots of the initial dyadic envelope `2^77`, the fully
rational upper bound in (19) is

```text
232437037423222418449 / 27831344977224191180800
  < 1/100.                                        (22)
```

The cleared margin in (22) is

```text
27831344977224191180800
 - 100*232437037423222418449
 = 4587641234901949335900 > 0.
```

## 5. Why maximality is load-bearing

If `r` is allowed to be an arbitrary smaller integer, valuation rarity
does not follow.  For example, fix the Q branch, `p=5`, `a=2`, and `r=1`.
Then `s=0`, so this tuple is near for every positive `eta`, at every
cutoff.  On each complete block of 125 values of `x`, exactly five values
satisfy `25 | Q(x)` and exactly one satisfies `125 | Q(x)`.  Hence

```text
#{1<=x<=125N:25 || Q(x)}=4N,
```

with fixed density `4/125`.  The test suite checks the exact instance
`N=1000`, giving `4000` events among `125000` parameters.

This is not a counterexample to the digit obstruction bound: it shows that
the proposed **valuation-only payment** cannot become negligible unless
`r` is tied maximally to `X/p^a` as in (3).  The corrected global lemma
should make that convention explicit.

## 6. Dependency tree and verdicts

```text
R0  Near-affine payment for classes admitting r>=1 tends to zero     PAPER-PROVED
 |
 +-- R1  One branch root modulo p^a; N=X/p^a+O(1)                    PROVED
 +-- R2  r chosen maximally from N by p^r(log p^r)^2<=N              REQUIRED/PROVED
 +-- R3  Cofactor digit length uses the same q=p^a                   PROVED
 |       2qZ<=3M^2
 +-- R4  kappa_p<=1/3 for p>=5; eta=1/12                             PROVED
 +-- R5  Near condition forces a>=2 and 12a>19r                      PROVED
 +-- R6  Prime-power threshold X^38<(2W_X)^38(p^a)^81                PROVED
 +-- R7  Reciprocal prime-power tail <=2Y^-1/2+3Y^-2/3               PROVED
 +-- R8  Boundary pair count K(M)<=sqrt(M)+B M^(1/3)                 PROVED
 `-- R9  Uniform X>=2^57 payment <1/100                              EXACT-CHECKED

R10 Same valuation-rarity conclusion with arbitrary nonmaximal r     FALSE
 `-- Q-branch p=5,a=2,r=1 retains valuation density 4/125            EXACT-CHECKED

F0  Separated-range incomplete-block/Fourier estimate                NOT CLAIMED
F1  Top/short-range sieve payment                                    NOT CLAIMED
F2  Combined first-moment budget <=1-delta                           NOT CLAIMED
```

## 7. Reproduction

```bash
python3 -m pytest compute730/campaign_uniform/repair/test_near_affine_payment.py -q
python3 compute730/campaign_uniform/repair/near_affine_payment.py
```

All asserted certificate comparisons are integer or rational.  Decimal
approximations are not used by the proof or tests.
