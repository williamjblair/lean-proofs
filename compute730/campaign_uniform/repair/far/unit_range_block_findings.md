# Erdős 730 corrected unit range: exact block payment for `2<=a<=r`

Status: **proper corrected subrange paid on paper with exact arithmetic; block
algebra kernel-banked; full gate open.**

In the unpaid range `s>=r`, equivalently `a<=r`, the exact `p^r` block
decomposition pays the entire higher-prime-power subrange

```text
2 <= a <= r
```

across all four branches by less than

```text
58/125 = 0.464.                                      (1)
```

This is a deliberately coarse first-moment payment, not a zero-error
Fourier estimate.  The corrected incomplete-block residue is now `a=1`,
together with the independently open short/top budget.  No conclusion about
Erdős 730 is claimed.

The exact verifier is `unit_range_block.py`, its tests are
`test_unit_range_block.py`, and the generic block identity and normalized
cross inequality are in `ErdosProblems/Erdos730UnitRangeBlock.lean`.

## 1. Exact aligned-block identity

Fix a relevant odd prime `p>=5`, put

```text
H=(p+1)/2,   q=p^a,   P=p^r,
G(k)=A q k^2+(q u+b)k+v,   p does not divide b.
```

For all integers `x,z`, direct expansion gives

```text
G(x+Pz)
 = G(x)+Pz G'(x)+AqP^2z^2.                         (2)
```

Consequently

```text
G(x+Pz) = G(x)+Pz G'(x)  (mod P^2).                (3)
```

Lean proves (2)--(3) generically.  The Python verifier separately checks
1,764 signed fixtures across all four branch coefficient shapes and
`p=5,7,11`.

## 2. Uniform count on one aligned block

On the aligned block `zP <= k < (z+1)P`, write `k=x+zP` with
`0<=x<P`.  Equation (3) shows that the low `r` output digits are exactly
`G(x) mod P`.  The banked p-adic isometry says that `x -> G(x) mod P` is a
permutation.

The low `r` output digits must lie in `{0,...,H-1}`, and exact valuation
deletes one possible least digit.  Therefore exactly

```text
M=(H-1)H^(r-1)                                      (4)
```

values of `x mod P` pass the low-word test.  Requiring the upper `r` digits
can only decrease the count.  Thus every aligned block contains at most
`M` bad parameters.

An arbitrary interval `I` of length `N` intersects at most
`floor(N/P)+2` aligned blocks, so the explicit uniform estimate is

```text
#bad(I) <= E_block(p,r,N),
E_block(p,r,N)=M(floor(N/P)+2).                     (5)
```

This holds for every interval translation, branch, admissible root, and
`a`; no Fourier signs or interval averaging are used.

To place (5) in the requested main-plus-error form, one may take

```text
#bad(I)
 <= (H/p)^(2r) N (1+1/log(P)) + E_block(p,r,N).     (6)
```

The main term is simply discarded in the payment below, so (6) is not
presented as a sharp local estimate.

## 3. Exact family normalization

For a fixed branch and exact prime power `q=p^a`, the root class in
`1<=x<=X` is a consecutive `k`-interval of length `N`, and its endpoints
give

```text
q(N-1) <= X.                                        (7)
```

The campaign chooses `r` with

```text
N >= P(log P)^2 = P(r log p)^2.                    (8)
```

In the proper subrange `2<=a<=r`, one has `r>=2`.  Since `p>=5` and
`log 5>1`, certified by the verifier's rational atanh lower bound, (8)
gives

```text
4P <= N.                                           (9)
```

Multiplying (5) by `P` and using
`P floor(N/P)<=N` gives

```text
#bad(I) P <= M(N+2P).                              (10)
```

Equations (7), (9), and (10) imply the division-free inequality

```text
#bad(I) q P <= 2 M X.                              (11)
```

Lean proves this implication as
`normalized_block_cover_cross_bound`.  Since all denominators are positive,
(11) is exactly

```text
#bad(I)/X <= 2 rho_(p,r)/p^a,
rho_(p,r)=M/P=(H-1)H^(r-1)/p^r.                    (12)
```

## 4. Exact higher-prime-power sum

For each `(p,a)` only the campaign's maximal `r` is used.  Dropping that
restriction and summing every `r>=a` only enlarges (12).  For one branch,
the resulting geometric series at a fixed prime is exactly

```text
S_p
 = sum_(a>=2) p^(-a) sum_(r>=a) rho_(p,r)
 = (p+1)/(p(p-1)(2p+1)).                           (13)
```

The verifier generates the 166 primes from `5` through `997` by an exact
sieve and adds (13) as `Fraction` values.  It proves

```text
sum_(5<=p<=1000, p prime) S_p < 57/1000.           (14)
```

For `p>1000`,

```text
S_p < 1/(p(p-1)).                                  (15)
```

Dropping primality and telescoping over every integer gives

```text
sum_(p>1000, p prime) S_p
 < sum_(n>=1001) 1/(n(n-1))
 = 1/1000.                                         (16)
```

The factor `2` in (12) and the four branches therefore give

```text
HigherPower(X)/X
 < 2*4*(57/1000+1/1000)
 = 58/125
 < 1/2.                                            (17)
```

Unavailable roots and the excluded primes are retained in this upper sum,
so (17) does not depend on favorable branch omissions.

## 5. Dependency tree and verdicts

```text
B0  corrected incomplete range a<=r
|
+- B1 exact quadratic block expansion (2)                         LEAN-PROVED
|  `- low r digits independent of aligned block index
|
+- B2 p-adic isometry modulo p^r                                  BANKED INPUT
|  `- exact deleted low-word count M=(H-1)H^(r-1)
|
+- B3 arbitrary interval block cover                              PROVED
|  `- #bad(I)<=M(floor(N/P)+2)
|
+- B4 family root-class normalization                             LEAN-PROVED ALGEBRA
|  +- q(N-1)<=X
|  +- critical N>=P(log P)^2 and r>=2 give 4P<=N
|  `- #bad(I)qP<=2MX
|
+- B5 exact double geometric series for a>=2,r>=a                PROVED
|  `- S_p=(p+1)/(p(p-1)(2p+1))
|
+- B6 finite prime certificate plus telescoping tail              EXACT-CHECKED
|  `- four-branch normalized payment <58/125
|
`- B7 first-power range a=1 and short/top budget                  OPEN
```

The finite prime sum in B6 is exact Python rational arithmetic, not yet a
kernel-expanded 166-prime certificate.  The reusable polynomial and
normalization identities in B1 and B4 are kernel-checked with only the
allowed axiom set.

## 6. New exact hostile scans

Two rows extend beyond the previous grid (`p=5,r=5` and `p=7,r=4`).  The
`p=11,r=3` row probes the surviving first-power boundary.  All verdicts
compare cleared integers with the uninflated main term; decimals are not
used.

| branch | `p` | `r` | `a` | critical `N` | max hits | exact max/main ratio | max aligned / bound |
|:--|---:|---:|---:|---:|---:|:--|:--|
| Q | 5 | 5 | 4 | 202,367 | 1,008 | `1093750000/1327729887` | `30/162` |
| Q | 7 | 4 | 1 | 145,465 | 1,341 | `7730598141/9533194240` | `38/192` |
| S | 11 | 3 | 1 | 68,879 | 1,660 | `735197815/803404656` | `52/180` |

No corrected-range counterexample appears in these finite cases.  This is
not extrapolated to a uniform theorem; the proof of the paid subrange is
(2)--(17), not the scan.

## 7. Single remaining quantified gate

The strict band `s<r` is already paid by less than `1/100`.  Equation (17)
pays the `2<=a<=r` portion of `s>=r` by less than `58/125`.  The exact
unallocated budget is therefore

```text
1 - 1/100 - 58/125 = 263/500.                      (18)
```

It remains to prove that there is an explicit `delta>0` such that, for
every family cutoff `X>=2^57`, the total normalized contribution of

```text
a=1, s=2r-1>=r,
```

with `r` chosen maximally from the actual root-class length, plus the
short/top range, is at most

```text
263/500-delta.                                     (19)
```

Equivalently, one may prove a sharper incomplete-block estimate for the
first-power classes and combine its explicit error with the short/top
sieve.  The coarse block envelope (12) is available there too, but its
maximal-`r` prime-band sum has not been bounded by (19).  Calling it
payable without that prime-band calculation would be the remaining
theorem-strength gap.

## 8. Boundary audit

- The paid strict band `s<r` is not revisited.
- The boundary `a=r` is included whenever `r>=2`; the corner `(a,r)=(1,1)`
  remains in the explicit first-power gap.
- The false zero-error signed Fourier inequality is never invoked.  The
  nonzero error (5) is visible throughout.
- Exact valuation is paid by deleting the branch's forbidden least output
  digit; it is not silently replaced by divisibility.
- Arbitrary interval starts are handled by two boundary blocks in (5).
- Small relevant primes `5,7,11` are included.  Summing all primes `p>=5`
  only enlarges the first moment, so exceptional branch primes cannot make
  (17) optimistic.
- The exact scans include `a=1` only as hostile evidence; no first-power
  theorem is inferred from them.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos730UnitRangeBlock.lean
python3 -m pytest \
  compute730/campaign_uniform/repair/far/test_unit_range_block.py -q
python3 compute730/campaign_uniform/repair/far/unit_range_block.py --pretty
```
