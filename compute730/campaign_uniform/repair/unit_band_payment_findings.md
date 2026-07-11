# Erdős #730: full high-valuation-band payment

Status: **independent hostile audit PASS for the paper payment, exact
endpoint, and Lean arithmetic spine.**

The stronger affine-progression counterexample is confined to `s<r/2`, but
the valuation-rarity argument pays the strictly larger, natural band

```text
s=max(2r-a,0) < r.                                  (1)
```

This is the largest strict linear band of this form that uniformly excludes
the first-power boundary `(a,r)=(1,1)`.

## Exact exponent clearance

If `a<2r`, (1) and `s=2r-a` give `r<a`; if `a>=2r` the same conclusion is
immediate.  Since `r>=1`, every event in (1) satisfies

```text
a>=2,                 r+1<=a,
p^(r+1)<=p^a=q.                                      (2)
```

With `r` chosen maximally from the actual branch-class count, the audited
residue-count/maximality inequality is

```text
X < 2q p^(r+1) ((r+1)log p)^2.                      (3)
```

Write `M=380808X+19` and `B=bit_length(M)`.  Since `q<=M`, (2) gives
`(r+1)log p<=log q< B`.  Therefore

```text
X < 2 B^2 q^2,
q > sqrt(X/(2B^2)).                                 (4)
```

No digit equidistribution estimate enters this payment.

## Exact endpoint

For `X>=2^57`, the dyadic reduction has `B=78`.  The threshold base
`2^m/(2(m+21)^2)` is increasing for `m>=57`.  Exact arithmetic gives

```text
Y=3441480,
2*78^2*3441480^2 <= 2^57 < 2*78^2*3441481^2,
1855^2 <= Y < 1856^2,
150^3  <= Y < 151^3.                                (5)
```

Using the same exact reciprocal-prime-power tail and branch-boundary count,
the four-branch payment is

```text
4(2/1855 + 3/150^2)
 + 4(388736063997 + 78*53264341)/2^57
= 121726379332007683003 / 25062531926316810240000
< 1/100.                                            (6)
```

The cleared margin is

```text
25062531926316810240000
 - 100*121726379332007683003
= 12889893993116041939700 > 0.                      (7)
```

## Exact remaining gate

After this enlarged payment, the analytic incomplete-block range can be
taken as

```text
s>=r, equivalently a<=r.                            (8)
```

No estimate is claimed there.  The sparse Fourier triangle majorant and the
short/top-range global budget remain open.  The infinite reciprocal-prime-
power summation and positive-real root/monotonicity transfer remain
paper-level exactly as in the earlier payment; Lean checks the exponent,
maximality threshold, dyadic step, and endpoint arithmetic only.

## Reproduction

```bash
python3 -m pytest \
  compute730/campaign_uniform/repair/test_unit_band_payment.py -q
python3 compute730/campaign_uniform/repair/unit_band_payment.py
lake env lean ErdosProblems/Erdos730UnitBandPayment.lean
```
