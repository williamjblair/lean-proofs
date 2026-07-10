# Erdős #730: enlarged half-band valuation payment

Status: **independent hostile audit PASS for the paper derivation, exact
endpoint, and kernel-banked arithmetic spine.**

The stronger affine-progression obstruction reaches

```text
s/r < theta_p = kappa_p/(1-kappa_p),
```

so the old near/far cut at `(kappa_p+1/12)r` is too low.  This note repairs
the accounting side: the maximal-`r` valuation payment remains below one
percent on the uniform larger band

```text
2s < r.                                             (1)
```

The already-proved inequality `kappa_p<=1/3` also gives
`theta_p<=1/2`, since

```text
8p^2 <= (p+1)^3
```

is exactly `p^2<=H^3` after writing `p+1=2H`.  Thus (1) pays the whole
known progression-obstruction band for every `p>=5`.

## Sharpened valuation threshold

As before, let `q=p^a`, choose `r` maximally from the actual branch-class
length, and write `s=max(2r-a,0)`.  From `2s<r` one obtains

```text
3r < 2a,
a >= 2,
6(r+1) < 7a.                                      (2)
```

The maximality comparison therefore sharpens to

```text
p^(r+1) < q^(7/6).
```

With `B=bit_length(M)` and

```text
W_X=((7B)/6)^2,
```

the exact powered threshold is

```text
X^6 < (2W_X)^6 q^13.                              (3)
```

Equivalently, every half-band event has

```text
q > (X/(2W_X))^(6/13).                            (4)
```

This is only slightly weaker than the former exponent `38/81` and uses the
same reciprocal-prime-power tail and boundary-pair estimates.

## Exact one-percent endpoint

For `X>=2^57`, the same dyadic reduction lands at `m=57`, `B=78`.  Now

```text
W_X=(7*78/6)^2=8281.
```

Exact integer powers give the threshold floor

```text
Y=937824,
937824^13 * (2*8281)^6 <= (2^57)^6,
937825^13 * (2*8281)^6 >  (2^57)^6.               (5)
```

The exact root certificates are

```text
968^2 <= Y < 969^2,
97^3  <= Y < 98^3.                                (6)
```

Using the unchanged branch envelope `M<2^77`, the four-branch payment is

```text
4(2/968 + 3/97^2)
 + 4(388736063997 + 78*53264341)/2^57
= 391756066143304555403 / 41018389089323268964352
< 1/100.                                          (7)
```

The cleared margin is

```text
41018389089323268964352
 - 100*391756066143304555403
= 1842782474992813424052 > 0.                     (8)
```

## Exact remaining gate

After replacing the invalid cut, the corrected open analytic range can be
taken as

```text
s >= r/2.
```

No incomplete-block estimate is claimed there.  The sparse Fourier
triangle majorant remains insufficient, and signed cancellation plus the
short/top-range budget are still open.  The result here is a global payment
repair, not a proof of Erdős #730.

The infinite reciprocal-prime-power summation and positive-real
root/monotonicity transfer remain paper-level exactly as in the original
near-payment intake; the Lean companion checks the expanded arithmetic
spine and endpoint constants only.

The hostile audit rebuilt the endpoint independently, checked the strict
natural-number boundary cases behind (2), compiled the Lean module, and
checked every public theorem against the kernel axiom gate.  The reported
dependencies are exactly `[propext, Classical.choice, Quot.sound]` or a
subset; there are no `sorry`, `admit`, `axiom`, `unsafe`, or
`native_decide` declarations.

## Reproduction

```bash
python3 -m pytest \
  compute730/campaign_uniform/repair/test_half_band_payment.py -q
python3 compute730/campaign_uniform/repair/half_band_payment.py
lake env lean ErdosProblems/Erdos730HalfBandPayment.lean
```
