# Erdős #730: stronger affine-progression obstruction

Status: **independent hostile audit PASS; exact counterexample.**

The separated far-range signed inequality currently recorded as equation
(20) in `far_range_findings.md` is false.  The earlier near-affine
construction loses an unnecessary factor: once the low `s` output digits
are fixed, one should pigeonhole only the remaining restricted word modulo
the fixed affine coefficient.

## Exact construction

On the Q branch write

```text
G(k)=A p^a k^2+(p^a u+b)k+v  (mod p^(2r)),
b=1,301,094,
s=2r-a.
```

For every integer `j`, exact subtraction gives

```text
G(k0+p^s j)=G(k0)+b p^s j  (mod p^(2r)).          (1)
```

Indeed the omitted term is

```text
p^a p^s j (A(2k0+p^s j)+u),
```

and `a+s=2r`.

Fix the low `s` output digits to `1,0,...,0`; this retains exact valuation
on Q because its forbidden least digit is zero.  Among the `H^(r-s)`
restricted words `z` of length `r-s`, one residue class modulo `b` contains
at least

```text
ceil(H^(r-s)/b)                                  (2)
```

words.  Choose `G(k0)=1+p^s rho` for that residue class, using the banked
p-adic permutation lemma.  Equation (1) then realizes every output

```text
1+p^s z < p^r.
```

Its first `r` digits are restricted, its upper `r` digits are zero, and its
least digit is not forbidden.  All corresponding parameters lie in a span
strictly shorter than `p^r`, so they fit inside an interval of the critical
length `ceil(p^r(log p^r)^2)`.

The hostile checker reconstructs the least Q-branch root `x0 mod p^a`,
checks `380808*x0+13=p^a*c0`, and compares the exact expanded polynomial
with `Phi_Q(c0+380808k)`.  It also checks that output least digit `1` is
realized and forces `c0+380808k` to be nonzero modulo `p`.  Thus the fixed
low digit is the exact-valuation guard, not an extra unproved condition.

This gives a lower/main ratio, up to the fixed `b` and polynomial factors,

```text
p^r / H^(r+s).                                   (3)
```

It diverges whenever

```text
s/r < theta_p := log_H(p/H) = kappa_p/(1-kappa_p). (4)
```

This is a strictly wider obstruction band than the previously recorded
`s/r<kappa_p`.

## Explicit exact witness

Take

```text
p=5, H=3, r=432, s=176=(11/27)r, a=688.
```

The tuple lies in the advertised separated range.  After cancelling the
common multiple sixteen, the exact certificate is

```text
3^324 > 5^219,                                   (5)
```

which is equivalent to `s>(kappa_5+1/12)r`.  It remains inside the stronger
obstruction band because

```text
5^27 > 3^38.                                     (6)
```

The construction supplies at least

```text
106839669060916991981317096835172019173264076852655640554490931808183015700453953320053561967167329587110282224457956
```

exact-valuation hits.  Rational atanh-series bounds for `log 5` prove, with
integer-cleared arithmetic, that this is more than the whole proposed
zero-error RHS at the critical interval length; the certified ratio is
greater than `1.164`.

Indeed, if (20) held, the exact Fourier identity and
`delta_E=(1-1/H)(H/p)^(2r)` would give

```text
count <= delta_E*N + (H/p)^(2r)*N*(1/H+1/Lambda)
      =  (H/p)^(2r)*N*(1+1/Lambda).
```

The exact lower bound above exceeds a rigorous rational upper bound for
this last quantity.  Hence the witness refutes (20) itself, not merely a
triangle-inequality proof of it.

## Consequence and exact remaining gate

This does not refute Erdős #730, nor does it rule out a globally payable
explicit `E_far`.  It refutes the proposed signed inequality (20) and shows
that the current near/far cut cannot assign zero error immediately above
`(kappa_p+1/12)r`.  A repaired campaign must either

1. extend the valuation payment through at least the new band
   `s/r<theta_p`, with a fresh exact global budget; or
2. retain an explicit error term at least as large as (2) on these
   progressions and prove that its normalized family sum is affordable.

## Reproduction

```bash
python3 -m pytest \
  compute730/campaign_uniform/repair/far/test_stronger_affine_counterexample.py -q
python3 compute730/campaign_uniform/repair/far/stronger_affine_counterexample.py
```

No floating-point quantity enters the verdict.
