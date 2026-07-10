# Erdős #730 corrected gate: separated far-range Fourier audit

Date: 2026-07-10

Verdict: **the exact Fourier reduction and sparse quadratic completion are
proved, but the proposed signed bilinear inequality (20) is false.**  The
valuation-stratified triangle majorant is exponentially over budget for each
fixed `p=5,7,11`; more decisively, an exact translated-interval construction
at `p=5,r=432,s=176,a=688` violates (20) by a factor greater than
`1.164314`.  See `stronger_affine_counterexample_findings.md`.

This file makes no far-range estimate, global first-moment closure, or
Erdős #730 claim beyond the proved proper long-interval subrange in
Section 7 and the finite exact hostile checks in Section 8.  The corrected
analytic intake starts at `s>=r/2`; the complementary half-band `2s<r` is
paid arithmetically in `../half_band_payment_findings.md`.

## 1. Exact-valued restricted output set

Fix a relevant prime `p>=5`, put

```text
H=(p+1)/2,  m=2r,  Q=p^m,
G(k)=A p^a k^2+(p^a u+b)k+v,
A=84,591,927,504=2^4*3^5*7*41^2*43^2,
p does not divide b.
```

The exact valuation condition is itself one output-digit deletion.  If
`p | c(k)`, then the least digit of `G(k)` is

```text
d_*=0       on P and Q,
d_*=(p-1)/2 on R and S.
```

For P/Q this follows from `Phi(0)=0`; for R/S it follows from
`Phi(0)=-1/2=(p-1)/2 mod p`.  Thus an exact-valuation obstruction is
equivalent to

```text
G(k) mod Q belongs to E=E(p,m,d_*),
```

where every one of the `m` digits lies in `{0,...,H-1}` and the least
digit is not `d_*`.  Consequently

```text
|E|=(H-1)H^(m-1),
delta_E=|E|/Q=(1-1/H)(H/p)^m.                    (1)
```

This exact deletion is useful: the requested upper bound uses the larger
density

```text
delta=(H/p)^m.                                    (2)
```

## 2. Exact Fourier identity

Use `e_Q(z)=exp(2 pi i z/Q)` and define

```text
F(h)=sum_{y in E} e_Q(-hy),
S_I(h)=sum_{k in I} e_Q(hG(k)),
```

for an integer interval `I` of length `N`.  Fourier inversion gives the
identity

```text
#{k in I:G(k) mod Q in E}
 = delta_E N + Q^(-1) sum_{h=1}^{Q-1} F(h)S_I(h). (3)
```

The sum on the right is real after pairing `h` with `Q-h`.

The digit product also gives an exact cumulative energy formula.  For
every `0<=j<m`, subgroup Parseval yields

```text
sum_{p^j | h} |F(h)|^2
 = Q|E|(H/p)^j.                                   (4)
```

Proof: summing only frequencies divisible by `p^j` forces two elements of
`E` to agree modulo `p^(m-j)`.  There are
`(H-1)H^(m-j-1)` possible low strings and `H^j` independent high strings
on each side, giving exactly

```text
p^(m-j) (H-1) H^(m+j-1)=Q|E|(H/p)^j.
```

The tests reproduce (4) using integer collision counts, not numerical
Fourier transforms.

## 3. Exact sparse Gauss completion

Fix `h!=0`, let

```text
j=v_p(h),
n=m-j,
h=p^j h_0 with p not dividing h_0,
nu_p=v_p(A),
tau=min(n,a+nu_p),
d=n-tau=max(m-j-a-nu_p,0).                        (5)
```

The relevant values are

```text
nu_5=0,  nu_7=1,  nu_11=0.                        (6)
```

The `nu_7=1` loss is load-bearing for exact constants; P and R have no
7-adic branch root, but Q and S do.

Complete `S_I(h)` modulo `P=p^n`.  If

```text
V_I(t)=sum_{k in I} e_P(-tk),
```

then

```text
S_I(h)=P^(-1) sum_{t mod P} V_I(t)
        * sum_{x mod P} e_P(h_0 A p^a x^2+(h_0 beta+t)x),  (7)
beta=p^a u+b.
```

For odd `p`, the inner Gauss sum has the following exact support and
magnitude.

If `tau<n`, it vanishes unless

```text
t=-h_0 beta mod p^tau.                            (8)
```

On that single residue class its squared magnitude is

```text
p^(n+tau).                                        (9)
```

If `tau=n`, the quadratic term vanishes modulo `P`; the complete sum
vanishes except at `t=-h_0 beta mod P`, where its magnitude is `P`.

The exact tests verify the cyclotomic equalities behind (8)--(9) for all
714 completion frequencies in the cases

```text
(p,n,tau)=(5,3,0),(5,3,1),(7,3,2),(11,2,2).
```

No floating approximation to a root of unity is used.

## 4. Explicit per-frequency incomplete-sum bound

Suppose first that `d=n-tau>=1`.  The class in (8) contains `p^d`
frequencies.  Since `a>=1`, this case has `tau>=1`; moreover
`h_0 beta` is a unit modulo `p`.  The support residue is therefore a
genuine unit class modulo `p^tau` and cannot contain zero.  For a centered
nonzero residue `t`,

```text
|V_I(t)| <= min(N,P/(2|t|)).                      (10)
```

On each side of zero, retain the first point at cost `N`; subsequent
distances are at least `ell p^tau`.  Hence, with
`R=p^d`,

```text
sum_{t satisfying (8)} |V_I(t)|
 <= 2N + R(1+log R).                              (11)
```

Combining (9) and (11) proves

```text
|S_I(h)| <= B_j(N),                               (12)

B_j(N)=min(
  N,
  2N p^(-d/2)+p^(d/2)(1+d log p)
)                                                 (d>=1).
```

When `d=0`, the phase is linear with unit coefficient at conductor
`p^n`, so the geometric-series bound gives

```text
B_j(N)=min(N,p^n/2).                              (13)
```

Equations (12)--(13), including every constant, are the strongest bounds
obtained here from support sparsity plus termwise absolute completion.

## 5. Why the triangle majorant still fails

Let

```text
L_j=sum_{v_p(h)=j}|F(h)|.
```

Equations (12)--(13) give the valid absolute majorant

```text
|sum_{h!=0}F(h)S_I(h)| <= sum_{j=0}^{m-1} L_j B_j(N).      (14)
```

This bound is not merely missing a favorable constant.  Put

```text
s=max(m-a,0),
t=max(s-nu_p,0).
```

For every `j<t`, one has `d=t-j>=1`.  If `N>=8`, both entries in the
minimum defining `B_j` are at least `2sqrt(2N)`; for the second entry this
is AM-GM, and `N>=2sqrt(2N)` for the trivial entry.  From (4) and
`|F(h)|<=|E|`,

```text
sum_{v_p(h)<t}|F(h)|
 >= Q(1-(H/p)^t).                                 (15)
```

Therefore the right side of (14), as an explicit proof majorant, is at
least

```text
2sqrt(2N) Q(1-(H/p)^t).                           (16)
```

The entire allowance between the exact mean in (1) and the requested
bound

```text
delta N(1+1/log(p^r))
```

is only

```text
N H^m (1/H+1/log(p^r))                            (17)
```

before division by `Q` in (3).

At the critical length

```text
N=ceil(p^r(log(p^r))^2),
```

the ratio of (16) to (17) has exponential factor

```text
p^((2kappa_p-1/2)r),
kappa_p=log_p(p/H).                               (18)
```

For `p=5,7,11`, positivity of this exponent is certified without
logarithms by

```text
p^3>H^4:
125>81, 343>256, 1331>1296.                       (19)
```

The remaining factors in (16)/(17) are polynomial in `r`, while in the
separated range `t` grows linearly with `r`; hence (16)/(17) tends to
infinity for each of these three fixed primes.

Conclusion: applying triangle inequality after the exact sparse Gauss
completion cannot prove the far estimate for the diagnostic primes.  This
does **not** show the true Fourier error is large.  It proves that signed
cancellation between distinct `h` is indispensable.

## 6. The exact remaining exponential-sum inequality

Write

```text
Lambda=log(p^r)=r log p.
```

By (1)--(3), the requested far estimate follows exactly from the single
signed inequality

```text
Re sum_{h=1}^{Q-1} F(h)S_I(h)
 <= N H^m (1/H+1/Lambda).                         (20)
```

Here all quantities, maps, interval quantifiers, and Fourier coefficients
are explicit above, and the range is

```text
N>=p^r Lambda^2,
s>= (kappa_p+1/12)r.                              (21)
```

Inequality (20) is **OPEN**.  Bounding each term absolutely reduces it to
the failed majorant (14), so a proof must preserve cancellation across
completion frequencies or across Fourier frequencies.  Calling that
cancellation “square-root” without proving (20), with its digit-set
weights and uniform interval start, would be theorem-strength handwaving.

## 7. A proved proper subrange

There is one unconditional, but noncritical, interval range.  Periodicity
and the permutation property give exactly `|E|` hits in each full block of
length `Q`.  For an arbitrary interval of length `N`, full-period
decomposition gives

```text
count <= delta_E N+|E|.                           (22)
```

If

```text
N >= (H-1)Q,                                      (23)
```

then `|E|<=delta N/H`.  Equations (1), (2), and (22) yield

```text
count <= delta N
      <= delta N(1+1/log(p^r)).                   (24)
```

Intervals whose length is a multiple of `Q` satisfy the exact mean with
no condition (23).  This proper subrange is far longer than the critical
`p^r(log(p^r))^2` scale and therefore does not close the campaign gate.

## 8. Exact finite hostile checks

The checker certifies the integer ceiling

```text
N=ceil(p^r(log(p^r))^2)
```

using rational atanh-series bounds for `log p`; the tested lengths are

```text
p=5:  13, 260, 2915, 25903       (r=1,...,4),
p=7:  27, 743, 11690             (r=1,...,3),
p=11: 64, 2783, 68879            (r=1,...,3).
```

For every admissible branch/root and every exponent `a` in the exact
separated range, it scans all cyclic interval starts modulo `Q`, retaining
the exact valuation.  Results:

```text
104 branch/prime/r/a rows,
0 rows above the uninflated main term delta N.
```

The closest row is

```text
p=11, r=1, branch=R, a=1, s=1,
N=64, start=51, max hits=19,
(max hits)/(delta N)=2299/2304.
```

These are exact integer comparisons after multiplying by `Q`; they are
evidence against a small counterexample, not an extrapolation to all `r`,
`p`, or interval lengths.

## 9. Dependency tree and verdicts

```text
F0  Critical separated-range incomplete-block estimate              OPEN
 |
 +-- F1  Exact valuation is one allowed-output-digit deletion        PROVED
 +-- F2  Fourier identity (3)                                        PROVED
 +-- F3  Cumulative Fourier energy (4)                               PROVED
 +-- F4  Sparse Gauss support and exact magnitude (8)--(9)           PROVED
 +-- F5  Per-frequency bound with constants (12)--(13)               PROVED
 +-- F6  Valuation-stratified triangle majorant (14)                 VALID BUT INSUFFICIENT
 |    `-- exponentially over budget for p=5,7,11                    PROVED
 +-- F7  Signed bilinear cancellation inequality (20)                FALSE
 |    `-- p=5,r=432,s=176,a=688 exact translated witness             EXACT-CHECKED
 +-- F8  Long intervals N>=(H-1)Q                                   PROVED
 `-- F9  Exact finite hostile grid, 104 rows                         EXACT-CHECKED

G0  Full half-band 2s<r payment <1/100 for X>=2^57       LEAN-BANKED/EXACT-CHECKED
G1  Short/top-range payment                                          NOT CLAIMED
G2  Combined first-moment budget                                     NOT CLAIMED
```

## 10. Reproduction

```bash
python3 -m pytest compute730/campaign_uniform/repair/far/test_far_fourier.py -q
python3 compute730/campaign_uniform/repair/far/far_fourier.py
```

All finite assertions use integer or rational arithmetic.  NumPy is used
only for exact `int64` map values and window counts on moduli at most
`11^6=1,771,561`; no floating-point Fourier transform enters a verdict.
