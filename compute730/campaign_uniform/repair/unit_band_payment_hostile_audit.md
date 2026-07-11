# Hostile audit: Erdős 730 full strict-band payment

Verdict: **PASS for the stated paper payment and kernel arithmetic spine.**
The strict natural-number band, maximality composition, dyadic endpoint, root
certificates, and rational payment all reproduce independently.  This is not
a Lean proof of the infinite prime-power aggregation, the positive-real
dyadic transfer, the remaining incomplete-block estimate, or Erdős 730.

## Frozen producer inputs

```text
c4bdabbb108a817be8fd8d49bc2211995833d56740bb3251dae077191d9e9964  ErdosProblems/Erdos730UnitBandPayment.lean
31d7fcdb3c3e1a65be78acf72ec2e4f34e6aac92f4911b428d019db45beec8b1  compute730/campaign_uniform/repair/unit_band_payment.py
7d0f3b0b872ffc7d91722f693e3bbeab0dfaabe0727f3140249b602a340a3f07  compute730/campaign_uniform/repair/test_unit_band_payment.py
116fbf44c47b31d303f332ec00dd9596fc3a8731d5a30cfc19b6178ec1c3e60c  compute730/campaign_uniform/repair/unit_band_payment_findings.md
```

The findings file differs from the audited producer snapshot only in its
status line, updated after this PASS from “audit pending” to “audit PASS”;
no mathematical statement or reproduction command changed.

Independent audit artifacts at the time of this report:

```text
a4b0303f742dfd296b0c0f947490507ed95575a9d656f2437521633cf653e057  ErdosProblems/Erdos730UnitBandPaymentAudit.lean
376e2638cded43f32bdced336f1b085b26ae8acfa16eb649781c66c8f453afbd  compute730/campaign_uniform/repair/unit_band_payment_hostile_verify.py
c27617a804ad5627e11c561a82423e787eace1e82079a3d26b125771f7e1c43c  compute730/campaign_uniform/repair/test_unit_band_payment_hostile_verify.py
```

The hostile verifier imports neither `unit_band_payment.py` nor the earlier
near-band calculator.

## Dependency tree and per-node verdict

```text
U1  s = max(2r-a,0), r>=1, s<r
 +-- U2  a>=2 and r+1<=a
 |    `-- U3  p^(r+1)<=p^a=q
 |
 +-- U4  residue count X<=q(N+1)
 |    +-- maximality N<p^(r+1) nextWeight
 |    +-- 1<=nextWeight<=globalWeight
 |    `-- U5  X<2 globalWeight q^2
 |
 +-- U6  q<=M and globalWeight=B^2
 |    `-- X<2B^2q^2, hence q>sqrt(X/(2B^2))
 |
 +-- U7  dyadic threshold and endpoint Y=3441480
 |    +-- paper-level infinite prime-power tail
 |    +-- paper-level positive-real dyadic transfer
 |    `-- exact endpoint payment <1/100
 |
 `-- U8  complement s>=r iff a<=r
```

- **U1: PASS.**  `UnitBandEnvelope` uses Lean natural subtraction, exactly
  `max(2r-a,0)`.  No integer-subtraction substitution is made without a case
  split.
- **U2: PASS.**  In fact, for every `r>=1`, `s<r` is equivalent to
  `r+1<=a`; `a>=2` follows immediately.
- **U3: PASS.**  Monotonicity of natural powers is used with `p>=1`.  The
  analytic theorem has the stronger premise `p>=5`.
- **U4-U5: PASS.**  Every cast, strict inequality, sign premise, and final
  multiplication was checked separately in exact rational arithmetic.
- **U6: PASS at paper level.**  For the analytic instantiation,
  `nextWeight=((r+1)log p)^2<B^2`, since `p^(r+1)<=q<=M` and
  `B=bit_length(M)`.  The Lean theorem correctly keeps `globalWeight`
  quantified rather than assuming logarithms.
- **U7: PASS with the formalization boundary retained.**  The endpoint is
  kernel checked.  The infinite sum and real-power propagation are not Lean
  theorems in this module and are explicitly identified as paper-level.
- **U8: PASS.**  The corrected remaining analytic range is exactly `s>=r`,
  equivalently `a<=r`, under the load-bearing premise `r>=1`.

## Strict natural-subtraction boundary

For positive `r`, the exact partition is

```text
max(2r-a,0) < r    iff    r+1 <= a,
max(2r-a,0) >= r   iff    a <= r.
```

Both branches of natural subtraction are covered:

- If `a<2r`, then `s=2r-a`, and `s<r` is exactly `r<a`.
- If `a>=2r`, then `s=0<r`, and automatically `r+1<=a`.

The transition is strict: `a=r` gives `s=r` and is unpaid, while `a=r+1`
gives `s=r-1` and is paid.  In particular `(a,r)=(1,1)` is outside the paid
band.  The audit-only Lean module proves both equivalences directly with
natural subtraction.

The independent verifier checks all `512^2=262144` positive pairs:

```text
paid:   130816,
unpaid: 131328,
prime-power comparisons checked: 915712.
```

It separately reproduces the producer's `160` by `160` paid count `12720`.

## Maximality composition and casts

Write `q=p^a` and `P=p^(r+1)`.  The exact implication used by the Lean
theorem is

```text
X <= q(N+1),
N < P*nextWeight,
1 <= nextWeight <= globalWeight,
P <= q

==>

N+1 < 2P*nextWeight,
X < q*(2P*nextWeight)
  <= q*(2P*globalWeight)
  <= q*(2q*globalWeight)
   = 2*globalWeight*q^2.
```

The first strict step uses `1<=P*nextWeight`; the last order step uses
`globalWeight>=0`, which follows from `nextWeight>=1`.  Natural-to-rational
casts preserve the count and power inequalities.  An independent grid of
600 exact `Fraction` fixtures reproduces every link; its smallest final
margin is `5625/7`.

In the paper instantiation, `globalWeight=B^2`, giving the claimed

```text
X < 2B^2q^2.
```

No root or logarithm appears in the kernel theorem.

## Dyadic monotonicity

On `2^m<=X<2^(m+1)`, the deliberately loose bounds are

```text
M=380808X+19 < 2^19X < 2^(m+20),
B<=m+20<m+21.
```

At `X=1`, the first strict inequality has integer margin
`2^19-380808-19=143461`.

The threshold base

```text
T_m = 2^m / (2(m+21)^2)
```

increases because

```text
2(m+21)^2-(m+22)^2 > 0.
```

The independent verifier checks 4040 successive steps, `57<=m<=4096`;
the smallest cleared margin is `5927`.  It also checks the cuberoot boundary
step

```text
4(m+21)^3-(m+22)^3 > 0
```

with minimum margin `1405169`, the square-root envelope after clearing
denominators, and the exact normalized ceiling-root boundary envelope on all
4040 steps.  These computations support, but do not replace, the explicitly
paper-level positive-real monotonicity argument for every `m>=57`.

## Independent endpoint reconstruction

The endpoint inputs are

```text
X0=2^57=144115188075855872,
M_upper=2^77=151115727451828646838272,
B=78,
B^2=6084.
```

The exact threshold floor is

```text
Y=3441480,
2*6084*Y^2 <= 2^57       with margin 17179868672,
2^57 < 2*6084*(Y+1)^2   with margin 66572000776.
```

Independent integer-root algorithms reproduce

```text
floor(sqrt(Y))=1855,
floor(cuberoot(Y))=150,
ceil(sqrt(2^77))=388736063997,
ceil(cuberoot(2^77))=53264341.
```

The paper-level reciprocal-tail proof is also checked at the rational
relaxation boundary.  For `a=2`, the integral-test envelope is `1/1855`,
below `2/1855`.  For `a>=3`, splitting bases at `floor(Y^(1/3))=150`
gives at most `2/150^2` from small bases and `1/150^2` from the integral
tail of large bases.  Thus the rational envelope used in the endpoint is
exactly

```text
4(2/1855+3/150^2)=3371/695625.
```

The boundary pair envelope is

```text
388736063997+78*53264341=392890682595,
4*392890682595/2^57
  =392890682595/36028797018963968.
```

Adding the two exact fractions gives

```text
121726379332007683003 / 25062531926316810240000
  < 1/100,
```

with cleared positive margin

```text
12889893993116041939700.
```

Every endpoint value agrees with the producer output.

## Kernel and forbidden-construct audit

The source and audit modules both rebuild:

```bash
lake env lean ErdosProblems/Erdos730UnitBandPayment.lean
lake env lean ErdosProblems/Erdos730UnitBandPaymentAudit.lean
```

The ten public producer theorems have the following axiom surfaces:

```text
unitBandEnvelope_forces_high_exponent:
  [propext, Classical.choice, Quot.sound]
unitBandEnvelope_prime_power_clearance:
  [propext, Classical.choice, Quot.sound]
cutoff_lt_of_unitBand_maximal:
  [propext, Classical.choice, Quot.sound]
unitBandDyadicThresholdBase_strictMono_step:
  [propext, Classical.choice, Quot.sound]
unitBand_endpoint_threshold_certificate:
  [propext, Classical.choice, Quot.sound]
unitBand_endpoint_sqrt_floor_certificate:
  [propext, Classical.choice, Quot.sound]
unitBand_endpoint_cuberoot_floor_certificate:
  [propext, Classical.choice, Quot.sound]
unitBand_endpoint_payment_identity:
  [propext, Classical.choice, Quot.sound]
unitBand_endpoint_payment_lt_one_percent:
  [propext, Classical.choice, Quot.sound]
unitBand_endpoint_payment_margin:
  [propext]
```

The three audit-only boundary theorems also report exactly
`[propext, Classical.choice, Quot.sound]`.  The producer Lean file contains
zero occurrences of `sorry`, `admit`, `axiom`, `native_decide`, `of_decide`,
`unsafe`, `implemented_by`, `extern`, or `noncomputable`.

## Claim boundary and exact remaining gate

The module does not formalize or claim:

- the infinite reciprocal-prime-power aggregation;
- the positive-real root and all-dyadic-range transfer;
- an incomplete-block estimate in the complement;
- the sparse Fourier short/top-range budget;
- Erdős 730.

After paying the strict band `s<r`, the exact complementary range is

```text
s>=r  iff  a<=r                    (r>=1).
```

No estimate for that range is supplied.  This is the single corrected
analytic intake boundary; the payment must not be described as a solution of
the uniform digit-count lemma.

## Reproduction

```bash
python3 -m pytest \
  compute730/campaign_uniform/repair/test_unit_band_payment.py \
  compute730/campaign_uniform/repair/test_unit_band_payment_hostile_verify.py \
  -q
python3 compute730/campaign_uniform/repair/unit_band_payment.py
python3 compute730/campaign_uniform/repair/unit_band_payment_hostile_verify.py --pretty
lake env lean ErdosProblems/Erdos730UnitBandPaymentAudit.lean
```
