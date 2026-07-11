# Hostile audit: Erdős 686 two-owner aggregate checkpoint

Status: **PASS for the exact conditional two-owner closure.**  The module
proves that an exact target-row solution equipped with
`HasAtMostTwoGlobalResidualOwners` has `d < 10^120`.  It does **not** construct
that predicate from the per-prime concentration theorem and therefore does
not yet prove that every target-size solution has at least three cleaned
residual owners.

## Frozen artifacts

```text
ErdosProblems/Erdos686TwoOwnerAggregate.lean
  35959fee7b3080b2d0a91885a7a465455fcbed4ead9ecc1d652024ec7eabe009
compute/campaign686/two_owner_aggregate_verify.py
  4d1bb7f5a721298218f61d0927e0bb0adfd9371f4f910d4daac291aa55b9b032
compute/campaign686/test_two_owner_aggregate_verify.py
  8b22cc46344cbdb2285adc2832a14af1c93ff95274cd48778de52a948d5eaf92
compute/campaign686/two_owner_aggregate_findings.md
  0bb0f41955b0acf5ea2b24d92347400f43514e1be721c3d26ab6cb0c099f2115
docs/plans/2026-07-10-erdos686-two-owner-aggregate.md
  14390b977e46e02a4a1e742b659005ff79e77ca28a8183ab8c2c6f1c6d5154f6
compute/campaign686/two_owner_aggregate_hostile_verify.py
  6eea5d242e71ab7a645b37c932823dfb9c3a9e36d0fc5875eff167bd8d7b13b7
compute/campaign686/test_two_owner_aggregate_hostile_verify.py
  123f5f84788c5a4ba966aa5b583ada61f8d39b5c61920c40596c2421fde54dfb
```

The dependency hashes embedded in the Lean source also match the previously
hostile-audited files:

```text
Erdos686GlobalResidualConcentration.lean
  495981605282c4a1963f95bdce0788b4baba6cfa05c8be00b8c57154f49f9e24
Erdos686GlobalResidualTwoPrime.lean
  ca1a59a8e3cef454d9255a8fd70dff3d7c516492bd4c379b097e711ef24c060d
```

## Exact theorem surface and dependency tree

There are nine public theorems:

```text
targetAggregateLoss_table
aggregate_second_obstruction_abs_lt
dvd_scaled_of_dvd_mul_of_gcd_dvd
pell_left_gcd_dvd_three_natAbs
pell_right_gcd_dvd_three_natAbs
clean_third_zero_component_dvd_refined
two_owner_abstract_buckets_below_cutoff
grouped_two_owner_equation_below_cutoff
atMostTwoGlobalResidualOwners_below_cutoff
```

The grouping predicate is a definition, not a theorem:

```text
HasAtMostTwoGlobalResidualOwners k n d :=
  exists g P Q i j,
    d = g*P*Q and 0<g and 0<P and 0<Q and Coprime P Q and
    g <= targetAggregateLoss k and i,j in [1,k] and
    P | n+i and Q | n+j and
    P^2 | localResidual n d i and Q^2 | localResidual n d j.
```

The final theorem takes this predicate as an explicit hypothesis.  There is
no declaration in the module deriving it from the equation or from per-prime
owners.

```text
atMostTwoGlobalResidualOwners_below_cutoff
`- unwrap HasAtMostTwoGlobalResidualOwners
   `- grouped_two_owner_equation_below_cutoff
      |- exact equation plus banked row window
      |- same owner
      |  `- coprime square product and d < A*g^2
      `- distinct owners
         |- positive residual coefficients a,b
         |- a*P^2-b*Q^2 = 3(i-j)
         |- frozen second and third local lifts
         `- two_owner_abstract_buckets_below_cutoff
            |- one second obstruction nonzero
            |  `- d < A*(10^16)^2*g^6
            `- both second obstructions zero
               |- Pell gcd divisibilities
               |- generic gcd cancellation
               |- P | 60*|delta|*|E_i|*g^3 and symmetric Q result
               `- d <= 3600*|delta|^2*|E_i E_j|*g^7
```

The abstract theorem requires distinct owners.  The grouped wrapper handles
coincident owners before calling it.  `P=1` and `Q=1` remain legal throughout.

## Independent kernel gate

- A fresh direct source compilation emitted a 1.4 MiB `.olean` and 59 KiB
  `.ilean` under `/tmp`.
- `lake build ErdosProblems.Erdos686TwoOwnerAggregate` completed all 8,257
  jobs successfully.
- Standalone `#check` reproduced the exact public signatures above, including
  every factor, cast, positivity premise, coprimality premise, and the explicit
  grouping hypothesis of the final theorem.
- `#print axioms` on all nine public theorems is a subset of
  `[propext, Classical.choice, Quot.sound]`.  The loss-table theorem needs only
  `propext`; the other eight report the full allowed set.
- A nested-comment-aware code scan finds no executable `sorry`, `admit`,
  `native_decide`, `axiom`, or `unsafe` declaration.
- The four private declarations are proved cutoff lemmas, not assumptions:
  `aggregate_gap_lt_of_nonzero_second_obstruction`,
  `aggregate_one_owner_numeric_cutoff`,
  `aggregate_generic_numeric_cutoff`, and
  `aggregate_third_numeric_cutoff`.

## Independent exact arithmetic

The hostile verifier imports no producer verifier code.  It recomputes the
losses from Legendre valuations and obtains exactly

| `k` | `G_k` |
|---:|---:|
| 5 | 108 |
| 7 | 1,620 |
| 9 | 136,080 |
| 11 | 1,224,720 |
| 13 | 242,494,560 |
| 15 | 18,914,575,680 |

These values agree with every Lean table entry.  Primes at least `k` have
zero loss exponent; the remaining grouping proof must make that fact and the
finite product over `d.factorization.support` explicit.

The coefficient-only obstruction estimate is

```text
3 * (10^12*35^2 + 4*10^12*15)
= 3,855,000,000,000,000
< 10,000,000,000,000,000,
```

with exact margin `6,145,000,000,000,000`.

All 610 ordered distinct-owner pairs were independently recomputed.  The six
second-obstruction maxima are

```text
16,512
751,248
74,507,904
8,634,643,200
1,422,568,811,520
368,002,448,916,480.
```

The largest exact pairwise generic cutoff is

```text
217044647287343042885059609316395849093627507558461004041714015187255309475392782336000000000
```

and the largest exact cubic pair cutoff is

```text
93984078683194682557325451381987070845762855139556197071318510982175649195251213580361531392000000000.
```

The looser kernel-uniform worst-row cutoffs also reproduce exactly:

```text
generic:
160268311818898855770428923776425918589083124127638749184000000000000000000000000000000000000000

cubic:
701554217581018485144427969632122612578300735494193214835559445299200000000000000000000000000000000000.
```

Every value is strictly below `10^120`.  The one-owner worst-row cutoff is
only `12,521,641,060,405,661,184,000`.

## Gcd, sign, and zero-boundary audit

The independent verifier covers cases the producer test intentionally did not
enumerate:

- `dvd_scaled_of_dvd_mul_of_gcd_dvd`: 37,373 premise-satisfying cases over
  `0 <= m,b,K,D <= 20`, including 107 with `m=0`, 1,827 with `b=0`, 6,635
  with `K=0`, and 3,236 with `D=0`;
- both Pell gcd theorems: 13,073 exact Pell identities with 6,126 negative,
  821 zero, and 6,126 positive `delta`, including zero values of each natural
  input;
- the refined cubic implication: 107,496 cases with negative, zero, and
  positive `E`, negative, zero, and positive `delta`, `P=1`, `Q=0`, and
  `a=0`.  The exact factor `60=20*3` and both absolute values are necessary
  for the stated cancellation route; for example the generic cancellation
  data `(a,b,P,Q,delta,g,E)=(0,3,3,1,-1,1,-5)` fails if the factor three is
  deleted;
- same-owner algebra: 68,880 cases, including 13,541 each with `P=1` and
  `Q=1`, and 1,200 with both unit;
- abstract distinct-owner data: 40,916 fixtures with `P=Q=1` and 14,487
  fixtures in each one-unit orientation.  Both signs of the owner difference
  occur.

The finite factorization arithmetic was separately exercised on every
two-bucket assignment for `1 <= d <= 2000` in all six rows: 64,866 assignments
all satisfy `d=g*P*Q`, `Coprime P Q`, and `g<=G_k`, including empty and
one-unit cleaned buckets.  This is evidence for the remaining bookkeeping
lemma, not a substitute for its Lean proof.

The producer tests pass (`9 passed`), the independent hostile tests pass
(`10 passed`), and the combined dependency, producer, and hostile suite passes
`38 tests`.

## Findings-language audit

The findings are scoped correctly.  They say the arithmetic closure is
complete **after** globally cleaned prime powers have been grouped into at
most two owners.  Their dependency tree labels finite prime-owner grouping as
remaining, their final theorem displays `HasAtMostTwoGlobalResidualOwners` as
a hypothesis, and they never claim that the current module itself forces
three owners in a target-size solution.

The phrase "only absent equation-level step" is acceptable because the row
window and per-prime concentration are already frozen dependencies.  The
remaining step is finite factorization, finite choice of owners, coprime
product assembly, and the exact loss-product bound.  It is a proper lemma and
does not restate the Diophantine target.

## Exact remaining gap

A precise stronger-than-needed pure-bookkeeping form is the following single
quantified lemma.  It does not need to assume the block equation once the
per-prime owner data are supplied.

```text
For every target row k, naturals n,d with 0<d, indices i,j in [1,k], and
owner map o on d.factorization.support, put

  e_p = d.factorization p,
  t_p = globalResidualCleanExponent p e_p k.

If, for every p in d.factorization.support,

  o(p) in [1,k],
  p^t_p | n+o(p),
  (p^t_p)^2 | localResidual n d (o(p)), and
  t_p=0 or o(p)=i or o(p)=j,

then HasAtMostTwoGlobalResidualOwners k n d.
```

The proof must group the retained prime powers by `i,j`, place every
complementary `p^(e_p-t_p)` in `g`, prove `d=g*P*Q`, pairwise coprimality,
the factor and square product divisibilities, and `g<=G_k`.  Until this lemma
is kernel-banked and composed with finite owner choice, the correct conclusion
is only the conditional closure audited here, not an unconditional
three-owner restriction.

## Verdict

**PASS.**  No mathematical, computational, kernel, or scope defect was found
in the frozen checkpoint.  The exact remaining gap is the finite grouping
lemma above; the producer findings expose it honestly and do not count it as
proved.
