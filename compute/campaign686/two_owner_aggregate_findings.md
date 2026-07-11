# Erdős 686 two-owner aggregate closure

## Result

`ErdosProblems/Erdos686TwoOwnerAggregate.lean` proves the full arithmetic
closure after the globally cleaned prime-power components have been grouped
into at most two residual-owner buckets.

The final equation-level theorem is

```lean
atMostTwoGlobalResidualOwners_below_cutoff
```

and has conclusion `d < 10^120`.  Its grouping hypothesis is the explicit
predicate

```lean
HasAtMostTwoGlobalResidualOwners k n d
```

which supplies positive `g,P,Q`, owner indices `i,j`, the factorization
`d=g*P*Q`, `Coprime P Q`, the exact row bound `g≤G_k`, factor divisibility at
the owners, and square divisibility in the two owner residuals.  `P=1` or
`Q=1` covers the zero- and one-nontrivial-owner cases.

## Exact row losses

| `k` | `G_k` |
|---:|---:|
| 5 | 108 |
| 7 | 1,620 |
| 9 | 136,080 |
| 11 | 1,224,720 |
| 13 | 242,494,560 |
| 15 | 18,914,575,680 |

The function `targetAggregateLoss` and theorem `targetAggregateLoss_table`
put these six values in the kernel-visible surface.

## Sharpened second obstruction

The new public theorem

```lean
aggregate_second_obstruction_abs_lt
```

proves the exact uniform estimate

```text
|3(Ct+4Dg²δ)| < 10¹⁶ g²
```

from `A≤35`, `t<A²g²`, `|C|,|D|<10¹²`, and `|δ|<15`.  Independent
exact evaluation of all 610 ordered target-row pairs gives row maxima

```text
16,512
751,248
74,507,904
8,634,643,200
1,422,568,811,520
368,002,448,916,480
```

before the `g²` factor, all strictly below `10¹⁶`.

If either second obstruction is nonzero, the Lean proof obtains

```text
d < A (10¹⁶)² g⁶.
```

At the worst exact budget this is

```text
160268311818898855770428923776425918589083124127638749184000000000000000000000000000000000000000
```

and is below `10^120`.

## Gcd-refined cubic branch

The module proves both exact Pell consequences

```text
gcd(P,b) | 3|δ|,
gcd(Q,a) | 3|δ|,
```

as `pell_left_gcd_dvd_three_natAbs` and
`pell_right_gcd_dvd_three_natAbs`.  The generic lemma
`dvd_scaled_of_dvd_mul_of_gcd_dvd` implements the cancellation

```text
m | Kb,  gcd(m,b) | D  ==>  m | KD.
```

Applied to the audited third local lift, the public theorem
`clean_third_zero_component_dvd_refined` gives

```text
P | 60|δ||E_i|g³
```

and the abstract closure applies the same theorem symmetrically to `Q`.
Consequently

```text
d ≤ 3600 |δ|² |E_i E_j| g⁷
  ≤ 3600 * 15² * (10¹²)² * G_k⁷
  < 10¹²⁰.
```

The worst coefficient-uniform Lean bound is

```text
701554217581018485144427969632122612578300735494193214835559445299200000000000000000000000000000000000
```

and the exact worst pair bound is the smaller

```text
93984078683194682557325451381987070845762855139556197071318510982175649195251213580361531392000000000.
```

## Dependency tree

```text
Erdos686GlobalResidualConcentration (frozen)
  per-prime clean component and loss exponent
                 |
                 v
finite prime-owner grouping                  [remaining bookkeeping lemma]
  constructs g,P,Q,i,j and g≤G_k
                 |
                 v
HasAtMostTwoGlobalResidualOwners
                 |
                 v
grouped_two_owner_equation_below_cutoff      [proved]
  |-- coincident owners: coprime square product
  `-- distinct owners:
       exact Pell identity
       second_order_local_lift               [frozen]
       third_order_local_lift                [frozen]
                 |
                 v
two_owner_abstract_buckets_below_cutoff      [proved]
  |-- nonzero second obstruction: 10^16 bound
  `-- simultaneous zero: gcd-refined g^7 bound
                 |
                 v
d < 10^120
```

## Exact remaining Lean composition gap

The only absent equation-level step is the following finite factorization
lemma.  It is stated here as one quantified obligation, not as an analytic or
target-strength assumption.

For a positive target-row solution, let `S=d.factorization.support`.  Suppose
there are `i,j∈[1,k]` and an owner map `o` such that for every `p∈S`, with

```text
e_p = d.factorization p,
t_p = globalResidualCleanExponent p e_p k,
```

the chosen owner satisfies

```text
p^t_p | n+o(p),
(p^t_p)² | globalLocalResidualNat n d (o(p)),
t_p=0 or o(p)=i or o(p)=j.
```

The remaining lemma is exactly

```text
forall k n d,
  targetRow(k) -> 0<d -> exactBlockEquation(k,n,d) ->
  the owner-map conditions above ->
  HasAtMostTwoGlobalResidualOwners k n d.
```

Its proof is finite bookkeeping: group `p^t_p` by `i,j`, put the complementary
`p^(e_p-t_p)` factors into `g`, use distinct-prime coprimality, and prove
`g≤G_k` from the six exact loss rows.  No second- or third-order theorem is
missing, and the grouped equation wrapper already consumes precisely this
conclusion.

## Verification

- `lake build ErdosProblems.Erdos686TwoOwnerAggregate`: PASS, 8,257 jobs.
- Nine public theorem axiom prints are contained in
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the module.
- The standalone exact verifier has nine tests.
- The combined dependency and new verifier suite has 28 passing tests.
- Named `d=1` telescopes and both recorded deep non-equations remain in the
  falsification checks.
