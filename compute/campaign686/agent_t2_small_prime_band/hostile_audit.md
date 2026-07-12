# Hostile audit: crossing band and lower-owner prime-power obstructions

Verdict: **PASS as several kernel-checked unbounded Target 2 subfamilies;
FAIL as complete Target 2 closure.**

The originally proposed all-prime, any-position argument is false.  This audit
freezes exact counterfixtures and states only the corrected theorem surfaces.

## Exact exported surfaces

Source: `ErdosProblems/Erdos686SmallPrimeBand.lean`.

The strongest valuation core is:

```lean
theorem no_four_solution_lower_prime_power_of_upper_between_of_factorial_loss_le
    {p k n d i A : ℕ}
    (hp : p.Prime) (hi : i ∈ Finset.Icc 1 k)
    (howner : n + i = p ^ A)
    (hupperLo : p ^ A < n + d + 1)
    (hupperHi : n + d + k < 2 * p ^ A)
    (hfactorialLoss :
      (k - 1).factorial.factorization p ≤
        (4 : ℕ).factorization p +
          (localBlockCoefficientNat k i).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n
```

Its target-facing form replaces the two explicit interval inequalities by
`k>=16`, `k<=d`, and the banked equation consequence `9d<n`:

```lean
theorem no_gap_solution_lower_term_prime_power_of_factorial_loss_le
```

Three unconditional corollaries are exported:

```lean
theorem no_gap_solution_lower_block_starts_at_prime_power
theorem no_gap_solution_lower_term_prime_power_base_gt_length
theorem no_gap_solution_lower_block_ends_at_prime_power
```

They cover respectively `i=1` for every prime, every `i` when `p>k`, and
`i=k` for every prime.  The power-of-two endpoint specialization is retained:

```lean
theorem no_gap_solution_lower_block_ends_at_two_power
```

The separate owner-transfer core is:

```lean
theorem no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
    {p k n d i A a : ℕ}
    (hp : p.Prime) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (hA : 1 ≤ A)
    (howner : n + i = a * p ^ A)
    (hsize : a * (d + k - 1) < n + i) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n
```

The current ratio estimate supplies a concrete corollary for every `a<=4`:

```lean
theorem no_gap_solution_lower_term_small_cofactor_prime_power_base_gt_length
```

## Dependency tree

```text
general split-factorial valuation core
|
+- lower owner n+i=p^A
|  +- local cofactor contains two consecutive side blocks
|  +- (i-1)!*(k-i)! divides that cofactor
|  `- lower valuation >= A+v_p((i-1)!(k-i)!)
|
+- explicit upper interval p^A < upper terms < 2p^A
|  `- every upper owner valuation is <A
|
+- banked upper valuation concentration
|  `- upper valuation < A+v_p((k-1)!)
|
`- exact loss premise
   `- upper < v_p(4)+lower, contradicting factorization of the equation

target-facing split-factorial theorem
|
+- banked exact equation consequence 9d<n
`- derives both explicit upper interval inequalities

unconditional corollaries
|
+- i=1: local coefficient=(k-1)!
+- i=k: descending endpoint proof with full factorial baseline
`- p>k: v_p((k-1)!)=0 for every i

small-cofactor owner-transfer core
|
+- p^A divides lower owner and hence lower block
+- equation transfers p^A to upper block
+- p>k localizes p^A in one upper owner
+- owner subtraction gives p^A | d+j-i and p^A<=d+k-1
`- n+i=a*p^A<=a(d+k-1), contradicting explicit size premise

a<=4 target corollary
`- 9d<n and k<=d give 4(d+k-1)<n<n+i
```

## Per-node verdicts

| Node | Verdict | Reason |
|---|---|---|
| Block/ascending-factorial reindexing | PASS | Exact Finset bijections in Lean. |
| Split local coefficient divides local cofactor | PASS | The two side products are divisible by `(i-1)!` and `(k-i)!`. |
| Lower split valuation baseline | PASS | Exact prime-power divisibility; no equality is overclaimed. |
| Upper interval `(p^A,2p^A)` | PASS | Explicit hypotheses in the core; `9d<n` only in the target wrapper. |
| No full `p^A` upstairs | PASS | Any multiple strictly above `p^A` is at least `2p^A`. |
| Upper concentration | PASS | Existing kernel theorem with exact loss `v_p((k-1)!)`. |
| Split-factorial sufficient condition | PASS | Kernel-checked strict valuation contradiction. |
| Every position for `p>k` | PASS | The factorial loss is exactly zero. |
| Both endpoint positions for all primes | PASS | Full `(k-1)!` lower baseline; explicit first- and last-position theorems. |
| Small cofactor `a<=4`, `p>k` | PASS | Exact owner transfer and exact `9d<n` size calculation. |
| All primes at every internal position | **FALSE by this route** | Exact fixtures meet the required local quotient-four valuation. |
| Target 2 | OPEN | General composite lower terms and corrected small-prime internal owners remain. |

Every proved node is in the Lean dependency graph.  Private helpers are proved
declarations in the same source, not assumptions or inaccessible external
lemmas.

## Quantified correction: no hidden “essentially” phrase

At a lower owner `n+i=p^A`, the exact baseline is

```text
A + v_p((i-1)!) + v_p((k-i)!),
```

whereas upper concentration loses `v_p((k-1)!)`.  The exact sufficient
condition is

```text
v_p((k-1)!)
  <= v_p(4) + v_p((i-1)!) + v_p((k-i)!).
```

Equivalently, the missing binomial valuation
`v_p(binomial(k-1,i-1))` must be at most `v_p(4)`.  The Lean statement uses
`localBlockCoefficientNat k i=(i-1)!(k-i)!` directly and does not rely on an
unformalized binomial rewrite.

The owner-transfer core uses the exact external size premise

```text
a*(d+k-1) < n+i.
```

The present target corollary instantiates it only for `a<=4`.  It does not
claim that 4 is optimal, and a sharper future ratio bound can raise it without
changing the transfer proof.  In particular, `3*k*d<5*n` and `10*a<=3*k`
would imply the size premise through `d+k-1<2d`; that forthcoming window is
neither assumed nor reproved here.

## Boundary and falsification record

### `p=2`: multiplier-prime internal counterfixture

```text
(p,A,k,d,i,n) = (2,9,33,33,2,510)
9d=297<n
v_2(lower)=35, v_2(upper)=37, discrepancy=2=v_2(4).
```

This exactly satisfies the local valuation demanded by the equation.  It is
not a full equation solution.  Here the split-factorial condition fails, so
the corrected theorem does not apply.

### Odd `p`: internal counterfixture

```text
(p,A,k,d,i,n) = (3,5,16,19,8,235)
9d=171<n
v_3(lower)=9, v_3(upper)=9, discrepancy=0=v_3(4).
```

Again this is a local valuation fixture, not a product-equation solution.  It
falsifies the uncorrected odd-prime extension and lies outside the exact loss
premise.

### Positions `i=1` and `i=k`

At either endpoint the split coefficient is `(k-1)!`; therefore the loss
condition holds for every prime.  `no_gap_solution_lower_block_starts_at_prime_power`
and `no_gap_solution_lower_block_ends_at_prime_power` bank both boundaries
separately.  No symmetry is merely asserted in prose.

### Small exponents

The explicit interval core handles `A=0` whenever its hypotheses are
consistent.  The owner-transfer theorem requires `A>=1`, because localization
of a nontrivial prime power needs a positive exponent.  This premise is
displayed and never inferred silently.

### Named row-prefix fixtures

- `(984,3177026,4480)` lies in exact band `[3176708,3177690]`, fails first at
  `p=2` with discrepancy `0`, and has exactly 63 lower prime-power positions.
- `(244,48502,277)` lies in exact band `[48373,48615]`, fails first at `p=2`
  with discrepancy `-5`, and has exactly 20 lower prime-power positions.

Every detected prime power in both lower blocks has exponent one and prime
base larger than `k`; no composite prime power occurs.  The points are not
equation solutions.  The counts are exact trial-division reproductions, not a
uniform density claim.

### Structured small-prime survivors

The exact scan leaves four points among 294 structured rows:

```text
(k,d,n) = (16,80,878), (21,273,3996),
          (25,325,5688), (30,90,1877).
```

They are crossing-band plus small-prime-filter survivors only.  They prevent
promotion of the scan to a universal theorem.

### Crossing-band width

For `k>=3,d>=k`, the exact band has width `k-1`.  Equality at the common
threshold would force `k(v_2(a)-v_2(b))=2` for a reduced rational `a/b`, which
is impossible.  No floating root is used.

## Computational independence

The scanner uses integer powers, monotone binary search, Legendre floor sums,
and direct integer products.  Duplicate valuation calculations use the
explicit four-floor sum over prime powers.

The focused tests cover:

- endpoint arithmetic for `p=2,3,5,7` and exponents `1,...,4`;
- both internal counterfixtures;
- every position in three representative `p>k` rows;
- coefficients `1<=a<=4` at every position in a representative large-base
  row;
- exact prime-owner counts in both named fixtures;
- exact crossing-band endpoints and widths.

No finite test is imported into Lean or used as a uniformity premise.

## Exact remaining gap in this lane

The lane does not exclude an arbitrary internal prime-power owner for `p<=k`
when

```text
v_p(binomial(k-1,i-1)) > v_p(4),
```

nor a general lower term whose large-base prime-power cofactor exceeds the
current exact size threshold.  More broadly, Target 2 remains open for lower
blocks not covered by the displayed owner criteria.  No equivalent-strength
missing lemma is introduced.

## Verification record

```text
lake env lean ErdosProblems/Erdos686SmallPrimeBand.lean
  PASS; every printed theorem surface uses only
  [propext, Classical.choice, Quot.sound]

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_t2_small_prime_band
  12 passed in 0.11s

git diff --check -- ErdosProblems/Erdos686SmallPrimeBand.lean \
  compute/campaign686/agent_t2_small_prime_band \
  docs/plans/2026-07-12-erdos686-small-prime-crossing-band.md \
  docs/plans/2026-07-12-erdos686-any-position-prime-power.md
  PASS

forbidden-token scan for sorry, admit, and native_decide
  PASS
```

Frozen source hashes:

```text
4549ffbc667fa5a573c0b7d5d8301bf81199de369ec2880656690772d6ee985f  ErdosProblems/Erdos686SmallPrimeBand.lean
f8f54bfeaada39f4543e4ae39ca2c2334d8fc93a511f97b6105c41f1ee9fee82  compute/campaign686/agent_t2_small_prime_band/small_prime_band_verify.py
70ce496138709547bec96b4f4e9261dc6985a9252b3d30300ca61e54fba54a9e  compute/campaign686/agent_t2_small_prime_band/test_small_prime_band_verify.py
1fd21f17aa25c80524be7f663369f4c6bc367e8317e5583c6e568029420b2317  compute/campaign686/agent_t2_small_prime_band/findings.md
06d7b33485721559f48f4cfa1930ed99f0e3e746a1837ee4f3773d2392fd2a7d  docs/plans/2026-07-12-erdos686-small-prime-crossing-band.md
e2a3a50f3a356845751bfda68911ff7ce35a386ea2c17af3b02592e0f62a6caa  docs/plans/2026-07-12-erdos686-any-position-prime-power.md
```
