# Erdős 686 two-owner grouping hostile audit

Verdict: **PASS.**  The frozen candidate closes the finite grouping gap left
by `Erdos686TwoOwnerAggregate`: a certified per-prime assignment whose
nonzero cleaned components are covered by two owner indices is converted into
the exact `HasAtMostTwoGlobalResidualOwners` interface.  The candidate also
constructs one certified assignment from global residual concentration.

This does **not** close Erdős 686.  At target size, the final theorem proves
that the particular certified assignment it constructs is not coverable by
any two owner indices.  The surviving branch is therefore the genuinely
multi-owner branch.

## Frozen scope

The candidate and its two mathematical dependencies were unchanged throughout
the audit:

```text
ErdosProblems/Erdos686TwoOwnerGrouping.lean
  63799ee4a2cc6fc0632776c231ac0961ddc038d60348c1b2fc43def3803797ef
ErdosProblems/Erdos686TwoOwnerAggregate.lean
  35959fee7b3080b2d0a91885a7a465455fcbed4ead9ecc1d652024ec7eabe009
ErdosProblems/Erdos686GlobalResidualConcentration.lean
  495981605282c4a1963f95bdce0788b4baba6cfa05c8be00b8c57154f49f9e24
```

Independent audit artifacts:

```text
ErdosProblems/Erdos686TwoOwnerGroupingAudit.lean
  754181e1c20f7e7390d83b064d4f2eafdae91bb46615f9f21beda98c924fae72
compute/campaign686/two_owner_grouping_hostile_verify.py
  a495b254f8681ee7c84784841fc7a65c7b6076dbe5efe8f34b774b42abbc37f5
compute/campaign686/test_two_owner_grouping_hostile_verify.py
  14ff2d4a66f53dce995cc4b481e3e39348ffa27c59d97a3eb7d058cedee3b4f2
docs/plans/2026-07-10-erdos686-two-owner-grouping-hostile-audit.md
  720cee4d84064565232a957e507b1746dd424bb1737e2fb5d2b44b0f426c5e83
```

The hostile Python verifier does not import the producer verifier.  No
producer file, shared import, manifest, registry, or campaign document was
modified by this audit.

## Exact quantified interfaces

For each `p ∈ d.primeFactors`, a `GlobalResidualOwnerAssignment` contains the
three exact facts

```text
owner p ∈ Finset.Icc 1 k
p^t_p ∣ n + owner p
(p^t_p)^2 ∣ localResidual n d (owner p)

t_p = globalResidualCleanExponent p (d.factorization p) k.
```

The two-cover predicate is

```text
i ∈ Finset.Icc 1 k ∧ j ∈ Finset.Icc 1 k ∧
∀ p ∈ d.primeFactors, t_p = 0 ∨ owner p = i ∨ owner p = j.
```

The zero-exponent alternative is exact and necessary: `p^t_p=1` contributes
no retained mass.  It does not permit a nonzero cleaned component to escape
the cover.

The final theorem has the quantifier order

```text
∃ owner,
  GlobalResidualOwnerAssignment k n d owner ∧
  ∀ i j, ¬ GlobalResidualOwnerRangeAtMostTwo k d owner i j.
```

The `∀ i j` refers to the same existentially selected `owner`.  There is no
outer `∀ owner`; the theorem does not state that every possible choice of
concentration witnesses is non-coverable.  The audit module kernel-checks a
fully expanded version of this statement.  Pairs outside `Finset.Icc 1 k`
fail the cover predicate at its first two conjuncts, so the universal is
effectively over all valid owner-index pairs.

## Dependency tree and per-node verdict

```text
exists_globalResidualOwnerAssignment_not_two_cover
|- target-row and large-gap arithmetic gives 5 <= k <= d
|- exists_globalResidualOwnerAssignment
|  |- for each p in d.primeFactors, p is prime and v_p(d) > 0
|  |- p^(v_p(d)) divides d
|  |- primePower_component_exists_globalResidual_clean
|  |  |- p = 2 follows the non-three concentration route
|  |  |- p = 3 follows the exact common-factor route
|  |  `- all other primes use the same unified theorem
|  `- classical choice forms one total owner function; off-support values are irrelevant
|- assume a two-index cover of that assignment
|- hasAtMostTwoGlobalResidualOwners_of_assignment
|  |- per-prime exponent split
|  |  `- e = min(e,L_p) + max(e-L_p,0)
|  |- complete factorization reconstruction
|  |  `- d = product over all p in d.primeFactors
|  |- first-owner precedence
|  |  `- if i=j, all retained mass enters P and Q=1
|  |- P and Q are coprime
|  |- component divisibilities multiply within each bucket
|  |- component square divisibilities multiply within each bucket
|  `- grouped loss g divides G_k and hence g <= G_k
|- atMostTwoGlobalResidualOwners_below_cutoff
|  `- d < 10^120
`- contradiction with 10^120 <= d
```

Per-node verdicts:

- **Per-prime exponent split: PASS.**  Natural subtraction gives retained
  exponent `max(e-L_p,0)` and complementary exponent `min(e,L_p)`, including
  `e≤L_p` and `L_p=0`.
- **Full factorization reconstruction: PASS.**  The theorem requires `0<d`;
  the cutoff wrapper derives this from its base inequality.  Empty support is
  separately checked at `d=1` and yields `g=P=Q=1`.
- **Aggregate loss: PASS.**  For all six rows the independently recomputed
  losses are exactly `108`, `1620`, `136080`, `1224720`, `242494560`, and
  `18914575680`.  Fixtures attaining `g=G_k` were checked in every row.
  Every prime `p≥k`, including the boundary `p=k` when prime, has zero loss.
- **Coprimality and precedence: PASS.**  Distinct prime powers are disjoint
  across buckets.  When `i=j`, the right definition tests the left owner first,
  so no component is duplicated and `Q=1`.
- **Product divisibilities: PASS.**  Within one bucket the factors are powers
  of distinct primes.  Their lcm equals their product, both for the factors and
  their squares, so the pairwise-coprime finite-product lemma has exactly the
  required hypotheses.
- **Zero-clean components: PASS.**  Such components go wholly into `g`; an
  arbitrary valid owner outside `{i,j}` changes neither retained bucket.
  Nonzero cleaned components outside `{i,j}` are rejected.
- **`p=2`: PASS.**  The general non-three concentration branch supplies the
  owner, factor divisibility, and square residual divisibility.  Exhaustive,
  random, row-maximum, and kernel examples all include this boundary.
- **`p=3`: PASS.**  The special loss exponent is reproduced directly from
  `floor((k+v_3((k-1)!))/2)` and checked in every row.  No non-three lemma is
  applied to three.
- **Empty and one-prime support: PASS.**  Choice is vacuous off support, and
  unit products behave correctly.  The exhaustive sweep includes 6 empty and
  1,602 one-prime row/gap fixtures.
- **Chooser composition: PASS.**  The local theorem is invoked only after
  deriving primality, positive factorization exponent, and the full
  prime-power divisibility into `d`.  Classical choice selects one witness per
  prime; the total function's values away from `d.primeFactors` never enter a
  theorem hypothesis.
- **Final quantifiers: PASS.**  The existential assignment and the inner
  universal no-cover statement are scoped correctly.  A direct finite model
  checked 6,144 assignments and confirmed that no valid two-index cover is
  equivalent to having more than two distinct owner values among nonzero
  cleaned components.

The 14 `private` declarations in the candidate are proved helper lemmas in the
same kernel-checked module.  No private identifier occurs in any public
theorem type, and no executable `sorry`, `admit`, `native_decide`, `axiom`,
`unsafe`, or `opaque` declaration occurs in the candidate or audit module.

## Independent exact arithmetic

The hostile sweep covered:

```text
9,000 row/gap pairs, all 1 <= d <= 1500 in six rows
141,216 owner maps into three valid owner values
89,310 accepted two-owner maps
51,906 correctly rejected nonzero-clean outside-owner maps
47,130 coincident-owner maps
22,262 accepted coincident-owner maps
24,868 correctly rejected coincident-owner maps
157,104 zero-clean component occurrences
52,368 zero-clean outside-cover occurrences
63,551 p=2 component occurrences
49,253 p=3 component occurrences
86,720 prime-at-least-k component occurrences
5,000 seeded large exact fixtures, up to 454 decimal digits
455 large coincident-owner fixtures.
```

Every accepted fixture satisfies

```text
d = g * P * Q
gcd(P,Q) = 1
g ∣ G_k and g <= G_k
each component loss factor divides G_k
each same-owner factor product divides its synthetic common target
each same-owner squared product divides its synthetic common square target.
```

The six exact row-maximum fixtures have `g=G_k` and `P=Q=1`.  Six additional
prime-at-least-`k` fixtures have `g=1`, confirming the zero-loss branch.

## Kernel and test gates

- Fresh direct compilation produced temporary `.olean` and `.ilean` files.
- `#check` and full `#print` succeeded for all 13 public candidate theorems.
- `#print axioms` reports exactly
  `[propext, Classical.choice, Quot.sound]` for each of the 13 theorems.
- `lake build ErdosProblems.Erdos686TwoOwnerGrouping
  ErdosProblems.Erdos686TwoOwnerGroupingAudit` completed **8,259 jobs**.
- The combined hostile and producer suites completed **15/15 tests**.
- The frozen candidate SHA-256 remained unchanged after all gates.

## Exact remaining Erdős 686 gap

The finite grouping/bookkeeping gap is closed.  The next branch is not to
reprove that products can be grouped.  It is to eliminate the multi-owner
configuration forced by the final theorem.

An exact quantified form of that surviving obligation is:

```text
For k in {5,7,9,11,13,15}, whenever
  blockProduct k (n+d) = 4 * blockProduct k n,
  n+1 < C*d,
  A = 3*C+2,
  A <= 35,
  10^120 <= d,
and owner is a GlobalResidualOwnerAssignment k n d owner,
derive a contradiction from
  forall i j, not (GlobalResidualOwnerRangeAtMostTwo k d owner i j).
```

Equivalently, subsequent work must rule out a certified assignment with at
least three distinct owner values among its nonzero cleaned prime-power
components, using additional relations from the exact block equation.  The
candidate proves neither that exclusion nor the full Erdős 686 target.
