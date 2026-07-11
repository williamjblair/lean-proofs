# Erdős 686 finite two-owner grouping checkpoint

Status: **proved and kernel-checked for the exact grouping interface.**  The
module converts a certified per-prime owner assignment whose nonzero cleaned
components use at most two owner values into
`HasAtMostTwoGlobalResidualOwners`.  Global concentration constructs a
certified assignment for every exact target-row solution with `k ≤ d`.

The strengthened equation-level corollary says that if additionally
`10^120 ≤ d`, the constructed assignment has no two-index cover of its
nonzero cleaned owner range.  This is the precise sense in which a target-size
solution has at least three nontrivial cleaned owners.  The theorem does not
identify those owners, and this checkpoint does not claim the full Erdős 686
target is solved.

## Frozen artifacts

```text
ErdosProblems/Erdos686TwoOwnerGrouping.lean
  63799ee4a2cc6fc0632776c231ac0961ddc038d60348c1b2fc43def3803797ef
compute/campaign686/two_owner_grouping_verify.py
  66b0d3e0398447dc7cb23cd0069afc13b4a0bfeddc1b371c163eb386ad3b895a
compute/campaign686/test_two_owner_grouping_verify.py
  615d904f2c7b585993d30f7c3354759e09ac9f7e2c67fbcc9dd2f4598eec1254
docs/plans/2026-07-10-erdos686-two-owner-grouping.md
  e1117b800f1ca0a977d42710040ffc5a62e6468b2a068a299fee5ea54f3b0fa6
```

The module has one direct import, whose already audited hash is unchanged:

```text
ErdosProblems/Erdos686TwoOwnerAggregate.lean
  35959fee7b3080b2d0a91885a7a465455fcbed4ead9ecc1d652024ec7eabe009
```

The concentration theorem used by the chooser remains:

```text
ErdosProblems/Erdos686GlobalResidualConcentration.lean
  495981605282c4a1963f95bdce0788b4baba6cfa05c8be00b8c57154f49f9e24
```

No shared import registry, root audit file, manifest, or campaign registry was
changed by this checkpoint.

## Exact definitions

For every `p ∈ d.primeFactors`, `GlobalResidualOwnerAssignment k n d owner`
records:

```text
owner p ∈ [1,k]
p^t | n + owner p
(p^t)^2 | localResidual n d (owner p)

t = globalResidualCleanExponent p (d.factorization p) k.
```

`GlobalResidualOwnerRangeAtMostTwo k d owner i j` requires `i,j ∈ [1,k]`
and, for every prime factor, either `t=0`, `owner p=i`, or `owner p=j`.  The
`t=0` exception is intentional: its cleaned power is one and contributes no
mass to either bucket.

The grouped factors are

```text
g_p = p^(v_p(d)-t)
P_p = p^t if owner p=i, else 1
Q_p = p^t if owner p≠i and owner p=j, else 1.
```

The `owner p≠i` condition gives the first owner precedence.  Consequently,
when `i=j`, every retained power goes to `P` and `Q=1`; no prime power is
duplicated.

## Dependency tree and per-node verdict

```text
exists_globalResidualOwnerAssignment_not_two_cover
|- primePower_component_exists_globalResidual_clean
|  `- one certified owner for each p in d.primeFactors
|- assume a two-index cover i,j
|- hasAtMostTwoGlobalResidualOwners_of_assignment
|  |- globalResidualGrouped_decomposition
|  |  |- p^v = p^(v-t) * p^t for every prime factor
|  |  `- Nat.prod_factorization_pow_eq_self
|  |- globalResidualGroupedLeft_coprime_right
|  |  `- distinct prime powers are pairwise coprime; left precedence if i=j
|  |- grouped factor divisibilities
|  |  `- pairwise-coprime finite products of divisors divide the target
|  |- grouped square divisibilities
|  |  `- the same product argument applied to squared factors
|  `- globalResidualGroupedLoss_le_targetAggregateLoss
|     |- each g_p divides G_k
|     |- distinct g_p are pairwise coprime
|     `- therefore product g divides G_k and g≤G_k
|- atMostTwoGlobalResidualOwners_below_cutoff
|  `- d < 10^120
`- contradiction with 10^120 ≤ d
```

Verdicts:

- Per-prime factorization: **PASS.**  The proof uses exact natural
  subtraction with `t≤v_p(d)` and reconstructs `d` from its complete finite
  factorization.
- Coprimality: **PASS.**  `P` and `Q` contain disjoint powers of distinct
  primes.  The coincident-owner case is handled by definition, not excluded.
- Factor and square products: **PASS.**  The helper theorem performs induction
  with `Nat.Coprime.mul_dvd_of_dvd_of_dvd`; it does not misuse semiring
  `IsCoprime`, which would be too strong over naturals.
- Aggregate loss: **PASS.**  For primes below `k`, exact factorial valuations
  are evaluated with `Nat.factorization_factorial`; for primes at least `k`,
  the loss exponent is proved zero.  Pairwise coprimality turns the individual
  divisibilities into `g | G_k`.
- Chooser: **PASS.**  For each prime factor, the full factorization power
  divides `d`; `primePower_component_exists_globalResidual_clean` supplies its
  owner and both local divisibilities.  Finite choice is represented as a
  total function whose values away from `d.primeFactors` are irrelevant.
- Large-gap conclusion: **PASS for the stated no-two-cover result.**  It is a
  contradiction wrapper around the already audited conditional aggregate
  theorem, not a new unconditional resolution of the equation.

There is no phrase of the form "essentially at most two" in the theorem
surface: the exact quantified remaining condition is

```text
∃ owner, GlobalResidualOwnerAssignment k n d owner ∧
  ∀ i j, ¬ GlobalResidualOwnerRangeAtMostTwo k d owner i j
```

for target-size solutions, and `GlobalResidualOwnerRangeAtMostTwo` itself is
fully quantified over `d.primeFactors`.

## Exact arithmetic reproduction

The standalone verifier independently recomputes Legendre valuations and the
six aggregate losses:

| `k` | `G_k` |
|---:|---:|
| 5 | 108 |
| 7 | 1,620 |
| 9 | 136,080 |
| 11 | 1,224,720 |
| 13 | 242,494,560 |
| 15 | 18,914,575,680 |

For every `1 ≤ d ≤ 2000` in all six rows, it exhausts every binary
assignment of the distinct prime factors to two owners.  The exact totals are:

```text
64,866 binary owner assignments
12,000 coincident-owner fixtures
91,006 zero-clean component occurrences
12,344 fixtures moving a zero-clean component to an outside owner
73,068 prime-at-least-k component occurrences
3,936 assignments with both retained buckets equal to one
29,671 assignments with the left bucket equal to one
29,671 assignments with the right bucket equal to one
35,195 assignments with a nontrivial left bucket
35,195 assignments with a nontrivial right bucket.
```

Every fixture satisfies `d=g*P*Q`, `gcd(P,Q)=1`, `g≤G_k`, every individual
loss factor divides `G_k`, and all constructed component and aggregate factor
and square divisibilities.  Six explicit nonzero-clean outside-owner cases are
rejected, while six zero-clean outside-owner cases are accepted.  The
coincident-owner check confirms first-owner precedence and `Q=1`.

## Kernel and test gates

- A fresh direct compilation emitted a 1.4 MiB `.olean` and a 60 KiB `.ilean`
  under `/tmp`.
- `lake build ErdosProblems.Erdos686TwoOwnerGrouping` completed all 8,258 jobs.
- `#print axioms` for all 13 public theorems reports exactly the allowed subset
  `[propext, Classical.choice, Quot.sound]`.
- A nested-comment-aware scan finds no executable `sorry`, `admit`,
  `native_decide`, `axiom`, or `unsafe` declaration.
- The focused verifier has 7 passing tests.
- The combined grouping, aggregate-producer, and aggregate-hostile suite has
  26 passing tests.

## Exact remaining interface

The finite grouping gap is closed.  What remains for this branch of the
campaign is no longer product bookkeeping: a target-size solution's certified
assignment must use a nonzero cleaned owner range that cannot be covered by
two indices.  Any subsequent closure must exploit the resulting genuinely
multi-owner structure.  Reducing it back to an unproved assertion that those
owners somehow coalesce would be equivalent to contradicting the theorem
proved here and is not progress.
