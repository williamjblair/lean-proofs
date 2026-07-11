# Erdős 686 Two-Owner Aggregate Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove that every target-row Erdős 686 solution admitting a globally cleaned decomposition with at most two residual-owner buckets has `d < 10^120` under the exact row loss budget `G_k`.

**Architecture:** Add one standalone Lean module importing the frozen global-residual two-prime composition module.  The new module will expose the exact `G_k` table, a `10^16` second-obstruction bound, Pell-gcd cancellation lemmas, a strengthened abstract two-bucket closure, and an equation-level grouped-decomposition wrapper.  A standalone exact Python verifier and tests will reproduce all six numeric rows and boundary cases; the audited dependency modules remain byte-for-byte unchanged.

**Tech Stack:** Lean 4.29.1, mathlib, Python 3 exact integers, pytest.

---

### Task 1: Freeze dependencies and write the exact arithmetic tests

**Files:**
- Create: `compute/campaign686/test_two_owner_aggregate_verify.py`
- Create: `compute/campaign686/two_owner_aggregate_verify.py`
- Preserve: `ErdosProblems/Erdos686GlobalResidualConcentration.lean`
- Preserve: `ErdosProblems/Erdos686GlobalResidualTwoPrime.lean`

**Step 1: Write failing tests**

Cover the six exact budgets
`108, 1620, 136080, 1224720, 242494560, 18914575680`, the exact `10^16`
second-obstruction majorant, all generic cutoffs, the gcd-refined cubic cutoffs,
and `d = 1`/named deep non-equation fixtures.

**Step 2: Run the test to verify it fails**

Run: `python3 -m pytest compute/campaign686/test_two_owner_aggregate_verify.py -q`

Expected: FAIL because the verifier module does not yet exist.

**Step 3: Implement the exact verifier**

Use Python integer arithmetic only.  Compute
`35 * (10^16)^2 * G_k^6` and
`3600 * 15^2 * (10^12)^2 * G_k^7` for each target row and require every
value to be strictly below `10^120`.

**Step 4: Run the tests**

Run: `python3 -m pytest compute/campaign686/test_two_owner_aggregate_verify.py -q`

Expected: PASS.

### Task 2: Formalize the exact row budget and obstruction bounds

**Files:**
- Create: `ErdosProblems/Erdos686TwoOwnerAggregate.lean`

**Step 1: Define the row budget**

Add `targetAggregateLoss : ℕ → ℕ` with the exact six `G_k` values and a
kernel-checked table theorem.

**Step 2: Prove the sharpened second-obstruction estimate**

Define `aggregateSecondObstructionBound := 10^16` and prove

```lean
Int.natAbs (3 * (C * (t : ℤ) + 4 * D * (g : ℤ)^2 * delta))
  < aggregateSecondObstructionBound * g^2
```

from `A ≤ 35`, `t < A^2*g^2`, coefficient bounds `<10^12`, and
`|delta| < 15`.

**Step 3: Prove row-exact numeric cutoffs**

Case-split the six target rows so the kernel checks the actual `G_k` value in
both the generic `g^6` and refined cubic `g^7` bounds.

**Step 4: Source-check the module**

Run: `lake env lean ErdosProblems/Erdos686TwoOwnerAggregate.lean`

Expected: exit 0.

### Task 3: Formalize Pell gcd cancellation

**Files:**
- Modify: `ErdosProblems/Erdos686TwoOwnerAggregate.lean`

**Step 1: Prove both gcd consequences**

From `a*P^2-b*Q^2=3*delta`, prove

```lean
Nat.gcd P b ∣ 3 * Int.natAbs delta
Nat.gcd Q a ∣ 3 * Int.natAbs delta
```

using integer divisibility and `Int.natAbs_dvd_natAbs`.

**Step 2: Prove the generic cancellation lemma**

Use `dvd_gcd_mul_of_dvd_mul` to prove that `P ∣ K*b` and
`gcd P b ∣ D` imply `P ∣ K*D`.

**Step 3: Expose the refined cubic divisibility**

Combine the frozen `clean_third_zero_component_dvd` theorem with the two gcd
lemmas to obtain the exact factors
`P ∣ 60*|delta|*|E_i|*g^3` and its symmetric `Q` statement.

**Step 4: Source-check again**

Run: `lake env lean ErdosProblems/Erdos686TwoOwnerAggregate.lean`

Expected: exit 0.

### Task 4: Prove the abstract and grouped equation closures

**Files:**
- Modify: `ErdosProblems/Erdos686TwoOwnerAggregate.lean`

**Step 1: Prove the abstract two-bucket theorem**

Mirror the frozen second/third split, replacing the loose constants by
`10^16`, taking `g ≤ targetAggregateLoss k`, and using the refined gcd
cancellation in the simultaneous-zero branch.

**Step 2: Prove the grouped equation wrapper**

Take an exact equation, `d = g*P*Q`, coprimality, owner indices, divisibility
of `P,Q` into the owner factors, square divisibility into owner residuals, and
the row-specific `g` bound.  Handle coincident owners directly and derive the
Pell identity plus local second/third lifts for distinct owners.

**Step 3: State the exact remaining composition gap**

Document that the only absent equation-level step is a finite prime-factor
grouping theorem producing the grouped witnesses and `g ≤ G_k` from the
per-prime global concentration theorem under the at-most-two-owner premise.

**Step 4: Source-check**

Run: `lake env lean ErdosProblems/Erdos686TwoOwnerAggregate.lean`

Expected: exit 0.

### Task 5: Build, audit gates, and dependency report

**Files:**
- Create: `compute/campaign686/two_owner_aggregate_findings.md`

**Step 1: Build the standalone module**

Run: `lake build ErdosProblems.Erdos686TwoOwnerAggregate`

Expected: `.olean` and `.ilean` emitted, exit 0.

**Step 2: Run kernel and token gates**

Print axioms for every public theorem and require the subset
`[propext, Classical.choice, Quot.sound]`.  Scan the new Lean module for
`sorry`, `admit`, `axiom`, and `native_decide`.

**Step 3: Run exact tests**

Run: `python3 -m pytest compute/campaign686/test_two_owner_aggregate_verify.py -q`

Expected: all tests pass.

**Step 4: Write the dependency tree and freeze hashes**

Distinguish the completed abstract closure, completed grouped equation
wrapper, and the remaining finite prime-owner grouping lemma.  Record SHA-256
hashes and leave every file uncommitted as required.
