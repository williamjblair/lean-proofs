# Erdős 686 Two-Owner Grouping Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Convert finite per-prime cleaned-owner witnesses into `HasAtMostTwoGlobalResidualOwners`, and supply those witnesses from the global concentration theorem for exact target-row equations.

**Architecture:** Define an explicit owner-assignment predicate over `d.primeFactors`, then form `P` and `Q` as products of retained prime powers assigned to the two owners and `g` as the product of complementary loss powers. Prove factorization, coprimality, grouped divisibility, and the six exact `G_k` bounds using finite-product lemmas; finally use classical finite choice to select one concentration owner per prime factor.

**Tech Stack:** Lean 4.29.1, mathlib, Lake, Python 3 exact integers, pytest.

**Status:** Complete.  All five tasks were implemented and passed the focused
arithmetic, fresh compilation, Lake build, forbidden-token, and kernel axiom
gates.  The final theorem also records the no-two-cover consequence for a
target-size exact solution.

---

### Task 1: Freeze interfaces and write arithmetic tests

**Files:**
- Read: `ErdosProblems/Erdos686GlobalResidualConcentration.lean`
- Read: `ErdosProblems/Erdos686TwoOwnerAggregate.lean`
- Create: `compute/campaign686/two_owner_grouping_verify.py`
- Create: `compute/campaign686/test_two_owner_grouping_verify.py`

**Steps:**
1. Recompute retained and loss factors for every prime factor of exhaustive small `d` values.
2. Enumerate both owner assignments and verify `d=g*P*Q`, `Coprime P Q`, and `g<=G_k` for all six rows.
3. Cover empty/unit cleaned buckets and primes at least `k`.
4. Run the focused tests and record exact counts.

### Task 2: Define the owner-assignment interface

**Files:**
- Create: `ErdosProblems/Erdos686TwoOwnerGrouping.lean`

**Steps:**
1. Import only `Erdos686TwoOwnerAggregate`.
2. Define a per-prime owner witness over `d.primeFactors` using `globalResidualCleanExponent`.
3. Define the at-most-two-range condition with explicit owner indices `i,j`.
4. Define the retained products `P,Q` and complementary product `g`.

### Task 3: Prove finite product assembly

**Files:**
- Modify: `ErdosProblems/Erdos686TwoOwnerGrouping.lean`

**Steps:**
1. Prove every prime factor decomposes into complementary and retained powers.
2. Prove `d` equals the product over its prime-factor powers and derive `d=g*P*Q`.
3. Prove `P.Coprime Q` from disjoint owner predicates.
4. Multiply per-prime factor and square divisibilities at each owner.
5. Prove `g<=targetAggregateLoss k` by six target-row cases and exact small-prime loss bounds.

### Task 4: Prove grouping and chooser theorems

**Files:**
- Modify: `ErdosProblems/Erdos686TwoOwnerGrouping.lean`

**Steps:**
1. Prove the pure grouping theorem from an explicit assignment whose nontrivial range is contained in `{i,j}`.
2. Use `Classical.choose` over `d.primeFactors` and `primePower_component_exists_globalResidual_clean` to build an assignment for exact equations with `k<=d`.
3. State a chooser theorem returning the assignment and witnesses without assuming two owners.
4. State the final conditional theorem: if the chosen assignment has at most two nontrivial owners, derive `HasAtMostTwoGlobalResidualOwners` and hence `d<10^120` through the audited aggregate theorem.

### Task 5: Verify and document exact scope

**Files:**
- Create: `compute/campaign686/two_owner_grouping_findings.md`

**Steps:**
1. Compile the source to fresh temporary objects and run the Lake target build.
2. Print axioms for every public theorem and enforce `[propext, Classical.choice, Quot.sound]`.
3. Run forbidden-token and focused Python tests.
4. Document any remaining interface gap exactly; do not claim the chooser has at most two owners unless separately assumed.
5. Freeze all new artifact SHA-256 values without committing.
