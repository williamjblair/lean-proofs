# Erdős 686 Two-Owner Aggregate Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently decide whether the frozen two-owner aggregate checkpoint proves exactly its advertised conditional closure without smuggling in the finite prime-factor grouping lemma.

**Architecture:** Freeze every producer artifact by SHA-256, rebuild and inspect all public Lean surfaces, and reconstruct the aggregate arithmetic independently. Exercise the generic and cubic degeneracies, owner grouping boundaries, and unit cleaned components, then issue a separate PASS/FAIL report with the exact remaining finite grouping obligation.

**Tech Stack:** Lean 4.29.1, mathlib, Lake, Python 3 exact integers, `pytest`, POSIX shell.

---

### Task 1: Freeze artifacts and reconstruct dependencies

**Files:**
- Read: `ErdosProblems/Erdos686TwoOwnerAggregate.lean`
- Read: `compute/campaign686/two_owner_aggregate_verify.py`
- Read: `compute/campaign686/test_two_owner_aggregate_verify.py`
- Read: `compute/campaign686/two_owner_aggregate_findings.md`
- Create: `compute/campaign686/two_owner_aggregate_hostile_audit.md`

**Steps:**
1. Record exact SHA-256 values and theorem declarations.
2. Map all hypotheses of the abstract, grouped, predicate, and final wrappers.
3. Identify precisely where finite prime-factor grouping remains assumed.

### Task 2: Run the independent kernel gate

**Files:**
- Create temporarily: `/tmp/Erdos686TwoOwnerAggregateAudit.lean`

**Steps:**
1. Compile the frozen source to fresh temporary object files and run the Lake target build.
2. `#check` and `#print axioms` all nine public theorems.
3. Require axioms to be a subset of `[propext, Classical.choice, Quot.sound]`.
4. Scan code, excluding comments and strings, for `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, and unproved private assumptions.

### Task 3: Reproduce arithmetic and branch coverage

**Files:**
- Create: `compute/campaign686/two_owner_aggregate_hostile_verify.py`
- Create: `compute/campaign686/test_two_owner_aggregate_hostile_verify.py`

**Steps:**
1. Recompute all six `G_k` values and the uniform `10^16` obstruction bound.
2. Enumerate all 610 ordered owner pairs and compare every coefficient/cutoff certificate.
3. Verify Pell gcd divisibilities, generic gcd cancellation, and the refined cubic divisor with signs, factors, and zero-delta boundaries.
4. Exercise same-owner and `P=1`/`Q=1` cases.
5. Verify the finite grouping predicate is a proper additional hypothesis and is not inferred from the equation wrapper.

### Task 4: Issue the hostile verdict

**Files:**
- Complete: `compute/campaign686/two_owner_aggregate_hostile_audit.md`

**Steps:**
1. Record hashes, theorem surfaces, axioms, exact counts, and cutoff values.
2. State PASS only for the exact conditional theorem proved.
3. State the remaining finite grouping lemma in one quantified form and reject any target-equivalent or silent assumption.
4. Do not alter producer files and do not commit.
