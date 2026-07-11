# Erdős 686 Three-Owner Extraction Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently verify that the frozen ThreeOwnerExtraction package converts the negation of every two-index cover into exactly three live prime-power witnesses at pairwise-distinct certified owners, without strengthening its equation-level conclusion.

**Architecture:** Freeze every producer hash before inspection, reconstruct the finite cover equivalence independently in Python, and restate the exact logical bridge in an audit-only Lean module without modifying the producer.  Audit every public declaration, theorem quantifier, boundary case, dependency, forbidden token, and axiom surface; then rerun hashes to prove the producer remained unchanged.

**Tech Stack:** Lean 4.29.1 with mathlib, Python 3 exact finite enumeration, pytest, SHA-256, repository build scripts.

---

### Task 1: Freeze and inventory the producer

**Files:**
- Read only: `ErdosProblems/Erdos686ThreeOwnerExtraction.lean`
- Read only: `compute/campaign686/three_owner_extraction_verify.py`
- Read only: `compute/campaign686/test_three_owner_extraction_verify.py`
- Read only: `compute/campaign686/three_owner_extraction_findings.md`
- Read only: `docs/plans/2026-07-10-erdos686-three-owner-extraction.md`

**Step 1: Record SHA-256 hashes and line counts**

Run `shasum -a 256` over all five files and retain the exact output in the audit report.

**Step 2: Read every producer artifact completely**

Inventory definitions, structures, public theorems, imports, `#print axioms` commands, claimed fixture counts, and the exact equation-level quantifiers.

**Step 3: Build a dependency tree**

Trace both public theorems through `GlobalResidualOwnerAssignment`, `GlobalResidualOwnerRangeAtMostTwo`, and `exists_globalResidualOwnerAssignment_not_two_cover`.

### Task 2: Independent finite equivalence verifier

**Files:**
- Create: `compute/campaign686/three_owner_extraction_hostile_verify.py`
- Test: `compute/campaign686/test_three_owner_extraction_hostile_verify.py`

**Step 1: Write failing tests**

Test the exact equivalence for every live-value assignment over owner universes of sizes `1..6`:

```text
not(exists i,j covering every live value) iff
exists three live entries with pairwise-distinct values.
```

Include empty live support, one value, two values, three values, repeated primes at one owner, zero-clean entries outside the cover, coincident `i=j`, and arbitrary total-function values off the prime-factor support.

**Step 2: Run the test and observe the missing-module failure**

Run: `python3 -m pytest compute/campaign686/test_three_owner_extraction_hostile_verify.py -q`

Expected: import failure before the verifier exists.

**Step 3: Implement independent exhaustive enumeration**

Use only tuples, sets, and exact Boolean predicates.  Do not import the producer verifier.  Report exact assignment and boundary-fixture counts.

**Step 4: Verify the producer fixture claims independently**

Run both producer and hostile tests and compare their claimed logical surface, not their internal implementation.

### Task 3: Audit-only Lean reconstruction

**Files:**
- Create: `ErdosProblems/Erdos686ThreeOwnerExtractionHostileAudit.lean`

**Step 1: Import only the frozen producer**

Use `import ErdosProblems.Erdos686ThreeOwnerExtraction` and add `#check`, `#print`, and `#print axioms` for every public producer declaration.

**Step 2: Restate the cover-to-three-value implication abstractly**

Prove an audit theorem over a finite support and a live predicate.  Its conclusion must expose three support elements, liveness, and pairwise-distinct values; it must not assume cardinality three or that no fourth value exists.

**Step 3: Reconstruct the structure projection audit**

Prove that `ThreeGlobalResidualOwnerWitness` projects exactly three prime-factor memberships, three nonzero clean exponents, three in-range owners, pairwise owner inequality, factor/square divisibilities, and pairwise coprimality.

**Step 4: Audit equation-level quantifiers**

Restate that the target-size wrapper concludes `exists owner, assignment and witness`; confirm it does not conclude the assignment has exactly three owners, does not group the entire gap into three factors, and does not prove Target 1.

### Task 4: Hostile source and kernel gates

**Files:**
- Create: `compute/campaign686/three_owner_extraction_hostile_audit.md`

**Step 1: Scan forbidden declarations and tactics**

Run a comment-aware check for executable `sorry`, `admit`, `native_decide`, `axiom`, and `unsafe` declarations in the producer and audit Lean files.

**Step 2: Compile and build**

Run:

```bash
lake env lean ErdosProblems/Erdos686ThreeOwnerExtraction.lean
lake env lean ErdosProblems/Erdos686ThreeOwnerExtractionHostileAudit.lean
lake build ErdosProblems.Erdos686ThreeOwnerExtraction
lake build ErdosProblems.Erdos686ThreeOwnerExtractionHostileAudit
```

Expected: success with only `[propext, Classical.choice, Quot.sound]` on public theorem surfaces.

**Step 3: Run exact tests**

Run producer and hostile pytest modules together; expected all pass.

**Step 4: Recheck frozen hashes**

The five producer hashes must match Task 1 exactly.

### Task 5: Final adversarial report

**Files:**
- Create: `compute/campaign686/three_owner_extraction_hostile_audit.md`

**Step 1: Give per-node verdicts**

Explicitly grade the no-two-cover equivalence, witness extraction, prime distinctness, owner distinctness, factor/square projections, coprimality, equation-level wrapper, and theorem-strength claims.

**Step 2: State every boundary result**

Record empty/one/two live values, exactly three, four-or-more, coincident covers, zero-clean entries, off-support owner values, endpoints, bases 2 and 3, and the `d=1` telescope scope.

**Step 3: Return PASS or FAIL**

PASS requires unchanged hashes, independent equivalence reproduction, clean Lean compilation/build, allowed axioms only, no forbidden executable tokens, and no theorem-strength overclaim.

**Step 4: Check audit-only diffs**

Run `git diff --check` over the five uniquely named audit artifacts and verify no shared file was modified.
