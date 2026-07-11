# Erdős 686 Short-Window Lattice-Sign Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently audit the frozen ShortWindowLatticeSign package, its nine public Lean theorems, and every finite sign/sliver/boundary count.

**Architecture:** Pin all six producer inputs, treating the existing `Audit.lean` as a producer-side importer.  Reconstruct the 1,035 triple geometry and every sign-cell classification in a verifier that imports no producer Python.  Add a distinctly named Lean hostile module that independently reproves all public theorems, then document the exact surviving mixed, sliver, and zero-boundary scope.

**Tech Stack:** Lean 4/mathlib, exact Python integers and `Fraction`, pytest, SHA-256.

---

### Task 1: Freeze and enumerate the public surface

**Files:**
- Create: `compute/campaign686/short_window_lattice_sign_hostile_verify.py`
- Create: `compute/campaign686/test_short_window_lattice_sign_hostile_verify.py`

**Step 1:** Pin producer Lean, importer, Python, tests, findings, and plan hashes.

**Step 2:** Enumerate all nine public Lean theorems and verify that the producer importer contributes no independent theorem.

**Step 3:** Write failing hash and theorem-surface tests, then implement the immutable boundary checks.

### Task 2: Reconstruct every finite sign case

**Files:**
- Modify only the two new hostile Python files.

**Step 1:** Reimplement row coefficients, primitive lattice weights, Gamma, quotient bounds, and sign-cell inequalities without importing producer Python.

**Step 2:** Reproduce all 1,035 triples and the weight totals `1539+`, `1539-`, and `27` zero.

**Step 3:** Reproduce 2,381 mixed open cells, nine one-sided strict slivers, exclusion of all nine slivers, and the eighteen positive zero boundaries split into eight excluded and ten live.

**Step 4:** Add hostile mutations for strictness, zero weights, sign orientation, centers, and target-size inequalities.

### Task 3: Independently replay every Lean theorem

**Files:**
- Create: `ErdosProblems/Erdos686ShortWindowLatticeSignHostileAudit.lean`

**Step 1:** Import the producer module only.

**Step 2:** Independently reprove all nine public theorem statements under distinct names.

**Step 3:** Kernel-check exact count arithmetic and representative sliver/boundary constants.

**Step 4:** Print producer and hostile theorem axioms and require only `[propext, Classical.choice, Quot.sound]`.

### Task 4: Report exact remaining scope

**Files:**
- Create: `compute/campaign686/short_window_lattice_sign_hostile_audit.md`

**Step 1:** Record frozen hashes, dependency tree, theorem verdicts, and every exact finite count.

**Step 2:** Separate kernel-generic sign lemmas from finite Python row instantiation.

**Step 3:** State the 2,381 mixed cells, ten live positive zero boundaries, and all other still-open quotient branches explicitly.

**Step 4:** Give PASS/FAIL and integration safety without claiming three-owner or Erdős 686 closure.

### Task 5: Freeze the hostile package

**Files:**
- Modify only the four new hostile artifacts and this plan.

**Step 1:** Run eight producer tests and the independent hostile tests.

**Step 2:** Compile producer Lean, producer importer, and hostile Lean; run axiom, forbidden-token, Python byte-compilation, and whitespace gates.

**Step 3:** Recheck all six producer hashes and compute final hashes for all five hostile artifacts.

**Step 4:** Return exact PASS/FAIL and remaining scope; do not modify producer files, shared imports, manifests, docs, attestations, or git state.
