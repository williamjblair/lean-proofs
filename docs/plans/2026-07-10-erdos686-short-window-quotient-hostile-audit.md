# Erdős 686 Short-Window Quotient Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently audit the frozen ShortWindowQuotient package, including all 2,603 exact cases, its two-zero claims, and its precise partial-result scope.

**Architecture:** Treat both producer Lean files, including the existing `Audit.lean` importer, as frozen producer inputs.  Pin all six producer hashes, then implement a separately named verifier using independent formulas and a new Lean hostile module that reproves the public theorem boundary.  Record the duplicated findings line as non-semantic prose only and leave every frozen file unchanged.

**Tech Stack:** Lean 4/mathlib, exact Python integers and `Fraction`, pytest, SHA-256.

---

### Task 1: Freeze and enumerate the producer package

**Files:**
- Create: `compute/campaign686/short_window_quotient_hostile_verify.py`
- Create: `compute/campaign686/test_short_window_quotient_hostile_verify.py`

**Step 1:** Pin SHA-256 for producer Lean, producer-side `Audit.lean`, Python verifier, tests, findings, and plan.

**Step 2:** Enumerate every public producer theorem/lemma and every claim in the producer-side audit importer.

**Step 3:** Detect the duplicated findings section-8 line and classify it as prose-only without editing it.

### Task 2: Reconstruct the 2,603-case computation independently

**Files:**
- Modify only the two new hostile Python files.

**Step 1:** Reimplement the quotient/window arithmetic without importing `short_window_quotient_attack.py`.

**Step 2:** Reproduce the exact case count, row splits, extremal values, and every asserted implication.

**Step 3:** Reproduce both two-zero claims and add hostile mutations at each load-bearing hypothesis.

**Step 4:** Run the independent pytest file and require all checks to pass.

### Task 3: Build a genuinely independent Lean hostile audit

**Files:**
- Create: `ErdosProblems/Erdos686ShortWindowQuotientHostileAudit.lean`

**Step 1:** Import the producer module, not the producer-side audit as proof authority.

**Step 2:** Independently reprove every public theorem/lemma boundary used by the package.

**Step 3:** Kernel-check exact target constants and both two-zero conclusions.

**Step 4:** Print producer and hostile theorem axioms and require only `[propext, Classical.choice, Quot.sound]`.

### Task 4: Write the hostile report

**Files:**
- Create: `compute/campaign686/short_window_quotient_hostile_audit.md`

**Step 1:** Give frozen hashes, dependency tree, per-node verdicts, and all exact case totals.

**Step 2:** Distinguish theorem-proved claims from finite diagnostics and explicitly audit the two-zero statements.

**Step 3:** State the exact unresolved branch and whether the package is safe to integrate.

**Step 4:** Note the duplicated findings line as prose-only and preserve the frozen findings file.

### Task 5: Freeze the hostile audit

**Files:**
- Modify only the four new hostile artifacts and this plan.

**Step 1:** Run producer tests, hostile tests, producer Lean, producer-side importer, and independent hostile Lean.

**Step 2:** Run Python byte-compilation, forbidden-token, `native_decide`, `sorry`, custom-axiom, and whitespace gates.

**Step 3:** Recheck all six producer hashes and compute final hostile artifact hashes.

**Step 4:** Return PASS/FAIL, exact hashes, integration safety, and the exact remaining gap; do not edit or commit frozen files.
