# Erdos686 Two-Prime Gap Restriction Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Derive and audit the strongest unconditional exact restriction supplied by the p-adic local lifts when the gap has exactly two coprime prime-power components.

**Architecture:** First eliminate the shared lower-block variable from the two local residual congruences and record the resulting bounded-coefficient Pell-type identity. Then split by localization indices and center/non-center cases, using exact arithmetic to identify genuinely elementary closures. Only a nontrivial unconditional theorem will be promoted to a standalone Lean module; target-equivalent Diophantine residuals will remain explicitly labeled gaps.

**Tech Stack:** Lean 4/mathlib, Python 3 exact integer arithmetic, Markdown dependency-tree audit.

---

### Task 1: Extract the exact local hypotheses

**Files:**
- Read: `ErdosProblems/Erdos686PadicLift.lean`
- Read: `codex/prompt_686_full_solve.md`

**Step 1:** Record the unique localization theorem and the square/cubic residual divisibilities.

**Step 2:** Record the exact archimedean constants for `k = 5,7,9,11,13,15`.

**Step 3:** Check every use of `p >= k`, `q >= k`, positivity of exponents, and `d >= k`.

### Task 2: Derive the two-prime coefficient identity

**Files:**
- Create only if the result is substantive: `compute/campaign686/two_prime_gap_findings.md`
- Create only if exact enumeration is useful: `compute/campaign686/two_prime_gap_verify.py`

**Step 1:** Write `u = p^e`, `v = q^f`, `d = uv`, and local indices `i,j`.

**Step 2:** From `u^2 | 3(n+i)-d` and `v^2 | 3(n+j)-d`, introduce positive coefficients `a,b` and prove
`a*u^2 - b*v^2 = 3*(i-j)`.

**Step 3:** Derive exact strict bounds on `a` and `b`, including center cubic refinements.

**Step 4:** Reproduce all finite coefficient claims with integer arithmetic tests.

### Task 3: Hostile-audit elementary closure subcases

**Files:**
- Modify only if created: `compute/campaign686/two_prime_gap_findings.md`
- Modify only if created: `compute/campaign686/two_prime_gap_verify.py`

**Step 1:** Analyze equal localization index `i = j` using coprimality and square classes.

**Step 2:** Analyze one or both components at the center using cubic divisibility and size bounds.

**Step 3:** Analyze coefficient-square and dominant-component cases without importing an unproved Pell or prime-power assertion.

**Step 4:** Test the formulas against the `d = 1` telescope caveat and make clear why that caveat lies outside the prime-power hypotheses.

### Task 4: Bank a theorem only if it is genuinely new

**Files:**
- Create only on success: `ErdosProblems/Erdos686TwoPrimeGap.lean`
- Test: the new Lean module with `lake env lean`

**Step 1:** State the exact unconditional subcase theorem, with every arithmetic hypothesis explicit.

**Step 2:** Prove it from `Erdos686PadicLift` without axioms, `native_decide`, or a target-equivalent assumption.

**Step 3:** Run `lake env lean ErdosProblems/Erdos686TwoPrimeGap.lean` and the exact Python verifier if present.

**Step 4:** Report the dependency tree, theorem obtained, and the single quantified residual gap to the parent agent; do not modify shared audit, manifest, or frontier files.
