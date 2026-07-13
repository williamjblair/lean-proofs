# Even Laurent Cancellation Probe Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Determine by exact arithmetic whether one additional Laurent term, a one-pole Padé approximant, or another two-term Runge eliminant closes the even rows `k = 22,26,30,34` beyond `18d <= k^2`.

**Architecture:** Reconstruct the centered polynomial and canonical square-root series with `Fraction`, derive denominator-cleared eliminants symbolically, and test their lattice sizes on the exact first-complement center windows. Freeze every positive or negative conclusion in a deterministic JSON certificate, tests, and a hostile audit. No shared Lean or campaign file is modified.

**Tech Stack:** Python 3 integer arithmetic, `fractions.Fraction`, `pytest`, and existing Lean theorem surfaces as read-only dependencies.

---

### Task 1: Freeze source data and mandatory boundary fixtures

**Files:**
- Create: `compute/campaign686/agent_even_laurent_cancellation/even_laurent_cancellation_verify.py`
- Test: `compute/campaign686/agent_even_laurent_cancellation/test_even_laurent_cancellation_verify.py`

**Step 1:** Add tests asserting the quadratic last gap, first complementary gap, exact power-window endpoints, canonical polynomial part, and fixed divisors for `r = 11,13,15,17`.

**Step 2:** Run the focused tests and confirm failure because the verifier is absent.

**Step 3:** Implement exact centered-polynomial and formal-square-root-series recurrences using `Fraction` only.

**Step 4:** Run the focused tests and confirm the four row fixtures pass.

### Task 2: Test the first negative Laurent correction

**Files:**
- Modify: `compute/campaign686/agent_even_laurent_cancellation/even_laurent_cancellation_verify.py`
- Modify: `compute/campaign686/agent_even_laurent_cancellation/test_even_laurent_cancellation_verify.py`

**Step 1:** Add failing tests for the first omitted Laurent coefficient and the exact denominator-cleared identity after multiplying by the required center powers.

**Step 2:** Derive the integer eliminant from `S(w)=4S(v)` and compute its fixed divisor on all odd-center residue classes by the finite-difference gcd theorem.

**Step 3:** Compare the exact numerator/error size with the lattice step throughout each first-complement center window.

**Step 4:** Record either a strict integer trap or the smallest exact fixture that survives the proposed trap.

### Task 3: Test one-pole Padé and alternative two-term constructions

**Files:**
- Modify: `compute/campaign686/agent_even_laurent_cancellation/even_laurent_cancellation_verify.py`
- Modify: `compute/campaign686/agent_even_laurent_cancellation/test_even_laurent_cancellation_verify.py`

**Step 1:** Solve the relevant Padé coefficient equations over `Fraction` and assert their exact approximation order.

**Step 2:** Clear denominators minimally and compute all unavoidable center factors introduced into the integer numerator.

**Step 3:** Audit fixed divisors and boundary fixtures for all four rows.

**Step 4:** State the strongest uniform inequality obtained, or an exact structural obstruction quantified in `r`, `v`, and `w`.

### Task 4: Package the adversarial audit

**Files:**
- Create: `compute/campaign686/agent_even_laurent_cancellation/hostile_audit.md`

**Step 1:** Write the dependency tree and give a PASS/FAIL verdict for every claimed node.

**Step 2:** Convert every asymptotic or “dominant term” statement into an exact coefficient or interval inequality.

**Step 3:** Include all mandatory first-complement and root-pair fixtures and distinguish route falsifiers from equation counterexamples.

**Step 4:** State one quantified remaining lemma if no construction closes the rows.

### Task 5: Reproduce and freeze

**Files:**
- Modify: only files under `compute/campaign686/agent_even_laurent_cancellation/`.

**Step 1:** Run the verifier and focused pytest suite with bytecode and cache disabled.

**Step 2:** Freeze a canonical payload SHA-256 in the tests and audit.

**Step 3:** Confirm `git status` shows no modified shared committed file.
