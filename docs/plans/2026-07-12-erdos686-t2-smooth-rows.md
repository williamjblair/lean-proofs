# Erdős 686 Target 2 Smooth-Row Attack Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove `LargeKSmoothHypothesis`, or bank one new exact quantified lemma strictly weaker than it, by combining equation-level prime-power matching, row divisibility, and reflection-owner alignment.

**Architecture:** Reconstruct the exact owner ledger prime by prime and split every reflection-center contribution into non-reflected mass, already absorbed by `lcm(1,...,k-1)`, and reflected mass. Search only for identities that use the full equation or all rows and therefore survive the two mandatory prefix fixtures. Any successful arithmetic statement receives an independent exact verifier before a Lean theorem is attempted.

**Tech Stack:** Python 3 exact integers and `fractions.Fraction`, pytest, Lean 4/mathlib, repository manifest and axiom gates.

---

### Task 1: Freeze the theorem surface and boundary fixtures

**Files:**
- Read: `codex/prompt_686_full_solve.md`
- Read: `compute/campaign686/approach_registry.md`
- Read: `compute/campaign686/large_k_findings.md`
- Read: `compute/campaign686/matching_compression_findings.md`
- Read: `compute/campaign686/reflection_lcm_correlation_hostile_audit.md`

**Step 1:** Record the exact target premises and the stronger equation-level facts already banked.

**Step 2:** Reproduce `(984,3177026,4480)` through row 16 and `(244,48502,277)` through row 15 with the checked-in tests.

**Step 3:** Reject any candidate lemma whose premises are only a fixed row prefix, lower-block smoothness alone, or a raw size bound on the centered lcm.

### Task 2: Build a reflected-owner ledger

**Files:**
- Create only if a new invariant survives: `compute/campaign686/agent_t2_smooth_rows/reflected_owner_ledger.py`
- Create only if needed: `compute/campaign686/agent_t2_smooth_rows/test_reflected_owner_ledger.py`

**Step 1:** For exact integer fixtures and bounded searches, compute maximum lower and upper owners for every prime and the factorial-loss-truncated reflection-center exponent.

**Step 2:** Classify owner pairs by `i+j=k+1` and verify the banked offset divisibility exactly.

**Step 3:** Test global correlations involving reflected owner indices, row landings, valuations of `S`, and complementary lower/upper terms.

**Step 4:** Add a regression test for each mandatory fixture before accepting a universal conjecture.

### Task 3: Prove the strongest surviving identity

**Files:**
- Create only for sound progress: `compute/campaign686/agent_t2_smooth_rows/findings.md`
- Create only after exact audit: `ErdosProblems/Erdos686ReflectedAlignmentElimination.lean`

**Step 1:** State the candidate with all quantifiers, constants, and hypotheses explicit.

**Step 2:** Give a dependency tree down to equation equality, concentration, reflection gcd, and row divisibility.

**Step 3:** Prove it on paper without using finite-search evidence as a universal argument.

**Step 4:** Formalize it in Lean only if it is strictly weaker than `LargeKSmoothHypothesis` and introduces no theorem-strength placeholder.

### Task 4: Hostile audit and handoff

**Files:**
- Test: `compute/campaign686/test_large_k_rows.py`
- Test: `compute/campaign686/test_matching_compression.py`
- Test: `compute/campaign686/test_reflection_lcm_correlation_verify.py`
- Test: `compute/campaign686/test_reflection_lcm_correlation_hostile_verify.py`

**Step 1:** Run all four exact test groups and the new isolated tests.

**Step 2:** Compile any new Lean module directly with `lake env lean`.

**Step 3:** Scan the new proof surface for `sorry`, `admit`, `axiom`, and `native_decide`.

**Step 4:** Report either the complete contradiction or one genuinely new quantified lemma plus the exact remaining gap.
