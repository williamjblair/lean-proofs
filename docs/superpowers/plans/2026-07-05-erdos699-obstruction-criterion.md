# Erdős 699 Obstruction Criterion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the corrected obstruction criterion: absence of a relevant common prime divisor is equivalent to digit-domination for `i` or `j` at every prime `p >= i`.

**Architecture:** Add a predicate `obstructionCriterion` in `lean/Erdos699/Proved/Basic.lean` after `relevantPrime`, so the quantifier explicitly carries the `i <= p` hypothesis. Prove the equivalence with `∀ p, ¬ commonPrimeDivisor n i j p` using the Lucas bridge and the existing `prime_dvd_choose_of_not_dominated` helper.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact Python criterion tests, repository shell gates.

---

### Task 1: Add The Failing Lean Check

**Files:**
- Create: `lean/Erdos699/WIP/ObstructionCriterionTest.lean`

- [x] **Step 1: Write the failing check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.obstructionCriterion
#check Erdos699.no_commonPrimeDivisor_iff_obstructionCriterion
```

- [x] **Step 2: Run the check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/ObstructionCriterionTest.lean`

Expected: FAIL with unknown identifier errors for
`Erdos699.obstructionCriterion` and
`Erdos699.no_commonPrimeDivisor_iff_obstructionCriterion`.

### Task 2: Prove The Criterion Bridge

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/ObstructionCriterionTest.lean`

- [x] **Step 1: Add the predicate and bridge theorem**

Add after `relevantPrime_ignores_small`:

```lean
/-- The corrected obstruction criterion: only primes `p >= i` are constrained. -/
def obstructionCriterion (n i j : ℕ) : Prop :=
  ∀ p : ℕ, relevantPrime i p → dominated i n p ∨ dominated j n p

theorem no_commonPrimeDivisor_iff_obstructionCriterion (n i j : ℕ) :
    (∀ p : ℕ, ¬ commonPrimeDivisor n i j p) ↔ obstructionCriterion n i j := by
  ...
```

- [x] **Step 2: Run the targeted Lean file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: PASS.

- [x] **Step 3: Rebuild and rerun the WIP check**

Run:

```bash
lake build Erdos699
lake env lean lean/Erdos699/WIP/ObstructionCriterionTest.lean
```

Expected: PASS and print both declarations.

### Task 3: Update Notes And Gates

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Mark the bridge as `[R]`**

Add:

```markdown
- [R] Proved `Erdos699.no_commonPrimeDivisor_iff_obstructionCriterion`, the
  formal corrected counterexample criterion. The predicate quantifies over
  `relevantPrime i p`, so primes `p < i` impose no digit-domination condition.
```

- [x] **Step 2: Run repository gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.no_commonPrimeDivisor_iff_obstructionCriterion
EOF
git diff --check
```

Expected: all commands pass; the direct axiom report is only
`[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 3: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-obstruction-criterion.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 obstruction criterion"
```
