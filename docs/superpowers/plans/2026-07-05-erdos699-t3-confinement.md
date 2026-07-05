# Erdős 699 T3 Confinement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the T3 confinement consequences: a no-common-prime obstruction forces the top interval `(n - i, n]` to be prime-free, and no prime above `n / 2` can divide the numerator window `n(n-1)...(n-i+1)`.

**Architecture:** Reuse `commonPrimeDivisor_of_prime_in_top_interval` for the prime-free interval result. Define `fallingWindowProduct n i = ∏ r in range i, (n - r)` and prove the large-prime product exclusion by extracting a factor from the product, showing a prime `p > n/2` dividing a factor `n-r` in the window must equal that factor, and then applying the prime-free interval theorem.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact Python criterion tests, repository shell gates.

---

### Task 1: Add The Failing Lean Check

**Files:**
- Create: `lean/Erdos699/WIP/T3ConfinementTest.lean`

- [x] **Step 1: Write the failing check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.fallingWindowProduct
#check Erdos699.t3_top_interval_prime_free_of_no_common
#check Erdos699.t3_no_large_prime_dvd_fallingWindowProduct_of_no_common
```

- [x] **Step 2: Run the check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/T3ConfinementTest.lean`

Expected: FAIL with unknown identifier errors for the three new declarations.

### Task 2: Prove The Confinement Consequences

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/T3ConfinementTest.lean`

- [x] **Step 1: Add the window product definition and prime-free theorem**

Add after `commonPrimeDivisor_of_prime_in_top_interval`:

```lean
def fallingWindowProduct (n i : ℕ) : ℕ :=
  ∏ r ∈ Finset.range i, (n - r)

theorem t3_top_interval_prime_free_of_no_common {n i j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n i j q)
    (hij : i < j) (hjn : 2 * j ≤ n) (hp : p.Prime) :
    ¬ (n - i < p ∧ p ≤ n) := by
  ...
```

- [x] **Step 2: Add the large-prime product exclusion**

Add:

```lean
theorem t3_no_large_prime_dvd_fallingWindowProduct_of_no_common {n i j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n i j q)
    (hij : i < j) (hjn : 2 * j ≤ n) (hp : p.Prime) (hp_large : n < 2 * p) :
    ¬ p ∣ fallingWindowProduct n i := by
  ...
```

- [x] **Step 3: Run the targeted Lean file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: PASS.

- [x] **Step 4: Rebuild and rerun the WIP check**

Run:

```bash
lake build Erdos699
lake env lean lean/Erdos699/WIP/T3ConfinementTest.lean
```

Expected: PASS and print the three declarations.

### Task 3: Update Notes And Gates

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Mark T3 confinement as `[R]`**

Add:

```markdown
- [R] Proved T3 confinement consequences:
  `Erdos699.t3_top_interval_prime_free_of_no_common` and
  `Erdos699.t3_no_large_prime_dvd_fallingWindowProduct_of_no_common`.
```

Update the final open line so full T3 confinement is no longer listed as open.

- [x] **Step 2: Run repository gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.t3_top_interval_prime_free_of_no_common
#print axioms Erdos699.t3_no_large_prime_dvd_fallingWindowProduct_of_no_common
EOF
git diff --check
```

Expected: all commands pass; direct axiom reports are only
`[propext, Classical.choice, Quot.sound]`.

- [x] **Step 3: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t3-confinement.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t3 confinement"
```
