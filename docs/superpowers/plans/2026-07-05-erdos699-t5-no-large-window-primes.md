# Erdős 699 T5 No Large Window Primes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Combine the `i = 3` product-forcing lemmas with the T5 residue-kill lemmas to prove that, in the `n = 3*j` branch, no prime `p ≥ 5` divides `n - 1` or `n - 2`.

**Architecture:** Add two symbolic `n = 3*j` bridge theorems to `lean/Erdos699/Proved/Basic.lean`. They reuse the existing no-common-prime hypothesis for row `i = 3`, first deriving product divisibility from digit forcing, then applying the residue-kill contradiction. Use a temporary WIP `#check` file for red-green API validation and update `notes/PROGRESS.md` only after the Lean proof compiles.

**Tech Stack:** Lean 4, Mathlib, Lake, exact Python criterion tests.

---

### Task 1: Red Check

**Files:**
- Create: `lean/Erdos699/WIP/T5NoLargeWindowPrimesTest.lean`

- [x] **Step 1: Write the failing Lean API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul
#check Erdos699.no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul
```

- [x] **Step 2: Run the WIP check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/T5NoLargeWindowPrimesTest.lean`

Expected: unknown identifier errors for the two new names.

### Task 2: Lean Bridge Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Prove the `n - 1` bridge**

Add after the T5 residue-kill support lemmas:

```lean
theorem no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) (hpdvd : p ∣ n - 1) :
    False := by
  have hn_gt : 1 < n := by omega
  have hprod : p ∣ j * (j - 1) :=
    i_three_window_one_product_forcing (n := n) (j := j) (p := p)
      hnone hp hp5 hn_gt hpdvd
  have hlin : p ∣ 3 * j - 1 := by
    simpa [hn_eq] using hpdvd
  exact no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one hp hp5 hj hlin hprod
```

- [x] **Step 2: Prove the `n - 2` bridge**

```lean
theorem no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 2 ≤ j) (hpdvd : p ∣ n - 2) :
    False := by
  have hn_gt : 2 < n := by omega
  have hprod : p ∣ j * (j - 1) * (j - 2) :=
    i_three_window_two_product_forcing (n := n) (j := j) (p := p)
      hnone hp hp5 hn_gt hpdvd
  have hlin : p ∣ 3 * j - 2 := by
    simpa [hn_eq] using hpdvd
  exact no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple hp hp5 hj hlin hprod
```

- [x] **Step 3: Run the proved file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: clean elaboration with no warnings.

### Task 3: Green Check and Progress Log

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T5NoLargeWindowPrimesTest.lean`

- [x] **Step 1: Rebuild and run the WIP API check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T5NoLargeWindowPrimesTest.lean
```

Expected: the WIP file prints both theorem signatures.

- [x] **Step 2: Update progress**

Add a `[R]` entry:

```markdown
- [R] Proved T5 no-large-window-prime bridge lemmas
  `Erdos699.no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul` and
  `Erdos699.no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul`: under
  the row-3 no-common-prime hypothesis and `n = 3 * j`, no prime `p ≥ 5`
  divides `n - 1` or `n - 2`. Full T5 remains open.
```

- [x] **Step 3: Remove the temporary WIP file**

Delete `lean/Erdos699/WIP/T5NoLargeWindowPrimesTest.lean`.

### Task 4: Verification and Commit

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`
- Create: `docs/superpowers/plans/2026-07-05-erdos699-t5-no-large-window-primes.md`

- [x] **Step 1: Run verification gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
```

Run the local axiom audit:

```bash
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul
#print axioms Erdos699.no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul
EOF
```

Expected: all checks pass; direct axiom audit reports only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 2: Commit**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t5-no-large-window-primes.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t5 no large window primes"
```
