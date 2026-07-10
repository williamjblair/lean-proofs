# Erdős 699 I3 Window Digit Forcing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove two `i = 3` window-row forcing lemmas: under a no-common-prime hypothesis, primes `p >= 5` dividing `n - 1` force `j % p <= 1`, and primes `p >= 5` dividing `n - 2` force `j % p <= 2`.

**Architecture:** Reuse the Lucas bridge and `prime_dvd_choose_of_not_dominated`. First show `p | C(n,3)` from the units digit obstruction `3 > n % p` when `n % p` is `1` or `2`. Then the no-common-prime hypothesis forces `p ∤ C(n,j)`, so Lucas gives digit domination for `j`, hence the units digit bound.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact Python criterion tests, repository shell gates.

---

### Task 1: Add The Failing Lean Check

**Files:**
- Create: `lean/Erdos699/WIP/I3WindowDigitForcingTest.lean`

- [x] **Step 1: Write the failing check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.i_three_window_one_digit_forcing
#check Erdos699.i_three_window_two_digit_forcing
```

- [x] **Step 2: Run the check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/I3WindowDigitForcingTest.lean`

Expected: FAIL with unknown identifier errors for both declarations.

### Task 2: Prove The Digit Forcing Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/I3WindowDigitForcingTest.lean`

- [x] **Step 1: Add the `n - 1` window lemma**

Add near the other `i = 3` support lemmas:

```lean
theorem i_three_window_one_digit_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ∣ n - 1) :
    j % p ≤ 1 := by
  ...
```

- [x] **Step 2: Add the `n - 2` window lemma**

Add:

```lean
theorem i_three_window_two_digit_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ∣ n - 2) :
    j % p ≤ 2 := by
  ...
```

- [x] **Step 3: Run the targeted Lean file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: PASS.

- [x] **Step 4: Rebuild and rerun the WIP check**

Run:

```bash
lake build Erdos699
lake env lean lean/Erdos699/WIP/I3WindowDigitForcingTest.lean
```

Expected: PASS and print both declarations.

### Task 3: Update Notes And Gates

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Mark only these support lemmas as `[R]`**

Add:

```markdown
- [R] Proved `i = 3` window digit-forcing support lemmas
  `Erdos699.i_three_window_one_digit_forcing` and
  `Erdos699.i_three_window_two_digit_forcing`. Full T4/T5 remain open.
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
#print axioms Erdos699.i_three_window_one_digit_forcing
#print axioms Erdos699.i_three_window_two_digit_forcing
EOF
git diff --check
```

Expected: all commands pass; direct axiom reports are only
`[propext, Classical.choice, Quot.sound]`.

- [x] **Step 3: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-i3-window-digit-forcing.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 i3 window digit forcing"
```
