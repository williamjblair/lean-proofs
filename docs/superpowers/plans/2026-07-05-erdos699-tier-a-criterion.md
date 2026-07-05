# Erdős 699 Tier A Criterion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Strengthen the #699 Lean criterion scaffold toward Tier A by proving that the finite `dominated` predicate really captures all base-`p` digit inequalities for `p ≥ 2`, then attempt the Lucas nonzero bridge.

**Architecture:** Keep all sorry-free, reusable facts in `lean/Erdos699/Proved/Basic.lean`. Use temporary `#check`/scratch Lean commands from the shell only for API discovery, not as committed artifacts. Update `notes/PROGRESS.md` with `[R]` only for compiled theorems and `[OPEN]` for any bridge not completed.

**Tech Stack:** Lean 4.29.1, Mathlib v4.29.1, Lake, pytest for existing exact criterion tests.

---

### Task 1: Prove the Finite Digit Range Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [ ] **Step 1: Discover exact pow/range API**

Run:

```bash
lake env lean /tmp/erdos699_checks.lean
```

with a scratch file containing:

```lean
import Erdos699.Proved.Basic

#check Nat.lt_pow_self
#check Nat.div_eq_of_lt
#check Finset.mem_range
#check Finset.filter_eq_empty_iff
```

Expected: output names and types for the lemmas used in the next step.

- [ ] **Step 2: Add finite range theorem**

Add this theorem near `dominated`:

```lean
theorem dominated_iff_forall_mem_range (k n p : ℕ) :
    dominated k n p ↔
      ∀ r ∈ Finset.range (max k n + 1), digit k p r ≤ digit n p r := by
  classical
  unfold dominated
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h r hr
    exact Nat.not_lt.mp (h r hr)
  · intro h r hr
    exact Nat.not_lt.mpr (h r hr)
```

- [ ] **Step 3: Add all-level theorem for bases at least two**

Add:

```lean
theorem dominated_iff_forall_digits {k n p : ℕ} (hp : 2 ≤ p) :
    dominated k n p ↔ ∀ r : ℕ, digit k p r ≤ digit n p r := by
  classical
  constructor
  · intro h r
    by_cases hr : r ∈ Finset.range (max k n + 1)
    · exact (dominated_iff_forall_mem_range k n p).mp h r hr
    · have hle : max k n + 1 ≤ r := by
        exact Nat.le_of_not_gt (by simpa using hr)
      have hm_lt_r : max k n < r := Nat.lt_of_succ_le hle
      have hr_pos : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hm_lt_r
      have hr_lt_pow : r < p ^ r := Nat.lt_pow_self hp hr_pos.ne'
      have hk_lt : k < p ^ r := (le_max_left k n).trans_lt (hm_lt_r.trans hr_lt_pow)
      have hn_lt : n < p ^ r := (le_max_right k n).trans_lt (hm_lt_r.trans hr_lt_pow)
      simp [digit, Nat.div_eq_of_lt hk_lt, Nat.div_eq_of_lt hn_lt]
  · intro h
    exact (dominated_iff_forall_mem_range k n p).mpr fun r _ => h r
```

- [ ] **Step 4: Verify the target**

Run:

```bash
lake build Erdos699
```

Expected: PASS.

### Task 2: Attempt the Lucas Nonzero Bridge

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Add supporting factor nondivisibility lemma**

Try to add:

```lean
theorem prime_not_dvd_small_choose {p a b : ℕ} (hp : p.Prime) (ha : a < p) :
    ¬ p ∣ Nat.choose a b := by
  by_cases hb : b ≤ a
  · have hchoose_ne : Nat.choose a b ≠ 0 := Nat.choose_ne_zero hb
    intro hdiv
    have hfac_pos : 0 < (Nat.choose a b).factorization p :=
      hp.factorization_pos_of_dvd hchoose_ne hdiv
    have hfac_zero : (Nat.choose a b).factorization p = 0 :=
      Nat.factorization_choose_eq_zero_of_lt ha
    omega
  · have hchoose : Nat.choose a b = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)
    simp [hchoose]
```

If the `b > a` branch shows the statement is false because `p ∣ 0`, replace this with the correct conditional lemma requiring `b ≤ a`.

- [ ] **Step 2: Add bridge theorem only if the proof closes sorry-free**

Target statement:

```lean
theorem lucas_nonzero_mod_prime_iff_dominated {n k p : ℕ} (hp : p.Prime) :
    Nat.choose n k % p ≠ 0 ↔ dominated k n p := by
  ...
```

Use `Choose.lucas_theorem_nat` with `a := max k n + 1`. The theorem does not need `k ≤ n`; the digit-domination side is false automatically when the digit comparison fails, matching the zero binomial coefficient.

- [ ] **Step 3: Update progress tags**

Update progress with:

```markdown
- [R] Proved `Erdos699.dominated_iff_forall_mem_range` and
  `Erdos699.dominated_iff_forall_digits`, showing the finite decidable
  predicate captures all digit inequalities for bases `p ≥ 2`.
- [R] Proved `Erdos699.lucas_nonzero_mod_prime_iff_dominated`, the
  sorry-free Lucas bridge for the decidable digit-domination predicate.
```

### Task 3: Verify and Commit

**Files:**
- Modified files from Tasks 1-2.

- [ ] **Step 1: Run gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
git diff --check
```

Expected: all pass.

- [ ] **Step 2: Commit**

Run:

```bash
git add lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-tier-a-criterion.md
git commit -m "feat: prove erdos699 digit domination range"
```

Expected: one new milestone commit on `erdos699/full-solve`.
