# Erdős 699 T7 Four-Divisibility Half-Row Wrapper Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the existing Case-I factor-square squeeze no longer needs an explicit `(n / 2 - 1).Coprime 4` hypothesis when `4 | n`.

**Architecture:** Add one arithmetic lemma showing `4 | n` and `2 < n` imply `(n / 2 - 1).Coprime 4`. Then wrap the existing theorem `i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound` with this lemma to get a row-bound Case-I factor-square squeeze for the `4 | n` subcase.

**Tech Stack:** Lean 4, Mathlib, existing `lean/Erdos699/Proved/Basic.lean`.

---

### Task 1: Add Red Lean Checks

**Files:**
- Create: `lean/Erdos699/WIP/FourDvdHalfRowCheck.lean`

- [x] **Step 1: Add planned theorem checks**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check half_sub_one_coprime_four_of_four_dvd
#check i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound

end Erdos699
```

- [x] **Step 2: Run and verify RED**

Run: `lake env lean lean/Erdos699/WIP/FourDvdHalfRowCheck.lean`

Expected: FAIL because both theorem names are not defined yet.

### Task 2: Prove Four-Divisibility Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add half-row coprime-four lemma**

Add near the existing half-row coprimality lemmas:

```lean
theorem half_sub_one_coprime_four_of_four_dvd {n : ℕ}
    (h4n : 4 ∣ n) (hn : 2 < n) :
    (n / 2 - 1).Coprime 4 := by
  rcases h4n with ⟨m, hm⟩
  subst n
  have hdiv : 4 * m / 2 = 2 * m := by omega
  rw [hdiv]
  apply Nat.coprime_of_dvd
  intro p hp hpd hp4
  have hp_eq_two : p = 2 := by
    have hp_le_four : p ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hp4
    interval_cases p <;> simp at hp
  subst p
  rcases hpd with ⟨a, ha⟩
  omega
```

- [x] **Step 2: Add factor-square wrapper**

Add near the existing row-bound factor-square wrappers:

```lean
theorem i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hX_even : 2 ∣ X) (hjn : 2 * j ≤ n) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hjn
    (half_sub_one_coprime_four_of_four_dvd h4n hn_gt)
```

- [x] **Step 3: Run focused Lean check**

Run: `lake env lean lean/Erdos699/WIP/FourDvdHalfRowCheck.lean`

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[R]` entry naming:
- `Erdos699.half_sub_one_coprime_four_of_four_dvd`
- `Erdos699.i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound`

State that full T7 remains open.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
lake env lean lean/Erdos699/WIP/FourDvdHalfRowCheck.lean
lake env lean lean/Erdos699/Proved/Basic.lean
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build Erdos699.Proved.Basic
lake build
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q
```

Commit:

```bash
git add lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/FourDvdHalfRowCheck.lean \
  notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-t7-four-dvd-half-row.md
git commit -m "feat: prove erdos699 four-divisibility half-row wrapper"
```
