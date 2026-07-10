# Erdos699 T5 Collapse Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the missing T5 Case I-A0 collapse and assemble the full odd `3 ∥ n` row-3 theorem in Lean.

**Architecture:** Reuse the existing Lucas/no-common infrastructure and the newly proved `n = 3 * j` endpoint. First prove the row-3 divisor forcing `n / 3 ∣ j`; then use `2 * j ≤ n` to collapse to `n = 3 * j`; finally call the endpoint contradiction.

**Tech Stack:** Lean 4, Mathlib `Nat`, existing `Erdos699.Proved.Basic`, exact pytest criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T5CollapseTest.lean`

- [x] **Step 1: Write the failing WIP check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.t5_collapse_eq_three_mul_of_no_common
#check Erdos699.t5_i_eq_three_odd_three_exactly_once
```

- [x] **Step 2: Run Lean and confirm the expected failure**

Run:

```bash
lake env lean lean/Erdos699/WIP/T5CollapseTest.lean
```

Expected: Lean reports unknown constants for the two new theorem names.

### Task 2: Prove Collapse Prerequisites

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `prime_dvd_choose_three_of_prime_ge_five_dvd`**

Insert after `i_three_window_two_primeRadicalGE_dvd`:

```lean
theorem prime_dvd_choose_three_of_prime_ge_five_dvd {n p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpn : p ∣ n) :
    p ∣ Nat.choose n 3 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_mod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have hthree_mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  simp [digit, hn_mod, hthree_mod] at hdigits
```

- [x] **Step 2: Add the row-3 divisor forcing helper**

Insert after the previous theorem:

```lean
theorem dvd_j_of_no_common_i_three {d n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 3 j p) (hn : 0 < n) (hj : 0 < j)
    (hdn : d ∣ n) (hrel : ∀ p : ℕ, p.Prime → p ∣ d → 3 ≤ p)
    (hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 3) :
    d ∣ j := by
  have hcop : d.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpchoose
    exact hnone p ⟨hp, hrel p hp hpd, hdchoose p hp hpd, hpchoose⟩
  have hn_dvd : n ∣ j * Nat.choose n j := n_dvd_mul_choose_self hn hj
  have hdprod : d ∣ j * Nat.choose n j := Nat.dvd_trans hdn hn_dvd
  exact (hcop.dvd_mul_right).mp hdprod
```

### Task 3: Prove T5 Collapse and Full Case I-A0

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `lean/Erdos699/WIP/T5CollapseTest.lean`

- [x] **Step 1: Add the `n / 3` prime divisor bound**

Insert after `dvd_j_of_no_common_i_three`:

```lean
theorem prime_ge_five_of_dvd_div_three_odd_not_nine {n p : ℕ}
    (hodd : Odd n) (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hp : p.Prime)
    (hpd : p ∣ n / 3) :
    5 ≤ p := by
  have hn_eq : n = 3 * (n / 3) := (Nat.mul_div_cancel' h3n).symm
  have hdn : n / 3 ∣ n := by
    refine ⟨3, ?_⟩
    rw [hn_eq, mul_comm]
  by_cases hp2 : p = 2
  · subst p
    have h2n : 2 ∣ n := Nat.dvd_trans hpd hdn
    have hn_even : Even n := even_iff_two_dvd.mpr h2n
    exact False.elim ((Nat.not_odd_iff_even.mpr hn_even) hodd)
  by_cases hp3 : p = 3
  · subst p
    rcases hpd with ⟨a, ha⟩
    apply False.elim
    apply hnot9
    refine ⟨a, ?_⟩
    rw [hn_eq, ha]
    omega
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp2le : 2 ≤ p := hp.two_le
  omega
```

- [x] **Step 2: Add the collapse theorem**

Insert after the previous theorem:

```lean
theorem t5_collapse_eq_three_mul_of_no_common {n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 3 j p) (hodd : Odd n)
    (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hj : 3 < j) (hjn : 2 * j ≤ n) :
    n = 3 * j := by
  let d := n / 3
  have hj_pos : 0 < j := by omega
  have hn_pos : 0 < n := by omega
  have hn_eq : n = 3 * d := by
    dsimp [d]
    exact (Nat.mul_div_cancel' h3n).symm
  have hdn : d ∣ n := by
    refine ⟨3, ?_⟩
    rw [hn_eq, mul_comm]
  have hrel : ∀ p : ℕ, p.Prime → p ∣ d → 3 ≤ p := by
    intro p hp hpd
    have hp5 : 5 ≤ p :=
      prime_ge_five_of_dvd_div_three_odd_not_nine hodd h3n hnot9 hp (by simpa [d] using hpd)
    omega
  have hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 3 := by
    intro p hp hpd
    have hp5 : 5 ≤ p :=
      prime_ge_five_of_dvd_div_three_odd_not_nine hodd h3n hnot9 hp (by simpa [d] using hpd)
    exact prime_dvd_choose_three_of_prime_ge_five_dvd hp hp5 (Nat.dvd_trans hpd hdn)
  have hdj : d ∣ j := dvd_j_of_no_common_i_three hnone hn_pos hj_pos hdn hrel hdchoose
  have hd_pos : 0 < d := by omega
  have hj_lt_two_d : j < 2 * d := by omega
  have hj_eq_d : j = d := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdj hj_lt_two_d
  rw [hn_eq, hj_eq_d]
```

- [x] **Step 3: Add the full T5 theorem**

Insert after the collapse theorem:

```lean
theorem t5_i_eq_three_odd_three_exactly_once {n j : ℕ} (hodd : Odd n)
    (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hj : 3 < j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 3 j p := by
  by_contra hnone_exists
  rw [not_exists] at hnone_exists
  have hn_eq : n = 3 * j :=
    t5_collapse_eq_three_mul_of_no_common hnone_exists hodd h3n hnot9 hj hjn
  exact no_common_eq_three_mul_false_of_two_le hnone_exists hn_eq (by omega)
```

- [x] **Step 4: Run the WIP check and remove it**

Run:

```bash
lake env lean lean/Erdos699/WIP/T5CollapseTest.lean
```

Expected: Lean prints both theorem signatures. Then delete `lean/Erdos699/WIP/T5CollapseTest.lean`.

### Task 4: Progress Log and Verification

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Add the `[R]` progress entry**

Append before the `[OPEN]` line:

```md
- [R] Proved full T5 Case I-A0 as
  `Erdos699.t5_i_eq_three_odd_three_exactly_once`: for row `i = 3`,
  `n` odd, `3 ∣ n`, `¬ 9 ∣ n`, `3 < j`, and `2 * j ≤ n`, a relevant common
  prime divisor exists.
```

- [x] **Step 2: Run verification gates**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
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
#print axioms Erdos699.t5_collapse_eq_three_mul_of_no_common
#print axioms Erdos699.t5_i_eq_three_odd_three_exactly_once
EOF
```

- [x] **Step 3: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t5-collapse.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t5 odd case"
```
