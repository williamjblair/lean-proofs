# Erdos699 T7 Central Branch Kill Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free T7 central-branch contradiction for `2 * t = X`.

**Architecture:** Add a pure arithmetic lemma showing that if `n = F * X`, `2 < n`, `2 * t = X`, and `n - 1 ∣ t * (X - t)`, then contradiction follows because `n - 1` is coprime to `X` and hence to `t`. Add a case-I wrapper using the proved row-one divisor. This closes the central branch under the current case-I row-one hypotheses; the non-central half-row lower-bound input and full T7 remain open.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Central Branch Kill

**Files:**
- Create: `lean/Erdos699/WIP/T7CentralBranchKillTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.central_branch_false_of_sub_one_dvd_t_mul_X_sub_t
#check Erdos699.i_three_caseI_central_branch_false
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7CentralBranchKillTest.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the pure central-branch lemma**

Insert after `i_three_caseI_row_one_exists_factor`:

```lean
theorem central_branch_false_of_sub_one_dvd_t_mul_X_sub_t {n F X t : ℕ}
    (hn : n = F * X) (hn_gt : 2 < n) (hcentral : 2 * t = X)
    (hdvd : n - 1 ∣ t * (X - t)) : False := by
  have hcop_n : (n - 1).Coprime n := by
    have hsucc : n = (n - 1) + 1 := by omega
    rw [hsucc]
    exact Nat.coprime_self_add_right.mpr (by simp)
  have hX_dvd_n : X ∣ n := by
    rw [hn]
    exact dvd_mul_left X F
  have hcop_X : (n - 1).Coprime X :=
    Nat.Coprime.coprime_dvd_right hX_dvd_n hcop_n
  have ht_dvd_X : t ∣ X := by
    refine ⟨2, ?_⟩
    omega
  have hcop_t : (n - 1).Coprime t :=
    Nat.Coprime.coprime_dvd_right ht_dvd_X hcop_X
  have hXt : X - t = t := by omega
  have hdvd_tt : n - 1 ∣ t * t := by
    simpa [hXt] using hdvd
  have hdvd_t : n - 1 ∣ t := hcop_t.dvd_of_dvd_mul_left hdvd_tt
  have hself : (n - 1).Coprime (n - 1) :=
    Nat.Coprime.coprime_dvd_right hdvd_t hcop_t
  have hnm1_eq_one : n - 1 = 1 := by
    exact (Nat.coprime_self (n - 1)).mp hself
  omega
```

- [ ] **Step 4: Add the case-I wrapper**

Insert after the pure lemma:

```lean
theorem i_three_caseI_central_branch_false {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcentral : 2 * t = X) : False :=
  central_branch_false_of_sub_one_dvd_t_mul_X_sub_t hn hn_gt hcentral
    (i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X))
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming both new theorems and stating that the central branch is closed under the current case-I row-one hypotheses.

- [ ] **Step 6: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7CentralBranchKillTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 7: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7CentralBranchKillTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_central_branch_false
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains only the standard trusted base already expected in this project.

- [ ] **Step 8: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-central-branch-kill.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 central branch kill"
```
