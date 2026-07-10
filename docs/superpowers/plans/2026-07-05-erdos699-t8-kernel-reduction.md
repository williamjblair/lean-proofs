# Erdős 699 T8 Kernel Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Name the consecutive-divisor kernel in Lean and prove that the `4 | n` Case-I row hypotheses reduce to that kernel with coprime factors below `n / 2`.

**Architecture:** Add small Prop definitions for the kernel and the half-row-bounded kernel. Then package the existing row-one divisor theorem, half-row row-two theorem, coprimality lemma, and row-bound hypothesis into one reduction theorem.

**Tech Stack:** Lean 4, Mathlib, existing `lean/Erdos699/Proved/Basic.lean`.

---

### Task 1: Add Red Lean Checks

**Files:**
- Create: `lean/Erdos699/WIP/KernelReductionCheck.lean`

- [x] **Step 1: Add planned declaration checks**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check consecutiveDivisorKernel
#check consecutiveDivisorKernelBelow
#check i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common

end Erdos699
```

- [x] **Step 2: Run and verify RED**

Run: `lake env lean lean/Erdos699/WIP/KernelReductionCheck.lean`

Expected: FAIL because the declaration names are not defined yet.

### Task 2: Define the Kernel and Prove the Reduction

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add kernel definitions**

Add after `commonPrimeDivisor`:

```lean
/-- The consecutive-divisor kernel: two fixed divisors packed into products of
one, then two, consecutive gaps from `t`. -/
def consecutiveDivisorKernel (N1 N2 t : ℕ) : Prop :=
  N1 ∣ t * (t - 1) ∧ N2 ∣ t * (t - 1) * (t - 2)

/-- The same kernel with the problem's half-row bound. -/
def consecutiveDivisorKernelBelow (N1 N2 bound t : ℕ) : Prop :=
  2 * t ≤ bound ∧ consecutiveDivisorKernel N1 N2 t
```

- [x] **Step 2: Add the `4 | n` Case-I kernel reduction theorem**

Add after `i_three_caseI_half_sub_one_dvd_row_two_product`:

```lean
theorem i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn_gt : 2 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    (n - 1).Coprime (n / 2 - 1) ∧
      consecutiveDivisorKernelBelow (n - 1) (n / 2 - 1) n j := by
  have hcop : (n - 1).Coprime (n / 2 - 1) :=
    (half_sub_one_coprime_sub_one_of_even h2n hn_gt).symm
  have hrow1 : n - 1 ∣ j * (j - 1) :=
    i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n
  have hrow2 : n / 2 - 1 ∣ j * (j - 1) * (j - 2) :=
    i_three_caseI_half_sub_one_dvd_row_two_product hnone h2n h3n hn_gt
      (half_sub_one_coprime_four_of_four_dvd h4n hn_gt)
  refine ⟨hcop, ?_⟩
  exact ⟨hjn, hrow1, hrow2⟩
```

- [x] **Step 3: Run focused Lean check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/KernelReductionCheck.lean
```

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[R]` entry naming:
- `Erdos699.consecutiveDivisorKernel`
- `Erdos699.consecutiveDivisorKernelBelow`
- `Erdos699.i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common`

State that the theorem is a kernel reduction and does not prove the kernel empty.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
lake env lean lean/Erdos699/WIP/KernelReductionCheck.lean
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
git add lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/KernelReductionCheck.lean \
  notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-t8-kernel-reduction.md
git commit -m "feat: formalize erdos699 kernel reduction"
```
