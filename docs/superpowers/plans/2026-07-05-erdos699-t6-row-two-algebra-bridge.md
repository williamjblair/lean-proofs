# Erdos699 T6 Row Two Algebra Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the T6 second-row algebra bridge that turns the already proved `n - 2` triple-product forcing into a normalized divisor of `t * (X - t) * (X - 2 * t)`.

**Architecture:** Add one abstract congruence bridge for an odd divisor `d` of `n - 2`, then instantiate it with the existing row-3 `primePowerPartGE 5 (n - 2)` divisor. The abstraction keeps the missing 2-adic part explicit: primes below `i = 3`, especially `2`, remain free and are not smuggled into the divisor.

**Tech Stack:** Lean 4, Mathlib `Nat.ModEq`/`Int.ModEq`, existing `Erdos699.Proved.Basic`, exact Python criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6RowTwoAlgebraBridgeTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.primePowerPartGE_dvd_self
#check Erdos699.primePowerPartGE_five_coprime_four
#check Erdos699.sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
#check Erdos699.i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6RowTwoAlgebraBridgeTest.lean
```

Expected: unknown constants for the four new theorem names.

### Task 2: Add Prime-Power-Part Support

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `primePowerPartGE_dvd_self` after `primePowerPartGE_eq_self_of_forall_prime_ge`**

```lean
theorem primePowerPartGE_dvd_self {lo m : ℕ} (hm : m ≠ 0) :
    primePowerPartGE lo m ∣ m := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp _hlo _hpdvd
  exact (hp.pow_dvd_iff_le_factorization hm).mpr le_rfl
```

- [x] **Step 2: Add `finset_prod_prime_powers_coprime_four_of_ge_five` and `primePowerPartGE_five_coprime_four`**

The implementation proves the finite-product helper
`finset_prod_prime_powers_coprime_four_of_ge_five`, then instantiates it for
the filtered prime factors in `primePowerPartGE 5 m`. A selected prime cannot
divide `4`, since it is at least `5`.

### Task 3: Add Abstract Second-Row Algebra Bridge

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple` after the row-one bridge**

The theorem signature is:

```lean
theorem sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    {d n F X j t : ℕ} (hdn : d ∣ n - 2) (hcop4 : d.Coprime 4)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hj_two : 2 ≤ j)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hdvd : d ∣ j * (j - 1) * (j - 2)) :
    d ∣ t * (X - t) * (X - 2 * t)
```

The proof converts `d ∣ n - 2` and `n = F * X` to
`F * X ≡ 2 (mod d)` over `ℤ`, multiplies the triple-product congruence by
`X^3`, rewrites the result to `4 * t * (X - t) * (X - 2 * t)`, and cancels
the factor `4` using `hcop4`.

### Task 4: Add Row-3 Case-I Instantiation

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add the `primePowerPartGE 5 (n - 2)` instantiation**

The theorem signature is:

```lean
theorem i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hn_gt_two : 2 < n)
    (hj_two : 2 ≤ j) (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t) := by
  sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    (primePowerPartGE_dvd_self (by omega : n - 2 ≠ 0))
    (primePowerPartGE_five_coprime_four (n - 2))
    hn hj hn_ge_two hj_two htX h2tX
    (i_three_window_two_primePowerPartGE_dvd hnone hn_gt_two)
```

### Task 5: Verification, Progress, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6RowTwoAlgebraBridgeTest.lean`

- [x] **Step 1: Run WIP API check green and remove the WIP test file**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6RowTwoAlgebraBridgeTest.lean
```

Expected: Lean prints all four theorem signatures. Then delete the WIP API file.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved the T6 row-two algebra bridge:
  `Erdos699.i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t`
  turns the full-multiplicity large-prime part of the `n - 2` row into the
  normalized divisor `primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t)`.
  The statement keeps the row-3-free 2-adic part explicit. Full T6/T7 remain
  open.
```

- [x] **Step 3: Run verification gates**

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-row-two-algebra-bridge.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 row two algebra bridge"
```
