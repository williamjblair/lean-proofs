# Erdős 699 i=3 Window Product Forcing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove sorry-free Lean lemmas converting existing `i = 3` window digit forcing into product divisibility constraints.

**Architecture:** Keep reusable proved material in `lean/Erdos699/Proved/Basic.lean`. Use a temporary WIP `#check` file to drive the API first, then remove it after the theorem names compile. Record only the proven result in `notes/PROGRESS.md`; do not claim T4 or T5.

**Tech Stack:** Lean 4, Mathlib, Lake, exact Python perimeter tests.

---

### Task 1: Red Check

**Files:**
- Create: `lean/Erdos699/WIP/I3WindowProductForcingTest.lean`

- [x] **Step 1: Write the failing Lean API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.dvd_mul_sub_one_of_mod_le_one
#check Erdos699.dvd_mul_sub_one_sub_two_of_mod_le_two
#check Erdos699.i_three_window_one_product_forcing
#check Erdos699.i_three_window_two_product_forcing
```

- [x] **Step 2: Run the WIP check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/I3WindowProductForcingTest.lean`

Expected: unknown identifier errors for the four theorem names.

### Task 2: Product Divisibility Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Prove residue-to-product helper lemmas**

Add after `Erdos699.i_three_window_two_digit_forcing`:

```lean
theorem dvd_mul_sub_one_of_mod_le_one {j p : ℕ} (hp : p.Prime) (hmod : j % p ≤ 1) :
    p ∣ j * (j - 1) := by
  -- split on `j % p = 0` or `j % p = 1`.
```

```lean
theorem dvd_mul_sub_one_sub_two_of_mod_le_two {j p : ℕ} (hp : p.Prime)
    (hmod : j % p ≤ 2) :
    p ∣ j * (j - 1) * (j - 2) := by
  -- split on `j % p = 0`, `1`, or `2`.
```

- [x] **Step 2: Prove the i=3 wrappers**

```lean
theorem i_three_window_one_product_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ∣ n - 1) :
    p ∣ j * (j - 1) :=
  dvd_mul_sub_one_of_mod_le_one hp
    (i_three_window_one_digit_forcing hnone hp hp5 hn hpdvd)
```

```lean
theorem i_three_window_two_product_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ∣ n - 2) :
    p ∣ j * (j - 1) * (j - 2) :=
  dvd_mul_sub_one_sub_two_of_mod_le_two hp
    (i_three_window_two_digit_forcing hnone hp hp5 hn hpdvd)
```

- [x] **Step 3: Run the proved file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: clean elaboration with no `sorry`.

### Task 3: Green Check and Progress Log

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/I3WindowProductForcingTest.lean`

- [x] **Step 1: Run the WIP API check**

Run: `lake env lean lean/Erdos699/WIP/I3WindowProductForcingTest.lean`

Expected: clean elaboration.

- [x] **Step 2: Update progress**

Add a `[R]` entry:

```markdown
- [R] Proved `Erdos699.dvd_mul_sub_one_of_mod_le_one`,
  `Erdos699.dvd_mul_sub_one_sub_two_of_mod_le_two`, and the `i = 3`
  product-forcing wrappers `Erdos699.i_three_window_one_product_forcing` and
  `Erdos699.i_three_window_two_product_forcing`. These turn the existing
  residue bounds into divisibility by `j(j-1)` and `j(j-1)(j-2)`.
```

- [x] **Step 3: Remove the temporary WIP file**

Delete `lean/Erdos699/WIP/I3WindowProductForcingTest.lean`.

### Task 4: Verification and Commit

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`
- Create: `docs/superpowers/plans/2026-07-05-erdos699-i3-window-product-forcing.md`

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
#print axioms Erdos699.i_three_window_one_product_forcing
#print axioms Erdos699.i_three_window_two_product_forcing
EOF
```

Expected: build/check scripts pass; axiom audit reports only allowed imported axioms.

- [ ] **Step 2: Commit**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-i3-window-product-forcing.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 i3 window product forcing"
```
