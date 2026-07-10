# Erdős 699 T5 Residue Kill Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the residue-kill lemmas used in the `n = 3*j` branch of the `i = 3` T5 argument.

**Architecture:** Add small modular-arithmetic helpers to `lean/Erdos699/Proved/Basic.lean`, then prove that no prime `p ≥ 5` can simultaneously divide `3*j - 1` and `j(j-1)`, or `3*j - 2` and `j(j-1)(j-2)`. Use a temporary WIP `#check` file for red-green API validation and update `notes/PROGRESS.md` only after the Lean proof compiles.

**Tech Stack:** Lean 4, Mathlib, Lake, exact Python criterion tests.

---

### Task 1: Red Check

**Files:**
- Create: `lean/Erdos699/WIP/T5ResidueKillTest.lean`

- [x] **Step 1: Write the failing Lean API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.mod_eq_of_dvd_sub
#check Erdos699.three_mul_mod_eq_one_of_dvd_pred
#check Erdos699.three_mul_mod_eq_two_of_dvd_sub_two
#check Erdos699.no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one
#check Erdos699.no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple
```

- [x] **Step 2: Run the WIP check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/T5ResidueKillTest.lean`

Expected: unknown identifier errors for the five new names.

### Task 2: Lean Residue Kill Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add the reverse residue helper**

Add after the existing private `dvd_sub_of_mod_eq`:

```lean
theorem mod_eq_of_dvd_sub {j p r : ℕ} (hrj : r ≤ j) (hrp : r < p)
    (hpdvd : p ∣ j - r) :
    j % p = r := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : j = p * a + r := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hrp]
```

- [x] **Step 2: Add the linear congruence helpers**

```lean
theorem three_mul_mod_eq_one_of_dvd_pred {j p : ℕ}
    (hp : p.Prime) (hj : 0 < j) (hpdvd : p ∣ 3 * j - 1) :
    (3 * j) % p = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 3 * j = p * a + 1 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]
```

```lean
theorem three_mul_mod_eq_two_of_dvd_sub_two {j p : ℕ}
    (hp5 : 5 ≤ p) (hj : 0 < j) (hpdvd : p ∣ 3 * j - 2) :
    (3 * j) % p = 2 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 3 * j = p * a + 2 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < p)]
```

- [x] **Step 3: Add the two T5 residue-kill support lemmas**

```lean
theorem no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) (hlin : p ∣ 3 * j - 1)
    (hprod : p ∣ j * (j - 1)) : False := by
  -- split `p ∣ j(j-1)` and compare residues of `3*j`.
```

```lean
theorem no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple {j p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 2 ≤ j) (hlin : p ∣ 3 * j - 2)
    (hprod : p ∣ j * (j - 1) * (j - 2)) : False := by
  -- split `p ∣ j(j-1)(j-2)` and compare residues of `3*j`.
```

- [x] **Step 4: Run the proved file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: clean elaboration with no warnings.

### Task 3: Green Check and Progress Log

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T5ResidueKillTest.lean`

- [x] **Step 1: Rebuild and run the WIP API check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T5ResidueKillTest.lean
```

Expected: the WIP file prints all five theorem/type signatures.

- [x] **Step 2: Update progress**

Add a `[R]` entry:

```markdown
- [R] Proved T5 residue-kill support lemmas
  `Erdos699.no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one` and
  `Erdos699.no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple`: in the
  `n = 3*j` branch, a prime `p ≥ 5` cannot divide both the relevant window
  row and the forced product. Full T5 remains open.
```

- [x] **Step 3: Remove the temporary WIP file**

Delete `lean/Erdos699/WIP/T5ResidueKillTest.lean`.

### Task 4: Verification and Commit

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`
- Create: `docs/superpowers/plans/2026-07-05-erdos699-t5-residue-kill.md`

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
#print axioms Erdos699.no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one
#print axioms Erdos699.no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple
EOF
```

Expected: all checks pass; direct axiom audit reports only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 2: Commit**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t5-residue-kill.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t5 residue kill"
```
