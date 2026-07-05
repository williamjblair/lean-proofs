# Erdős 699 T5 Conditional Endpoint Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the conditional endpoint for the T5 branch: under the row-3 no-common-prime hypothesis, `n = 3*j`, and `2 ≤ j`, contradiction follows.

**Architecture:** Add generic arithmetic lemmas converting “all prime divisors are 2” into `twoPower`, then specialize the existing no-large-window-prime bridge lemmas to prove `twoPower (n - 1)` and `twoPower (n - 2)`. Finish by applying the existing endpoint theorem `Erdos699.eq_three_of_sub_one_sub_two_twoPowers`. This remains conditional on `n = 3*j`; it does not claim full T5.

**Tech Stack:** Lean 4, Mathlib, Lake, exact Python criterion tests.

---

### Task 1: Red Check

**Files:**
- Create: `lean/Erdos699/WIP/T5ConditionalEndpointTest.lean`

- [x] **Step 1: Write the failing Lean API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.twoPower_of_unique_prime_dvd_two
#check Erdos699.twoPower_of_no_prime_ge_five_and_not_three
#check Erdos699.not_three_dvd_sub_one_of_eq_three_mul
#check Erdos699.not_three_dvd_sub_two_of_eq_three_mul
#check Erdos699.twoPower_sub_one_of_no_common_eq_three_mul
#check Erdos699.twoPower_sub_two_of_no_common_eq_three_mul
#check Erdos699.eq_three_of_no_common_eq_three_mul
#check Erdos699.no_common_eq_three_mul_false_of_two_le
```

- [x] **Step 2: Run the WIP check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/T5ConditionalEndpointTest.lean`

Expected: unknown identifier errors for the eight new names.

### Task 2: Lean Conditional Endpoint

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Prove the generic two-power bridge**

Add after the no-large-window-prime bridge lemmas:

```lean
theorem twoPower_of_unique_prime_dvd_two {m : ℕ} (hm0 : m ≠ 0)
    (huniq : ∀ {p : ℕ}, p.Prime → p ∣ m → p = 2) :
    twoPower m := by
  exact ⟨m.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniq⟩
```

```lean
theorem twoPower_of_no_prime_ge_five_and_not_three {m : ℕ} (hm0 : m ≠ 0)
    (hno5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ m) (hnot3 : ¬ 3 ∣ m) :
    twoPower m := by
  -- Prime divisors are either 2, 3, 4, or at least 5; rule out 3 and ≥5,
  -- and rule out 4 by primality.
```

- [x] **Step 2: Prove the `3 ∤ n-r` helpers for `n = 3*j`**

```lean
theorem not_three_dvd_sub_one_of_eq_three_mul {n j : ℕ} (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    ¬ 3 ∣ n - 1 := by
  intro h
  rcases h with ⟨a, ha⟩
  omega
```

```lean
theorem not_three_dvd_sub_two_of_eq_three_mul {n j : ℕ} (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    ¬ 3 ∣ n - 2 := by
  intro h
  rcases h with ⟨a, ha⟩
  omega
```

- [x] **Step 3: Prove the two `twoPower` specializations**

```lean
theorem twoPower_sub_one_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    twoPower (n - 1) := by
  -- use no-large-window-prime bridge plus `3 ∤ n - 1`.
```

```lean
theorem twoPower_sub_two_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    twoPower (n - 2) := by
  -- use no-large-window-prime bridge plus `3 ∤ n - 2`.
```

- [x] **Step 4: Prove the conditional endpoint and contradiction**

```lean
theorem eq_three_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    n = 3 :=
  eq_three_of_sub_one_sub_two_twoPowers
    (twoPower_sub_one_of_no_common_eq_three_mul hnone hn_eq (by omega))
    (twoPower_sub_two_of_no_common_eq_three_mul hnone hn_eq hj)
```

```lean
theorem no_common_eq_three_mul_false_of_two_le {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    False := by
  have hn3 : n = 3 := eq_three_of_no_common_eq_three_mul hnone hn_eq hj
  omega
```

- [x] **Step 5: Run the proved file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: clean elaboration with no warnings.

### Task 3: Green Check and Progress Log

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T5ConditionalEndpointTest.lean`

- [x] **Step 1: Rebuild and run the WIP API check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T5ConditionalEndpointTest.lean
```

Expected: the WIP file prints all eight theorem signatures.

- [x] **Step 2: Update progress**

Add a `[R]` entry:

```markdown
- [R] Proved the conditional T5 endpoint
  `Erdos699.eq_three_of_no_common_eq_three_mul` and contradiction theorem
  `Erdos699.no_common_eq_three_mul_false_of_two_le`: under row-3
  no-common-prime, `n = 3 * j`, and `2 ≤ j`, the branch is impossible. Full
  T5 remains open because the formal collapse to `n = 3*j` is not yet proved.
```

- [x] **Step 3: Remove the temporary WIP file**

Delete `lean/Erdos699/WIP/T5ConditionalEndpointTest.lean`.

### Task 4: Verification and Commit

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`
- Create: `docs/superpowers/plans/2026-07-05-erdos699-t5-conditional-endpoint.md`

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
#print axioms Erdos699.eq_three_of_no_common_eq_three_mul
#print axioms Erdos699.no_common_eq_three_mul_false_of_two_le
EOF
```

Expected: all checks pass; direct axiom audit reports only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 2: Commit**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t5-conditional-endpoint.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t5 conditional endpoint"
```
