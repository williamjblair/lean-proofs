# Erdős 699 T5 Power Endpoint Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the elementary endpoint used in T5: if `n - 1` and `n - 2` are both powers of two, then `n = 3`.

**Architecture:** Add a local predicate `twoPower m := ∃ a, m = 2 ^ a` in `lean/Erdos699/Proved/Basic.lean`. Prove that an odd power of two is `1`, then use parity of two consecutive natural numbers to prove the T5 endpoint.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact Python criterion tests, repository shell gates.

---

### Task 1: Add The Failing Lean Check

**Files:**
- Create: `lean/Erdos699/WIP/T5PowerEndpointTest.lean`

- [x] **Step 1: Write the failing check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.twoPower
#check Erdos699.twoPower_eq_one_of_odd
#check Erdos699.eq_three_of_sub_one_sub_two_twoPowers
```

- [x] **Step 2: Run the check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/T5PowerEndpointTest.lean`

Expected: FAIL with unknown identifier errors for the three declarations.

### Task 2: Prove The Endpoint

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/T5PowerEndpointTest.lean`

- [x] **Step 1: Add the predicate and odd-power helper**

Add near the T3/T5 support section:

```lean
def twoPower (m : ℕ) : Prop :=
  ∃ a : ℕ, m = 2 ^ a

theorem twoPower_eq_one_of_odd {m : ℕ} (hm : twoPower m) (hodd : Odd m) :
    m = 1 := by
  ...
```

- [x] **Step 2: Add the T5 endpoint theorem**

Add:

```lean
theorem eq_three_of_sub_one_sub_two_twoPowers {n : ℕ}
    (h1 : twoPower (n - 1)) (h2 : twoPower (n - 2)) :
    n = 3 := by
  ...
```

- [x] **Step 3: Run the targeted Lean file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: PASS.

- [x] **Step 4: Rebuild and rerun the WIP check**

Run:

```bash
lake build Erdos699
lake env lean lean/Erdos699/WIP/T5PowerEndpointTest.lean
```

Expected: PASS and print the three declarations.

### Task 3: Update Notes And Gates

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Mark only the endpoint as `[R]`**

Add:

```markdown
- [R] Proved the T5 elementary endpoint
  `Erdos699.eq_three_of_sub_one_sub_two_twoPowers`: if `n - 1` and `n - 2`
  are both powers of two, then `n = 3`. Full T5 remains open.
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
#print axioms Erdos699.eq_three_of_sub_one_sub_two_twoPowers
EOF
git diff --check
```

Expected: all commands pass; the direct axiom report is only
`[propext, Classical.choice, Quot.sound]`.

- [x] **Step 3: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t5-power-endpoint.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t5 power endpoint"
```
