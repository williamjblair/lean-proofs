# Erdős 699 Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish the first reproducible #699 branch milestone without claiming any unproved rung.

**Architecture:** Keep the existing root Lake project, add a second Lean library `Erdos699` rooted at `lean/`, and keep WIP proof sketches out of the default build. Put exact arithmetic scanners under `compute/` with pytest tests that lock the corrected Lucas counterexample criterion, especially the `p < i` free-prime trap.

**Tech Stack:** Lean 4.29.1, Mathlib v4.29.1, Python 3 standard library, pytest.

---

### Task 1: Wire the #699 Lean Library Root

**Files:**
- Modify: `lakefile.toml`
- Create: `lean/Erdos699.lean`
- Create: `lean/Erdos699/Proved/Basic.lean`
- Modify: `scripts/check_axioms.sh`

- [ ] **Step 1: Add an empty checked module before adding the library**

Create `lean/Erdos699/Proved/Basic.lean`:

```lean
/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Factorization

namespace Erdos699

/-- The base-`p` digit at level `r`, with level zero the units digit. -/
def digit (k p r : ℕ) : ℕ :=
  k / p ^ r % p

/-- Digitwise domination of `k` by `n` in base `p`. -/
def dominated (k n p : ℕ) : Prop :=
  (Finset.range (max k n + 1)).filter (fun r => digit n p r < digit k p r) = ∅

instance (k n p : ℕ) : Decidable (dominated k n p) :=
  inferInstanceAs
    (Decidable ((Finset.range (max k n + 1)).filter
      (fun r => digit n p r < digit k p r) = ∅))

/-- A prime `p` is relevant to row `i` exactly when `p ≥ i`. -/
def relevantPrime (i p : ℕ) : Prop :=
  p.Prime ∧ i ≤ p

theorem relevantPrime_ignores_small {i p : ℕ} (hp : p < i) :
    ¬ relevantPrime i p := by
  intro h
  exact Nat.not_le_of_gt hp h.2

end Erdos699
```

Create `lean/Erdos699.lean`:

```lean
import Erdos699.Proved.Basic
```

- [ ] **Step 2: Add the Lake library**

In `lakefile.toml`, add:

```toml
[[lean_lib]]
name = "Erdos699"
srcDir = "lean"
```

and extend `defaultTargets` to:

```toml
defaultTargets = ["ErdosProblems", "Erdos699"]
```

- [ ] **Step 3: Extend the sorry grep to proved #699 files**

In `scripts/check_axioms.sh`, replace the fixed `grep` block with:

```bash
for proof_dir in ErdosProblems lean/Erdos699/Proved; do
  if [ -d "$proof_dir" ] && grep -rnoE '\b(sorry|admit)\b' "$proof_dir" ; then
    fail "literal sorry/admit in $proof_dir/"
  fi
done
```

- [ ] **Step 4: Verify the Lean library compiles**

Run:

```bash
lake build Erdos699
```

Expected: PASS with no errors.

### Task 2: Add Exact Criterion Tests First

**Files:**
- Create: `compute/tests/test_criterion.py`
- Create later: `compute/erdos699.py`

- [ ] **Step 1: Write failing tests for the corrected criterion**

Create `compute/tests/test_criterion.py`:

```python
from compute.erdos699 import (
    binom_mod_prime_nonzero_by_lucas,
    counterexample_candidate,
    criterion_obstruction_primes,
    dominated,
    primes_upto,
)


def test_primes_below_i_are_free_in_counterexample_criterion() -> None:
    n, i, j = 10, 4, 5
    assert 2 < i and 3 < i
    assert dominated(i, n, 2) is False
    assert dominated(j, n, 3) is False
    obstructions = criterion_obstruction_primes(n, i, j)
    assert 2 not in obstructions
    assert 3 not in obstructions
    assert 7 in obstructions
    assert counterexample_candidate(n, i, j) is False


def test_i_three_does_not_constrain_two() -> None:
    n, i, j = 8, 3, 4
    assert 2 < i
    assert dominated(i, n, 2) is False
    obstructions = criterion_obstruction_primes(n, i, j)
    assert 2 not in obstructions
    assert 7 in obstructions
    assert counterexample_candidate(n, i, j) is False


def test_lucas_digit_predicate_matches_binomial_mod_prime_for_small_values() -> None:
    for p in primes_upto(13):
        for n in range(0, 60):
            for k in range(0, n + 1):
                assert binom_mod_prime_nonzero_by_lucas(n, k, p) == dominated(k, n, p)
```

- [ ] **Step 2: Run the test and confirm RED**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
```

Expected: FAIL with `ModuleNotFoundError: No module named 'compute.erdos699'`.

### Task 3: Implement the Exact Criterion

**Files:**
- Create: `compute/__init__.py`
- Create: `compute/erdos699.py`

- [ ] **Step 1: Add the implementation**

Create `compute/__init__.py` as an empty package marker.

Create `compute/erdos699.py`:

```python
from __future__ import annotations

from math import comb


def primes_upto(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= limit:
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
        p += 1
    return [p for p in range(2, limit + 1) if sieve[p]]


def digit(k: int, p: int, level: int) -> int:
    if p < 2:
        raise ValueError("base p must be at least 2")
    if k < 0 or level < 0:
        raise ValueError("k and level must be nonnegative")
    return (k // (p**level)) % p


def dominated(k: int, n: int, p: int) -> bool:
    if p < 2:
        raise ValueError("base p must be at least 2")
    if k < 0 or n < 0:
        raise ValueError("k and n must be nonnegative")
    m = max(k, n)
    level = 0
    while p**level <= m:
        if digit(k, p, level) > digit(n, p, level):
            return False
        level += 1
    return True


def binom_mod_prime_nonzero_by_lucas(n: int, k: int, p: int) -> bool:
    if not (0 <= k <= n):
        return False
    return comb(n, k) % p != 0


def criterion_obstruction_primes(n: int, i: int, j: int) -> list[int]:
    if not (1 <= i < j <= n // 2):
        return []
    return [
        p
        for p in primes_upto(n)
        if p >= i and not (dominated(i, n, p) or dominated(j, n, p))
    ]


def counterexample_candidate(n: int, i: int, j: int) -> bool:
    if not (1 <= i < j <= n // 2):
        return False
    return criterion_obstruction_primes(n, i, j) == []
```

- [ ] **Step 2: Run the focused Python tests**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
```

Expected: PASS.

### Task 4: Add Progress Log With Honest Rigor Tags

**Files:**
- Create: `notes/PROGRESS.md`

- [ ] **Step 1: Create the log**

Create `notes/PROGRESS.md`:

```markdown
# Erdős #699 Progress

## 2026-07-05

- [E] Added exact Python tests for the corrected counterexample criterion. Reproduce with:
  `python3 -m pytest compute/tests/test_criterion.py -q`.
- [R] Added Lean definitions `Erdos699.digit`, `Erdos699.dominated`, `Erdos699.relevantPrime`, and theorem
  `Erdos699.relevantPrime_ignores_small`. Reproduce with:
  `lake build Erdos699`.
- [OPEN] Lucas bridge, T1, T2, T3, and all later rungs remain unclaimed in this branch.
```

### Task 5: Verify and Commit the Milestone

**Files:**
- All files changed above.

- [ ] **Step 1: Run focused verification**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
lake build Erdos699
git diff --check
```

Expected: all pass.

- [ ] **Step 2: Commit**

Run:

```bash
git add lakefile.toml scripts/check_axioms.sh lean compute notes docs/superpowers/plans/2026-07-05-erdos699-foundation.md
git commit -m "feat: scaffold erdos699 proof campaign"
```

Expected: one milestone commit on `erdos699/full-solve`.
