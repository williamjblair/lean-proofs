# Erdős 699 Short-Circuit Scanner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the exact full-sweep scanner use a short-circuit obstruction predicate while preserving the corrected Lucas criterion.

**Architecture:** Add `has_obstruction_prime` beside `criterion_obstruction_primes` in `compute/erdos699.py`, prove equivalence by pytest over a bounded grid, and make `counterexample_candidate` plus `scan_full` use the boolean path. Keep JSON output stable.

**Tech Stack:** Python 3, pytest, exact integer arithmetic only.

---

### Task 1: Add Red Equivalence Tests

**Files:**
- Modify: `compute/tests/test_criterion.py`
- Modify: `compute/tests/test_scan.py`

- [x] **Step 1: Write failing criterion tests**

```python
from compute.erdos699 import has_obstruction_prime


def test_short_circuit_obstruction_matches_obstruction_list() -> None:
    for n in range(1, 90):
        primes = primes_upto(n)
        for i in range(1, n // 2):
            for j in range(i + 1, n // 2 + 1):
                obstructions = criterion_obstruction_primes(n, i, j, primes=primes)
                assert has_obstruction_prime(n, i, j, primes=primes) == bool(obstructions)
                assert counterexample_candidate(n, i, j, primes=primes) == (not obstructions)
```

- [x] **Step 2: Write scan metadata test**

```python
def test_scan_full_uses_short_circuit_algorithm_metadata() -> None:
    result = scan_full(20)
    assert result["algorithm"] == "short_circuit_obstruction"
```

- [x] **Step 3: Run tests and verify RED**

Run: `python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q`

Expected: FAIL because `has_obstruction_prime` and `algorithm` metadata do not exist.

### Task 2: Implement Short-Circuit Path

**Files:**
- Modify: `compute/erdos699.py`
- Modify: `compute/scan.py`

- [x] **Step 1: Add `has_obstruction_prime`**

The function must:
- reject invalid triples by returning `False`
- use `primes_upto(n)` when no shared prime list is passed
- scan candidate primes in descending order, filtered by `i <= p <= n`
- return as soon as it finds a prime with neither `i` nor `j` dominated

- [x] **Step 2: Wire `counterexample_candidate`**

Return `not has_obstruction_prime(...)`.

- [x] **Step 3: Wire `scan_full`**

Keep the same payload and add:

```python
"algorithm": "short_circuit_obstruction"
```

- [x] **Step 4: Run focused tests**

Run: `python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q`

Expected: PASS.

### Task 3: Reproduce Larger Bounded Scan and Document

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Run a larger exact scan**

Run a bound that completes locally after the short-circuit change, e.g.
`python3 -m compute.scan --limit 800`.

- [x] **Step 2: Update [E] progress entry**

Replace the previous `n <= 300` scanner entry only if the larger command
actually completes with `candidate_count = 0`.

- [x] **Step 3: Run final verification and commit**

Run:
- `python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q`
- `python3 -m compute.scan --limit 800`
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`

Commit:

```bash
git add compute/erdos699.py compute/scan.py compute/tests/test_criterion.py \
  compute/tests/test_scan.py notes/PROGRESS.md \
  docs/superpowers/plans/2026-07-05-erdos699-short-circuit-scanner.md
git commit -m "feat: speed erdos699 exact scanner"
```
