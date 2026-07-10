# Erdős 699 Bitset Scanner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the exact full-sweep scanner's default triple check with a faster bitset-domination algorithm while keeping the short-circuit scanner as a reference implementation.

**Architecture:** For each `n`, precompute integer masks of primes that fail Lucas domination for each `k <= n / 2`. A triple `(n,i,j)` is a candidate exactly when no prime bit with `p >= i` appears in both failure masks. Tests compare the bitset scanner with the existing short-circuit scanner over small full sweeps and restricted `i` sweeps.

**Tech Stack:** Python 3, pytest, exact integer arithmetic and bit operations only.

---

### Task 1: Add Red Bitset Tests

**Files:**
- Modify: `compute/tests/test_scan.py`

- [x] **Step 1: Add reference import and default algorithm assertion**

```python
from compute.scan import scan_full, scan_full_short_circuit


def test_scan_full_uses_bitset_algorithm_metadata() -> None:
    result = scan_full(20)
    assert result["algorithm"] == "bitset_domination"
```

- [x] **Step 2: Add equivalence tests**

```python
def test_bitset_scan_matches_short_circuit_scan() -> None:
    bitset = scan_full(75)
    reference = scan_full_short_circuit(75)
    assert bitset["checked_triples"] == reference["checked_triples"]
    assert bitset["candidates"] == reference["candidates"]


def test_bitset_scan_matches_short_circuit_scan_with_i_filter() -> None:
    bitset = scan_full(120, i_values=[3, 4, 5])
    reference = scan_full_short_circuit(120, i_values=[3, 4, 5])
    assert bitset["checked_triples"] == reference["checked_triples"]
    assert bitset["candidates"] == reference["candidates"]
```

- [x] **Step 3: Run tests and verify RED**

Run: `python3 -m pytest compute/tests/test_scan.py -q`

Expected: FAIL because `scan_full_short_circuit` is missing and the default
algorithm is still `short_circuit_obstruction`.

### Task 2: Implement Bitset Scanner

**Files:**
- Modify: `compute/scan.py`

- [x] **Step 1: Rename current scanner**

Move the current implementation body to:

```python
def scan_full_short_circuit(limit: int, i_values: Iterable[int] | None = None) -> dict[str, Any]:
```

Keep its payload stable with `"algorithm": "short_circuit_obstruction"`.

- [x] **Step 2: Add bitset helpers**

Add:
- `_prime_masks_by_threshold(primes_for_n: list[int], half: int) -> list[int]`
- `_failure_masks_for_n(n: int, half: int, primes_for_n: list[int]) -> list[int]`

Both helpers use only exact integer bit operations.

- [x] **Step 3: Reimplement `scan_full` using bitsets**

Use bitsets by default and return `"algorithm": "bitset_domination"`. Preserve
the rest of the JSON schema.

- [x] **Step 4: Run focused tests**

Run: `python3 -m pytest compute/tests/test_scan.py compute/tests/test_criterion.py -q`

Expected: PASS.

### Task 3: Reproduce Larger Exact Scan and Document

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Run a larger exact scan**

Run the largest bound that completes locally within the turn:
`python3 -m compute.scan --limit 2000`.

- [x] **Step 2: Update [E] progress entry**

Replace the previous `n <= 800` entry only if the larger command completes with
`candidate_count = 0`.

- [x] **Step 3: Run final verification and commit**

Run:
- `python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q`
- `python3 -m compute.scan --limit 2000`
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`

Commit:

```bash
git add compute/scan.py compute/tests/test_scan.py notes/PROGRESS.md \
  docs/superpowers/plans/2026-07-05-erdos699-bitset-scanner.md
git commit -m "feat: add erdos699 bitset exact scanner"
```
