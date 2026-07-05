# Erdős 699 Fixed-Row Scanner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a row-specialized exact scanner so historical fixed-row perimeters such as `i = 3` and `i = 4` can be reproduced by one command.

**Architecture:** Keep the existing full bitset scanner as the default for all-row sweeps. Add `scan_rows`, which fixes one or more row indices and, for each `n`, precomputes only the primes `p >= i` for which `i` is not dominated by `n`; a candidate row entry is then exactly a `j` dominated by all those obstruction primes. The implementation uses exact integer arithmetic and the same corrected `p >= i` criterion as the full scanner.

**Tech Stack:** Python 3, pytest, exact integer arithmetic, existing `compute.erdos699` digit-domination predicates.

---

### Task 1: Add Red Row-Scanner Tests

**Files:**
- Modify: `compute/tests/test_scan.py`

- [x] **Step 1: Import the planned row scanner**

```python
from compute.scan import scan_full, scan_full_short_circuit, scan_rows
```

- [x] **Step 2: Add exact equivalence tests**

```python
def test_row_scan_matches_full_scan_for_single_row() -> None:
    rows = scan_rows(90, [3])
    full = scan_full(90, i_values=[3])
    assert rows["mode"] == "rows"
    assert rows["algorithm"] == "row_obstruction_primes"
    assert rows["checked_triples"] == full["checked_triples"]
    assert rows["candidates"] == full["candidates"]


def test_row_scan_matches_full_scan_for_multiple_rows() -> None:
    rows = scan_rows(110, [3, 4, 5])
    full = scan_full(110, i_values=[3, 4, 5])
    assert rows["checked_triples"] == full["checked_triples"]
    assert rows["candidates"] == full["candidates"]
```

- [x] **Step 3: Add a CLI smoke test for the row strategy**

```python
def test_scan_cli_can_use_row_strategy() -> None:
    completed = subprocess.run(
        [sys.executable, "-m", "compute.scan", "--limit", "80", "--i", "3", "--row-scan"],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "rows"
    assert payload["algorithm"] == "row_obstruction_primes"
    assert payload["i_values"] == [3]
    assert payload["candidates"] == []
```

- [x] **Step 4: Run tests and verify RED**

Run: `python3 -m pytest compute/tests/test_scan.py -q`

Expected: FAIL because `scan_rows` and `--row-scan` do not exist yet.

### Task 2: Implement Exact Row Scanner

**Files:**
- Modify: `compute/scan.py`

- [x] **Step 1: Add row-obstruction and interval helpers**

```python
def _row_obstruction_primes(n: int, i: int, primes_for_n: list[int]) -> list[int]:
    return [p for p in primes_for_n if i <= p and not dominated(i, n, p)]


def _base_p_digits_through(n: int, p: int) -> list[int]:
    digits: list[int] = []
    place = 1
    while place <= n:
        digits.append((n // place) % p)
        place *= p
    return digits


def _merge_intervals(intervals: list[tuple[int, int]]) -> list[tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for start, stop in intervals[1:]:
        prev_start, prev_stop = merged[-1]
        if start <= prev_stop + 1:
            merged[-1] = (prev_start, max(prev_stop, stop))
        else:
            merged.append((start, stop))
    return merged


def _dominated_intervals(n: int, p: int, limit: int) -> list[tuple[int, int]]:
    digits = _base_p_digits_through(n, p)
    powers = [1]
    for _ in range(1, len(digits)):
        powers.append(powers[-1] * p)

    lower_unconstrained = [True]
    for digit_value in digits:
        lower_unconstrained.append(lower_unconstrained[-1] and digit_value == p - 1)

    intervals: list[tuple[int, int]] = []

    def visit(level: int, prefix: int) -> None:
        if level < 0:
            if prefix <= limit:
                intervals.append((prefix, prefix))
            return
        place = powers[level]
        for digit_value in range(digits[level] + 1):
            start = prefix + digit_value * place
            if limit < start:
                break
            if lower_unconstrained[level]:
                intervals.append((start, min(start + place - 1, limit)))
            else:
                visit(level - 1, start)

    visit(len(digits) - 1, 0)
    return _merge_intervals(intervals)


def _intersect_intervals(
    left: list[tuple[int, int]], right: list[tuple[int, int]]
) -> list[tuple[int, int]]:
    intersections: list[tuple[int, int]] = []
    i = 0
    j = 0
    while i < len(left) and j < len(right):
        left_start, left_stop = left[i]
        right_start, right_stop = right[j]
        start = max(left_start, right_start)
        stop = min(left_stop, right_stop)
        if start <= stop:
            intersections.append((start, stop))
        if left_stop < right_stop:
            i += 1
        else:
            j += 1
    return intersections
```

The interval helpers enumerate exactly the integers `k <= limit` satisfying
`k ⪯_p n`, merging adjacent digit blocks and intersecting the allowed ranges
across obstruction primes.

- [x] **Step 2: Add `scan_rows`**

```python
def scan_rows(limit: int, i_values: Iterable[int]) -> dict[str, Any]:
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    selected_i = _sorted_i_values(i_values)
    if selected_i is None or not selected_i:
        raise ValueError("row scan requires at least one i value")
    primes = primes_upto(limit)
    candidates: list[dict[str, int]] = []
    checked_triples = 0

    for n in range(1, limit + 1):
        half = n // 2
        primes_for_n = primes[: bisect_right(primes, n)]
        for i in selected_i:
            if half <= i:
                continue
            checked_triples += half - i
            allowed_intervals = [(i + 1, half)]
            for p in _row_obstruction_primes(n, i, primes_for_n):
                allowed_intervals = _intersect_intervals(
                    allowed_intervals, _dominated_intervals(n, p, half)
                )
                if not allowed_intervals:
                    break
            for start, stop in allowed_intervals:
                for j in range(start, stop + 1):
                    candidates.append({"n": n, "i": i, "j": j})

    return {
        "mode": "rows",
        "algorithm": "row_obstruction_primes",
        "limit": limit,
        "i_values": selected_i,
        "checked_triples": checked_triples,
        "candidate_count": len(candidates),
        "candidates": candidates,
    }
```

- [x] **Step 3: Add CLI flag**

Add `--row-scan`, require at least one `--i` when it is used, and dispatch to
`scan_rows`; otherwise keep the existing `scan_full` default.

- [x] **Step 4: Run focused tests**

Run: `python3 -m pytest compute/tests/test_scan.py compute/tests/test_criterion.py -q`

Expected: PASS.

### Task 3: Reproduce Fixed-Row Perimeters and Document

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Run row perimeters**

Run:

```bash
python3 -m compute.scan --limit 40000 --i 3 --row-scan
python3 -m compute.scan --limit 30000 --i 4 --row-scan
```

Expected: both commands return `candidate_count = 0`.

- [x] **Step 2: Update progress log**

Add an `[E]` entry with the exact reproduction commands, candidate counts,
and checked-triple counts. Do not upgrade the historical all-row `n <= 8000`
perimeter unless it is also reproduced.

- [x] **Step 3: Run final verification and commit**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q
python3 -m compute.scan --limit 40000 --i 3 --row-scan
python3 -m compute.scan --limit 30000 --i 4 --row-scan
lake env lean lean/Erdos699/Proved/Basic.lean
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build Erdos699.Proved.Basic
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
```

Commit:

```bash
git add compute/scan.py compute/tests/test_scan.py notes/PROGRESS.md \
  docs/superpowers/plans/2026-07-05-erdos699-fixed-row-scanner.md
git commit -m "feat: add erdos699 fixed-row exact scanner"
```
