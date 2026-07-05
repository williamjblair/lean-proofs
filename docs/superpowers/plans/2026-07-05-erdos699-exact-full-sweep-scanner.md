# Erdős 699 Exact Full-Sweep Scanner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a reusable exact Python scanner for full `n <= limit`, all valid `i, j` Lucas-criterion sweeps, with deterministic JSON output.

**Architecture:** Keep the corrected Lucas obstruction predicate in `compute/erdos699.py` as the single source of truth. Add `compute/scan.py` for scan orchestration and CLI output; tests validate the scanner on small full sweeps and lock the CLI schema.

**Tech Stack:** Python 3, pytest, exact integer arithmetic only.

---

### Task 1: Add Red Scanner Tests

**Files:**
- Create: `compute/tests/test_scan.py`

- [x] **Step 1: Write failing tests**

```python
import json
import subprocess
import sys

from compute.scan import scan_full


def test_scan_full_small_bound_has_no_candidates() -> None:
    result = scan_full(40)
    assert result["mode"] == "full"
    assert result["limit"] == 40
    assert result["checked_triples"] == sum(
        max(0, n // 2 - i) for n in range(1, 41) for i in range(1, n // 2)
    )
    assert result["candidates"] == []


def test_scan_full_can_restrict_i_values() -> None:
    result = scan_full(60, i_values=[3, 4])
    assert result["mode"] == "full"
    assert result["i_values"] == [3, 4]
    assert result["candidates"] == []


def test_scan_cli_emits_json() -> None:
    completed = subprocess.run(
        [sys.executable, "-m", "compute.scan", "--limit", "35"],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "full"
    assert payload["limit"] == 35
    assert payload["candidates"] == []
```

- [x] **Step 2: Run tests and verify RED**

Run: `python3 -m pytest compute/tests/test_scan.py -q`

Expected: FAIL with `ModuleNotFoundError: No module named 'compute.scan'`.

### Task 2: Implement Scanner and CLI

**Files:**
- Modify: `compute/erdos699.py`
- Create: `compute/scan.py`

- [x] **Step 1: Allow shared prime lists in the criterion**

Extend `criterion_obstruction_primes` and `counterexample_candidate` with an
optional `primes` argument. Preserve existing behavior when omitted.

- [x] **Step 2: Add `scan_full`**

`scan_full(limit: int, i_values: Iterable[int] | None = None) -> dict[str, object]`
must:
- reject negative limits
- precompute primes once with `primes_upto(limit)`
- check exactly all triples `1 <= i < j <= n // 2`, optionally restricted to `i_values`
- return a plain JSON-serializable dictionary with mode, limit, checked triple count, candidates, and sorted `i_values`

- [x] **Step 3: Add CLI**

Support:
- `python3 -m compute.scan --limit 100`
- optional repeated `--i 3 --i 4`

The CLI prints sorted-key indented JSON to stdout and returns nonzero on invalid arguments through `argparse`.

- [x] **Step 4: Run tests**

Run:
- `python3 -m pytest compute/tests/test_scan.py -q`
- `python3 -m pytest compute/tests/test_criterion.py -q`

### Task 3: Reproduce a Bounded Exact Scan and Document

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Run a bounded exact scan**

Run: `python3 -m compute.scan --limit 300`

Expected: JSON with `"candidates": []`.

- [x] **Step 2: Add [E] progress entry**

Record the exact command and limit. Do not claim the historical `n <= 8000`
perimeter unless that larger command is run in this branch.

- [x] **Step 3: Run verification and commit**

Run:
- `python3 -m pytest compute/tests/test_scan.py compute/tests/test_criterion.py -q`
- `python3 -m compute.scan --limit 300`
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`

Commit:

```bash
git add compute/erdos699.py compute/scan.py compute/tests/test_scan.py \
  notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-exact-full-sweep-scanner.md
git commit -m "feat: add erdos699 exact full sweep scanner"
```
