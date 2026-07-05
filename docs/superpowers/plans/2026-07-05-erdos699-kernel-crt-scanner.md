# Erdős 699 Kernel CRT Scanner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an exact, reproducible CRT scanner for the consecutive-divisor kernel `N1 | t(t-1)` and `N2 | t(t-1)(t-2)`.

**Architecture:** Factor `N1` exactly by trial division into prime powers, enumerate the `{0,1}` residue choices for each prime power by CRT, generate bounded representatives, then filter by the `N2` row. Tests compare the CRT enumerator against brute force on small kernels and verify JSON CLI output.

**Tech Stack:** Python 3 exact integer arithmetic, pytest, existing `compute/` package.

---

### Task 1: Add Red Tests

**Files:**
- Create: `compute/tests/test_kernel.py`

- [x] **Step 1: Add unit tests for factorization, CRT, and brute-force equivalence**

```python
import json
import subprocess
import sys

from compute.kernel import (
    consecutive_kernel_holds,
    kernel_survivors_bruteforce,
    prime_power_factorization,
    scan_kernel_crt,
)


def test_prime_power_factorization_exact() -> None:
    assert prime_power_factorization(1) == []
    assert prime_power_factorization(72) == [(2, 8), (3, 9)]
    assert prime_power_factorization(325) == [(5, 25), (13, 13)]


def test_kernel_predicate_uses_both_rows_and_bound() -> None:
    assert consecutive_kernel_holds(6, 5, 10, 6)
    assert not consecutive_kernel_holds(6, 5, 10, 5)
    assert not consecutive_kernel_holds(6, 5, 9, 6)


def test_crt_scan_matches_bruteforce_for_small_kernels() -> None:
    for n1, n2, bound in [(6, 5, 40), (10, 9, 80), (15, 14, 120), (21, 10, 150)]:
        crt = scan_kernel_crt(n1, n2, bound)
        brute = kernel_survivors_bruteforce(n1, n2, bound)
        assert crt["survivors"] == brute
        assert crt["survivor_count"] == len(brute)
        assert crt["row_one_class_count"] <= 2 ** len(prime_power_factorization(n1))


def test_crt_scan_reports_row_one_classes_before_filtering() -> None:
    result = scan_kernel_crt(15, 14, 120)
    assert result["mode"] == "kernel_crt"
    assert result["n1"] == 15
    assert result["n2"] == 14
    assert result["bound"] == 120
    assert result["row_one_class_count"] == 4
    assert result["row_one_candidate_count"] >= result["survivor_count"]
    assert result["survivors"] == kernel_survivors_bruteforce(15, 14, 120)


def test_kernel_cli_emits_json() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--n1",
            "15",
            "--n2",
            "14",
            "--bound",
            "120",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "kernel_crt"
    assert payload["survivors"] == kernel_survivors_bruteforce(15, 14, 120)
```

- [x] **Step 2: Run and verify RED**

Run: `python3 -m pytest compute/tests/test_kernel.py -q`

Expected: FAIL with `ModuleNotFoundError: No module named 'compute.kernel'`.

### Task 2: Implement Exact Kernel Scanner

**Files:**
- Create: `compute/kernel.py`

- [x] **Step 1: Add exact factorization and CRT helpers**

```python
from __future__ import annotations

import argparse
import json
import math
from typing import Any


def prime_power_factorization(n: int) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("n must be positive")
    factors: list[tuple[int, int]] = []
    remaining = n
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            power = 1
            while remaining % p == 0:
                power *= p
                remaining //= p
            factors.append((p, power))
        p = 3 if p == 2 else p + 2
    if remaining > 1:
        factors.append((remaining, remaining))
    return factors


def _crt_pair_coprime(residue: int, modulus: int, target: int, factor: int) -> int:
    step = ((target - residue) % factor) * pow(modulus, -1, factor) % factor
    return residue + modulus * step
```

- [x] **Step 2: Add kernel predicate and brute-force reference**

```python
def consecutive_kernel_holds(n1: int, n2: int, bound: int, t: int) -> bool:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or t < 0:
        raise ValueError("bound and t must be nonnegative")
    return (
        2 * t <= bound
        and (t * (t - 1)) % n1 == 0
        and (t * (t - 1) * (t - 2)) % n2 == 0
    )


def kernel_survivors_bruteforce(n1: int, n2: int, bound: int) -> list[int]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return [
        t
        for t in range(bound // 2 + 1)
        if consecutive_kernel_holds(n1, n2, bound, t)
    ]
```

- [x] **Step 3: Add CRT scan**

```python
def _row_one_residue_classes(n1: int) -> tuple[list[int], int]:
    classes = [0]
    modulus = 1
    for _p, prime_power in prime_power_factorization(n1):
        next_classes: list[int] = []
        for residue in classes:
            next_classes.append(_crt_pair_coprime(residue, modulus, 0, prime_power))
            next_classes.append(_crt_pair_coprime(residue, modulus, 1, prime_power))
        modulus *= prime_power
        classes = sorted(set(value % modulus for value in next_classes))
    return classes, modulus


def scan_kernel_crt(n1: int, n2: int, bound: int) -> dict[str, Any]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    classes, modulus = _row_one_residue_classes(n1)
    row_one_candidates: list[int] = []
    survivors: list[int] = []
    limit = bound // 2
    for residue in classes:
        t = residue
        while t <= limit:
            if (t * (t - 1)) % n1 == 0:
                row_one_candidates.append(t)
                if (t * (t - 1) * (t - 2)) % n2 == 0:
                    survivors.append(t)
            t += modulus
    row_one_candidates = sorted(set(row_one_candidates))
    survivors = sorted(set(survivors))
    return {
        "mode": "kernel_crt",
        "algorithm": "row_one_prime_power_crt",
        "n1": n1,
        "n2": n2,
        "bound": bound,
        "row_one_modulus": modulus,
        "row_one_class_count": len(classes),
        "row_one_candidate_count": len(row_one_candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }
```

- [x] **Step 4: Add JSON CLI**

```python
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact CRT scanner for the Erdős #699 consecutive-divisor kernel."
    )
    parser.add_argument("--n1", type=int, required=True)
    parser.add_argument("--n2", type=int, required=True)
    parser.add_argument("--bound", type=int, required=True)
    args = parser.parse_args(argv)
    print(json.dumps(scan_kernel_crt(args.n1, args.n2, args.bound), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
```

- [x] **Step 5: Run focused tests**

Run: `python3 -m pytest compute/tests/test_kernel.py -q`

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[E]` entry naming `compute.kernel.scan_kernel_crt`, the brute-force cross-check tests, and a one-command reproduction example:

```bash
python3 -m compute.kernel --n1 15 --n2 14 --bound 120
```

State that this is an exact C2 kernel enumerator, not a proof of kernel emptiness.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
python3 -m pytest compute/tests/test_kernel.py -q
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py compute/tests/test_kernel.py -q
python3 -m compute.kernel --n1 15 --n2 14 --bound 120
lake env lean lean/Erdos699/Proved/Basic.lean
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
```

Commit:

```bash
git add compute/kernel.py compute/tests/test_kernel.py notes/PROGRESS.md \
  docs/superpowers/plans/2026-07-05-erdos699-kernel-crt-scanner.md
git commit -m "feat: add erdos699 kernel crt scanner"
```
