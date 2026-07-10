# Erdős 699 Case-I Power-Two Kernel Scan Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the exact kernel CRT scanner with problem-relevant lower bounds and a reproducible `n = 3 * 2^A` Case-I family mode.

**Architecture:** Add `min_t` filtering to the scalar kernel predicate, brute-force reference, CRT scan, and CLI. Then add `scan_case_i_power_two_kernel`, which maps each exponent `A` to `n = 3 * 2^A`, `N1 = n - 1`, `N2 = n / 2 - 1`, `bound = n`, and the default row-3 lower bound `t >= 4`.

**Tech Stack:** Python 3 exact integer arithmetic, pytest, existing `compute/kernel.py`.

---

### Task 1: Add Red Tests

**Files:**
- Modify: `compute/tests/test_kernel.py`

- [x] **Step 1: Add imports and tests for `min_t` and the family scan**

```python
from compute.kernel import (
    consecutive_kernel_holds,
    kernel_survivors_bruteforce,
    prime_power_factorization,
    scan_case_i_power_two_kernel,
    scan_kernel_crt,
)
```

Add after `test_crt_scan_reports_row_one_classes_before_filtering`:

```python
def test_crt_scan_can_apply_problem_lower_bound() -> None:
    result = scan_kernel_crt(15, 14, 120, min_t=4)
    assert result["min_t"] == 4
    assert result["row_one_candidate_count"] == 15
    assert result["survivor_count"] == 6
    assert result["survivors"] == [15, 16, 21, 30, 36, 51]
    assert result["survivors"] == kernel_survivors_bruteforce(15, 14, 120, min_t=4)
    assert not consecutive_kernel_holds(15, 14, 120, 1, min_t=4)
```

Add after the CLI scalar test:

```python
def test_case_i_power_two_family_scan_matches_scalar_scans() -> None:
    result = scan_case_i_power_two_kernel(5)
    assert result["mode"] == "case_i_power_two_kernel"
    assert result["min_exponent"] == 2
    assert result["max_exponent"] == 5
    assert result["min_t"] == 4
    assert result["instance_count"] == 4
    expected = []
    for exponent in range(2, 6):
        n = 3 * (2**exponent)
        scan = scan_kernel_crt(n - 1, n // 2 - 1, n, min_t=4)
        expected.append({"exponent": exponent, "n": n, **scan})
    assert result["instances"] == expected
    assert result["survivor_count"] == sum(item["survivor_count"] for item in expected)


def test_kernel_cli_can_scan_case_i_power_two_family() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--case-i-power-two",
            "--max-exponent",
            "5",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "case_i_power_two_kernel"
    assert payload["max_exponent"] == 5
    assert payload["instances"] == scan_case_i_power_two_kernel(5)["instances"]
```

- [x] **Step 2: Run and verify RED**

Run: `python3 -m pytest compute/tests/test_kernel.py -q`

Expected: FAIL because `scan_case_i_power_two_kernel` is missing and scalar functions do not accept `min_t`.

### Task 2: Implement `min_t` and Case-I Family Mode

**Files:**
- Modify: `compute/kernel.py`

- [x] **Step 1: Add lower-bound helper and extend the predicate/reference**

```python
def _first_representative_at_least(residue: int, modulus: int, lower: int) -> int:
    if residue >= lower:
        return residue
    return residue + ((lower - residue + modulus - 1) // modulus) * modulus
```

Change signatures and checks:

```python
def consecutive_kernel_holds(
    n1: int, n2: int, bound: int, t: int, min_t: int = 0
) -> bool:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or t < 0 or min_t < 0:
        raise ValueError("bound, t, and min_t must be nonnegative")
    return (
        min_t <= t
        and 2 * t <= bound
        and (t * (t - 1)) % n1 == 0
        and (t * (t - 1) * (t - 2)) % n2 == 0
    )


def kernel_survivors_bruteforce(
    n1: int, n2: int, bound: int, min_t: int = 0
) -> list[int]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or min_t < 0:
        raise ValueError("bound and min_t must be nonnegative")
    return [
        t
        for t in range(min_t, bound // 2 + 1)
        if consecutive_kernel_holds(n1, n2, bound, t, min_t=min_t)
    ]
```

- [x] **Step 2: Extend `scan_kernel_crt` with `min_t`**

Change the signature and validation:

```python
def scan_kernel_crt(n1: int, n2: int, bound: int, min_t: int = 0) -> dict[str, Any]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or min_t < 0:
        raise ValueError("bound and min_t must be nonnegative")
```

Use:

```python
        t = _first_representative_at_least(residue, modulus, min_t)
```

Add `"min_t": min_t` to the result payload.

- [x] **Step 3: Add the `n = 3 * 2^A` family scanner**

```python
def scan_case_i_power_two_kernel(
    max_exponent: int, min_exponent: int = 2, min_t: int = 4
) -> dict[str, Any]:
    if min_exponent < 0 or max_exponent < min_exponent:
        raise ValueError("require 0 <= min_exponent <= max_exponent")
    if min_t < 0:
        raise ValueError("min_t must be nonnegative")
    instances: list[dict[str, Any]] = []
    for exponent in range(min_exponent, max_exponent + 1):
        n = 3 * (2**exponent)
        scan = scan_kernel_crt(n - 1, n // 2 - 1, n, min_t=min_t)
        instances.append({"exponent": exponent, "n": n, **scan})
    return {
        "mode": "case_i_power_two_kernel",
        "algorithm": "case_i_power_two_kernel_crt",
        "min_exponent": min_exponent,
        "max_exponent": max_exponent,
        "min_t": min_t,
        "instance_count": len(instances),
        "total_row_one_candidate_count": sum(
            item["row_one_candidate_count"] for item in instances
        ),
        "survivor_count": sum(item["survivor_count"] for item in instances),
        "instances": instances,
    }
```

- [x] **Step 4: Extend the CLI**

Replace required scalar arguments with optional arguments and add family flags:

```python
    parser.add_argument("--n1", type=int)
    parser.add_argument("--n2", type=int)
    parser.add_argument("--bound", type=int)
    parser.add_argument("--min-t", type=int)
    parser.add_argument("--case-i-power-two", action="store_true")
    parser.add_argument("--min-exponent", type=int, default=2)
    parser.add_argument("--max-exponent", type=int)
```

Dispatch:

```python
    if args.case_i_power_two:
        if args.max_exponent is None:
            parser.error("--case-i-power-two requires --max-exponent")
        min_t = 4 if args.min_t is None else args.min_t
        result = scan_case_i_power_two_kernel(
            args.max_exponent, min_exponent=args.min_exponent, min_t=min_t
        )
    else:
        if args.n1 is None or args.n2 is None or args.bound is None:
            parser.error("scalar scan requires --n1, --n2, and --bound")
        min_t = 0 if args.min_t is None else args.min_t
        result = scan_kernel_crt(args.n1, args.n2, args.bound, min_t=min_t)
    print(json.dumps(result, sort_keys=True))
```

- [x] **Step 5: Run focused tests**

Run: `python3 -m pytest compute/tests/test_kernel.py -q`

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[E]` entry naming:
- `compute.kernel.scan_kernel_crt` with the `min_t` argument
- `compute.kernel.scan_case_i_power_two_kernel`

Include reproduction commands:

```bash
python3 -m compute.kernel --n1 15 --n2 14 --bound 120 --min-t 4
python3 -m compute.kernel --case-i-power-two --max-exponent 12
```

State that this is exact kernel-family enumeration, not a proof of emptiness.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
python3 -m pytest compute/tests/test_kernel.py -q
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py compute/tests/test_kernel.py -q
python3 -m compute.kernel --n1 15 --n2 14 --bound 120 --min-t 4
python3 -m compute.kernel --case-i-power-two --max-exponent 12
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
  docs/superpowers/plans/2026-07-05-erdos699-case-i-power-two-kernel-scan.md
git commit -m "feat: add erdos699 case-i kernel family scan"
```
