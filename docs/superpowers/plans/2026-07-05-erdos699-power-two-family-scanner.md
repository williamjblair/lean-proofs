# Erdős 699 Power-Two Family Scanner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an exact sparse-family scanner that reproduces the package perimeter for `n = 2^A * M`, `M in {1,3,5,7,9,11,13,15,21,25}`, `n <= 2^36`, and `i in {3,4,5}`.

**Architecture:** Keep all-row and fixed-row interval scanners unchanged. For sparse huge `n`, obtain the relevant row-obstruction primes by factoring only `n-r` for `0 <= r < i`, because for `p > i`, `i ⪯_p n` fails exactly when `p | n-r` for one of those small residues. Enumerate candidate `j` values by applying largest-prime-first CRT constraints on the level-0 residues, then verify every survivor with the full Lucas digit-domination predicate.

**Tech Stack:** Python 3, pytest, exact integer arithmetic, existing `compute.erdos699` predicates.

---

### Task 1: Add Red Sparse-Scanner Tests

**Files:**
- Modify: `compute/tests/test_scan.py`

- [x] **Step 1: Import planned APIs**

```python
from compute.scan import (
    DEFAULT_POWER_TWO_MULTIPLIERS,
    power_two_family_values,
    scan_full,
    scan_full_short_circuit,
    scan_n_values,
    scan_power_two_family,
    scan_rows,
)
```

- [x] **Step 2: Add small sparse-value equivalence test**

```python
def test_sparse_n_value_scan_matches_full_scan_on_small_values() -> None:
    n_values = [12, 18, 24, 30]
    sparse = scan_n_values(n_values, [3, 4])
    full = scan_full(max(n_values), i_values=[3, 4])
    n_value_set = set(n_values)
    expected_candidates = [
        candidate for candidate in full["candidates"] if candidate["n"] in n_value_set
    ]
    expected_checked = sum(
        max(0, n // 2 - i) for n in n_values for i in [3, 4] if i < n // 2
    )
    assert sparse["mode"] == "n_values"
    assert sparse["algorithm"] == "factor_crt_row_obstruction"
    assert sparse["checked_triples"] == expected_checked
    assert sparse["candidates"] == expected_candidates
```

- [x] **Step 3: Add family generator and scanner smoke tests**

```python
def test_power_two_family_values_are_bounded_and_sorted() -> None:
    values = power_two_family_values(8, [1, 3, 5])
    assert values == sorted(set(values))
    assert all(n <= 2**8 for n in values)
    assert {1, 3, 5, 8, 24, 40, 128}.issubset(set(values))


def test_power_two_family_scan_matches_sparse_scan_on_small_family() -> None:
    family = scan_power_two_family(8, [1, 3, 5], [3, 4])
    sparse = scan_n_values(power_two_family_values(8, [1, 3, 5]), [3, 4])
    assert family["mode"] == "power_two_family"
    assert family["algorithm"] == "factor_crt_row_obstruction"
    assert family["family_limit"] == 2**8
    assert family["checked_triples"] == sparse["checked_triples"]
    assert family["candidates"] == sparse["candidates"]
```

- [x] **Step 4: Add CLI smoke test**

```python
def test_scan_cli_can_use_power_two_family_strategy() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.scan",
            "--power-two-family",
            "--family-max-exponent",
            "8",
            "--multiplier",
            "1",
            "--multiplier",
            "3",
            "--i",
            "3",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "power_two_family"
    assert payload["family_limit"] == 2**8
    assert payload["multipliers"] == [1, 3]
    assert payload["i_values"] == [3]
    assert payload["candidates"] == []
```

- [x] **Step 5: Run tests and verify RED**

Run: `python3 -m pytest compute/tests/test_scan.py -q`

Expected: FAIL because `scan_n_values`, `scan_power_two_family`, and the family CLI do not exist yet.

### Task 2: Implement Factorization and CRT Sparse Scanner

**Files:**
- Modify: `compute/scan.py`

- [x] **Step 1: Add constants and family generator**

```python
DEFAULT_POWER_TWO_MULTIPLIERS = [1, 3, 5, 7, 9, 11, 13, 15, 21, 25]


def power_two_family_values(max_exponent: int, multipliers: Iterable[int]) -> list[int]:
    if max_exponent < 0:
        raise ValueError("max exponent must be nonnegative")
    selected_multipliers = sorted(set(multipliers))
    if any(m < 1 for m in selected_multipliers):
        raise ValueError("multipliers must be positive")
    limit = 2**max_exponent
    values: set[int] = set()
    for multiplier in selected_multipliers:
        value = multiplier
        while value <= limit:
            values.add(value)
            value *= 2
    return sorted(values)
```

- [x] **Step 2: Add exact factorization helpers**

```python
def _prime_factors_from_primes(n: int, primes: list[int]) -> list[int]:
    factors: list[int] = []
    remaining = n
    for p in primes:
        if remaining < p * p:
            break
        if remaining % p == 0:
            factors.append(p)
            while remaining % p == 0:
                remaining //= p
    if 1 < remaining:
        factors.append(remaining)
    return factors


def _is_prime_by_trial(n: int) -> bool:
    if n < 2:
        return False
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            return False
    return True
```

- [x] **Step 3: Add factorized row-obstruction source**

```python
def _row_obstruction_primes_by_factorization(
    n: int, i: int, factor_primes: list[int]
) -> list[int]:
    obstructions: set[int] = set()
    if _is_prime_by_trial(i) and i <= n and not dominated(i, n, i):
        obstructions.add(i)
    for r in range(i):
        for p in _prime_factors_from_primes(n - r, factor_primes):
            if i < p <= n and not dominated(i, n, p):
                obstructions.add(p)
    return sorted(obstructions)
```

- [x] **Step 4: Add CRT candidate enumeration and sparse scan**

```python
def _first_representative_greater_than(residue: int, modulus: int, lower: int) -> int:
    if lower < residue:
        return residue
    return residue + ((lower - residue) // modulus + 1) * modulus


def _crt_pair_coprime(residue: int, modulus: int, target: int, prime: int) -> int:
    step = ((target - residue) % prime) * pow(modulus, -1, prime) % prime
    return residue + modulus * step


def _candidate_js_by_factor_crt(n: int, i: int, obstruction_primes: list[int]) -> list[int]:
    half = n // 2
    states = [0]
    modulus = 1
    for p in sorted((p for p in obstruction_primes if i < p), reverse=True):
        next_modulus = modulus * p
        next_states: list[int] = []
        for residue in states:
            for target in range(n % p + 1):
                combined = _crt_pair_coprime(residue, modulus, target, p)
                if _first_representative_greater_than(combined, next_modulus, i) <= half:
                    next_states.append(combined)
        states = sorted(set(next_states))
        modulus = next_modulus
        if not states:
            break

    candidates: list[int] = []
    for residue in states:
        j = _first_representative_greater_than(residue, modulus, i)
        while j <= half:
            if all(dominated(j, n, p) for p in obstruction_primes):
                candidates.append(j)
            j += modulus
    return candidates
```

- [x] **Step 5: Add `scan_n_values` and `scan_power_two_family`**

Use the helpers to return JSON-compatible payloads with:
- `mode`
- `algorithm = "factor_crt_row_obstruction"`
- `n_values` or `max_exponent`/`family_limit`/`multipliers`
- `i_values`
- `cells_checked`
- `checked_triples`
- `candidate_count`
- `candidates`
- `max_crt_states`

- [x] **Step 6: Add CLI dispatch**

Add:
- `--power-two-family`
- `--family-max-exponent` defaulting to `36`
- repeatable `--multiplier`, defaulting to `DEFAULT_POWER_TWO_MULTIPLIERS`

Require at least one `--i` for the family mode.

### Task 3: Reproduce Family Perimeter and Document

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Run focused tests**

Run: `python3 -m pytest compute/tests/test_scan.py compute/tests/test_criterion.py -q`

Expected: PASS.

- [x] **Step 2: Run the structured-family perimeter**

Run:

```bash
python3 -m compute.scan --power-two-family --family-max-exponent 36 --i 3 --i 4 --i 5
```

Expected: `candidate_count = 0` for the default multiplier set.

- [x] **Step 3: Update progress log**

Add an `[E]` entry with the exact reproduction command, multiplier set,
`cells_checked`, `checked_triples`, `candidate_count`, and `max_crt_states`.

- [x] **Step 4: Run final verification and commit**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q
python3 -m compute.scan --power-two-family --family-max-exponent 36 --i 3 --i 4 --i 5
lake env lean lean/Erdos699/Proved/Basic.lean
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build Erdos699.Proved.Basic
lake build
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
```

Commit:

```bash
git add compute/scan.py compute/tests/test_scan.py notes/PROGRESS.md \
  docs/superpowers/plans/2026-07-05-erdos699-power-two-family-scanner.md
git commit -m "feat: add erdos699 power-two family scanner"
```
