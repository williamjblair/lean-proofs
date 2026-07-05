# Erdős 699 Kernel Pollard-Rho Factorization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace trial-division-only kernel factorization with deterministic Miller-Rabin plus Pollard-Rho so the exact Case-I kernel family scan can reach exponent 60 locally.

**Architecture:** Keep `prime_power_factorization` as the public API. Add deterministic 64-bit primality testing, a deterministic Pollard-Rho factor finder, recursive factor collection, and tests that verify product reconstruction and the `n = 3 * 2^60` scan path.

**Tech Stack:** Python 3 exact integer arithmetic, `math.gcd`, pytest, existing `compute/kernel.py`.

---

### Task 1: Add Red Tests

**Files:**
- Modify: `compute/tests/test_kernel.py`

- [x] **Step 1: Add product helper and large factorization tests**

Add after imports:

```python
def _factorization_product(factors: list[tuple[int, int]]) -> int:
    product = 1
    for _prime, prime_power in factors:
        product *= prime_power
    return product
```

Add after `test_prime_power_factorization_exact`:

```python
def test_prime_power_factorization_handles_large_semiprime() -> None:
    n = 1_000_000_007 * 1_000_000_009
    factors = prime_power_factorization(n)
    assert factors == [(1_000_000_007, 1_000_000_007), (1_000_000_009, 1_000_000_009)]
    assert _factorization_product(factors) == n


def test_prime_power_factorization_reconstructs_case_i_exponent_sixty_inputs() -> None:
    for n in [3 * (2**60) - 1, 3 * (2**59) - 1]:
        factors = prime_power_factorization(n)
        assert _factorization_product(factors) == n
        assert all(prime_power % prime == 0 for prime, prime_power in factors)
```

Add after `test_kernel_cli_can_scan_case_i_power_two_family`:

```python
def test_case_i_power_two_family_scan_reaches_exponent_sixty() -> None:
    result = scan_case_i_power_two_kernel(60, min_exponent=60)
    assert result["mode"] == "case_i_power_two_kernel"
    assert result["min_exponent"] == 60
    assert result["max_exponent"] == 60
    assert result["instance_count"] == 1
    assert result["instances"][0]["exponent"] == 60
    assert result["instances"][0]["n"] == 3 * (2**60)
```

- [x] **Step 2: Run and verify RED**

Run: `python3 -m pytest compute/tests/test_kernel.py -q`

Expected: FAIL or hang under the current trial-division factorizer on the large semiprime/exponent-60 tests. If it hangs, stop it after 10 seconds and record that trial division is the root cause.

### Task 2: Implement Deterministic 64-bit Factoring

**Files:**
- Modify: `compute/kernel.py`

- [x] **Step 1: Import `math`**

```python
import math
```

- [x] **Step 2: Add deterministic Miller-Rabin**

Add before `prime_power_factorization`:

```python
_MR_BASES_64 = (2, 3, 5, 7, 11, 13, 17, 325, 9375, 28178, 450775, 9780504, 1795265022)


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    for base in _MR_BASES_64:
        a = base % n
        if a == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True
```

- [x] **Step 3: Add deterministic Pollard-Rho splitting and recursive collection**

```python
def _pollard_rho_factor(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    c = 1
    while True:
        x = 2
        y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
        c += 1


def _collect_prime_factors(n: int, factors: list[int]) -> None:
    if n == 1:
        return
    if _is_prime(n):
        factors.append(n)
        return
    factor = _pollard_rho_factor(n)
    _collect_prime_factors(factor, factors)
    _collect_prime_factors(n // factor, factors)
```

- [x] **Step 4: Replace `prime_power_factorization` internals**

```python
def prime_power_factorization(n: int) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("n must be positive")
    prime_factors: list[int] = []
    _collect_prime_factors(n, prime_factors)
    prime_factors.sort()
    factors: list[tuple[int, int]] = []
    i = 0
    while i < len(prime_factors):
        p = prime_factors[i]
        power = 1
        while i < len(prime_factors) and prime_factors[i] == p:
            power *= p
            i += 1
        factors.append((p, power))
    return factors
```

- [x] **Step 5: Run focused tests**

Run: `python3 -m pytest compute/tests/test_kernel.py -q`

Expected: PASS within a few seconds.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[E]` entry naming deterministic Miller-Rabin/Pollard-Rho factorization and the exponent-60 scan command:

```bash
python3 -m compute.kernel --case-i-power-two --min-exponent 60 --max-exponent 60
```

Record the resulting row-one candidate and survivor counts from the command output. State that this is exact finite evidence, not a proof of kernel emptiness.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
python3 -m pytest compute/tests/test_kernel.py -q
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py compute/tests/test_kernel.py -q
python3 -m compute.kernel --case-i-power-two --min-exponent 60 --max-exponent 60
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
  docs/superpowers/plans/2026-07-05-erdos699-kernel-pollard-rho.md
git commit -m "feat: add erdos699 kernel pollard rho factoring"
```
