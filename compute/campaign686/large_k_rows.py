#!/usr/bin/env python3
"""Exact row-divisibility diagnostics for Erdős 686 Target 2."""

from __future__ import annotations

from math import isqrt, prod


def factor(n: int) -> list[tuple[int, int]]:
    """Trial-division factorization, sufficient for the fixed audit fixtures."""
    if n <= 0:
        raise ValueError("factorization input must be positive")
    out: list[tuple[int, int]] = []
    exponent = 0
    while n % 2 == 0:
        n //= 2
        exponent += 1
    if exponent:
        out.append((2, exponent))
    p = 3
    while p <= isqrt(n):
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            out.append((p, exponent))
        p += 2
    if n > 1:
        out.append((n, 1))
    return out


def ratio_window_holds(k: int, n: int, d: int) -> bool:
    """The exact necessary N=4 ratio window used by the census."""
    return (n + d + k) ** k <= 4 * (n + k) ** k and (
        4 * (n + 1) ** k <= (n + d + 1) ** k
    )


def row_interval(k: int, d: int, row: int) -> tuple[int, int]:
    if not 1 <= row <= k:
        raise ValueError("row outside 1..k")
    return d + 1 - row, d + k - row


def row_product_mod(k: int, n: int, d: int, row: int) -> int:
    modulus = n + row
    value = 1 % modulus
    lo, hi = row_interval(k, d, row)
    for term in range(lo, hi + 1):
        value = value * (term % modulus) % modulus
    return value


def row_passes(k: int, n: int, d: int, row: int) -> bool:
    return row_product_mod(k, n, d, row) == 0


def first_failed_row(k: int, n: int, d: int, limit: int | None = None) -> int | None:
    last = k if limit is None else min(k, limit)
    for row in range(1, last + 1):
        if not row_passes(k, n, d, row):
            return row
    return None


def valuation_in_interval(prime: int, lo: int, hi: int) -> int:
    """Return v_p(product(lo..hi)) exactly."""
    if prime < 2 or lo <= 0 or hi < lo:
        raise ValueError("invalid interval valuation")
    total = 0
    power = prime
    while power <= hi:
        total += hi // power - (lo - 1) // power
        if power > hi // prime:
            break
        power *= prime
    return total


def allowed_positions(k: int, d: int, row: int, prime_power: int) -> list[int]:
    """Indices i in 1..k with prime_power | d+i-row."""
    return [
        i for i in range(1, k + 1) if (d + i - row) % prime_power == 0
    ]


def row_anatomy(k: int, n: int, d: int, row: int) -> dict[str, object]:
    lo, hi = row_interval(k, d, row)
    factors = factor(n + row)
    prime_data: list[dict[str, object]] = []
    for prime, exponent in factors:
        prime_power = prime**exponent
        prime_data.append(
            {
                "prime": prime,
                "exponent": exponent,
                "prime_power": prime_power,
                "block_valuation": valuation_in_interval(prime, lo, hi),
                "allowed_positions_for_full_power": allowed_positions(
                    k, d, row, prime_power
                ),
            }
        )
    return {
        "row": row,
        "modulus": n + row,
        "factorization": factors,
        "interval": (lo, hi),
        "passes": row_passes(k, n, d, row),
        "prime_data": prime_data,
    }


def block_equation_holds(k: int, n: int, d: int) -> bool:
    lower = prod(n + i for i in range(1, k + 1))
    upper = prod(n + d + i for i in range(1, k + 1))
    return upper == 4 * lower


def reflection_center(k: int, n: int, d: int) -> int:
    return 2 * n + d + k + 1


def reflection_coefficient(k: int) -> int:
    return 3 if k % 2 == 0 else 5


def reflection_product(k: int, d: int) -> int:
    return prod(d + k + 1 - 2 * i for i in range(1, k + 1))


def block_product(k: int, n: int) -> int:
    return prod(n + i for i in range(1, k + 1))


def greatest_prime_factor_of_block(k: int, n: int) -> int:
    return max(prime for i in range(1, k + 1) for prime, _ in factor(n + i))


def near_diagonal_power_check(k: int) -> bool:
    """Exact inequality used to force n>4d."""
    return 4 * 5**k < 6**k
