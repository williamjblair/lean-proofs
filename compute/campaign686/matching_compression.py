#!/usr/bin/env python3
"""Exact prime-power ownership compression for Erdos 686 row skeletons.

For every prime, select a maximum-valuation term of a consecutive lower
block.  Valuation outside that owner costs at most ``v_p((k-1)!)``.  If the
owner row divides its shifted-difference product, a second copy of the same
loss localizes the remaining owner power in one centered difference.

The resulting row-only paper lemma is

    B(k,n) | ((k-1)!)^2 * lcm(d-k+1, ..., d+k-1).

No floating point arithmetic is used here.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial, gcd, prod

from .large_k_rows import factor, row_passes


def valuation(value: int, prime: int) -> int:
    """Return the exact ``prime``-adic valuation of a positive integer."""
    if value <= 0 or prime < 2:
        raise ValueError("valuation expects a positive value and prime >= 2")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def factorial_valuation(bound: int, prime: int) -> int:
    """Return ``v_prime(bound!)`` by Legendre's formula."""
    if bound < 0 or prime < 2:
        raise ValueError("invalid factorial valuation input")
    total = 0
    quotient = bound
    while quotient:
        quotient //= prime
        total += quotient
    return total


def lcm(values: list[int]) -> int:
    result = 1
    for value in values:
        if value <= 0:
            raise ValueError("lcm inputs must be positive")
        result = result // gcd(result, value) * value
    return result


def centered_values(k: int, d: int) -> list[int]:
    if k < 1 or d < k:
        raise ValueError("expected 1 <= k <= d")
    return list(range(d - k + 1, d + k))


def centered_lcm(k: int, d: int) -> int:
    return lcm(centered_values(k, d))


def centered_product(k: int, d: int) -> int:
    return prod(centered_values(k, d))


def consecutive_factorial_lcm_absorption(start: int, length: int) -> bool:
    """Check ``floor(length/2)! * lcm(block) | product(block)`` exactly."""
    if start <= 0 or length < 1:
        raise ValueError("expected a positive nonempty consecutive block")
    values = list(range(start, start + length))
    return prod(values) % (factorial(length // 2) * lcm(values)) == 0


def block_product(k: int, n: int) -> int:
    if k < 1 or n < 0:
        raise ValueError("invalid block")
    return prod(n + index for index in range(1, k + 1))


@dataclass(frozen=True)
class OwnerChunk:
    prime: int
    block_exponent: int
    owner_exponent: int
    loss_exponent: int
    chunk_exponent: int
    chunk: int
    owner_row: int
    landing_column: int | None
    landing_value: int | None


@dataclass(frozen=True)
class MatchedOwnerChunk:
    prime: int
    lower_block_exponent: int
    upper_block_exponent: int
    loss_exponent: int
    chunk_exponent: int
    chunk: int
    lower_owner_row: int
    upper_owner_row: int
    shifted_difference: int
    divides_lower_owner: bool
    divides_upper_owner: bool


def owner_chunks(k: int, n: int, d: int) -> list[OwnerChunk]:
    """Compute the exact two-stage owner chunk for every block prime.

    A nontrivial chunk is guaranteed a landing only when its selected owner
    row satisfies the row-divisibility condition.  The function deliberately
    reports ``None`` otherwise, making failed fixture rows auditable.
    """
    if k < 1 or d < k or n < 0:
        raise ValueError("expected n >= 0 and 1 <= k <= d")

    term_factorizations = [dict(factor(n + row)) for row in range(1, k + 1)]
    primes = sorted({prime for data in term_factorizations for prime in data})
    chunks: list[OwnerChunk] = []

    for prime in primes:
        exponents = [data.get(prime, 0) for data in term_factorizations]
        owner_exponent = max(exponents)
        owner_row = exponents.index(owner_exponent) + 1
        block_exponent = sum(exponents)
        loss_exponent = factorial_valuation(k - 1, prime)
        chunk_exponent = max(owner_exponent - loss_exponent, 0)
        chunk = prime**chunk_exponent

        landing_column: int | None = None
        landing_value: int | None = None
        if chunk_exponent > 0:
            candidates = [
                column
                for column in range(1, k + 1)
                if (d + column - owner_row) % chunk == 0
            ]
            if candidates:
                # Concentration only asserts existence.  Choosing the first
                # keeps the exact certificate deterministic.
                landing_column = candidates[0]
                landing_value = d + landing_column - owner_row

        chunks.append(
            OwnerChunk(
                prime=prime,
                block_exponent=block_exponent,
                owner_exponent=owner_exponent,
                loss_exponent=loss_exponent,
                chunk_exponent=chunk_exponent,
                chunk=chunk,
                owner_row=owner_row,
                landing_column=landing_column,
                landing_value=landing_value,
            )
        )

    return chunks


def compressed_owner_product(k: int, n: int, d: int) -> int:
    return prod(chunk.chunk for chunk in owner_chunks(k, n, d))


def matched_owner_chunks(k: int, n: int, d: int) -> list[MatchedOwnerChunk]:
    """Match maximum-valuation owners between the lower and upper blocks.

    If the upper block product is a multiple of the lower block product, then
    every returned chunk divides both selected owner terms.  For an exact
    N=4 equation this is the one-factorial compression formalized in Lean.
    """
    if k < 1 or n < 0 or d < 0:
        raise ValueError("invalid block")
    lower = [dict(factor(n + row)) for row in range(1, k + 1)]
    upper = [dict(factor(n + d + row)) for row in range(1, k + 1)]
    primes = sorted({prime for data in lower for prime in data})
    chunks: list[MatchedOwnerChunk] = []
    for prime in primes:
        lower_exponents = [data.get(prime, 0) for data in lower]
        upper_exponents = [data.get(prime, 0) for data in upper]
        lower_block_exponent = sum(lower_exponents)
        upper_block_exponent = sum(upper_exponents)
        lower_owner_row = lower_exponents.index(max(lower_exponents)) + 1
        upper_owner_row = upper_exponents.index(max(upper_exponents)) + 1
        loss_exponent = factorial_valuation(k - 1, prime)
        chunk_exponent = max(lower_block_exponent - loss_exponent, 0)
        chunk = prime**chunk_exponent
        lower_owner = n + lower_owner_row
        upper_owner = n + d + upper_owner_row
        chunks.append(
            MatchedOwnerChunk(
                prime=prime,
                lower_block_exponent=lower_block_exponent,
                upper_block_exponent=upper_block_exponent,
                loss_exponent=loss_exponent,
                chunk_exponent=chunk_exponent,
                chunk=chunk,
                lower_owner_row=lower_owner_row,
                upper_owner_row=upper_owner_row,
                shifted_difference=upper_owner - lower_owner,
                divides_lower_owner=lower_owner % chunk == 0,
                divides_upper_owner=upper_owner % chunk == 0,
            )
        )
    return chunks


def matched_owner_product(k: int, n: int, d: int) -> int:
    return prod(chunk.chunk for chunk in matched_owner_chunks(k, n, d))


def compression_rhs(k: int, d: int) -> int:
    return factorial(k - 1) ** 2 * centered_lcm(k, d)


def equation_compression_rhs(k: int, d: int) -> int:
    return factorial(k - 1) * centered_lcm(k, d)


def scaled_ratio_power_check(k: int) -> bool:
    """Exact Bernoulli comparison behind ``k*d < 5*n``."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return 4 * (k + 5) ** k < (k + 10) ** k


def all_rows_pass(k: int, n: int, d: int) -> bool:
    return all(row_passes(k, n, d, row) for row in range(1, k + 1))


def verify_compression_certificate(k: int, n: int, d: int) -> bool:
    """Replay the divisibility certificate when every row survives."""
    if not all_rows_pass(k, n, d):
        return False
    chunks = owner_chunks(k, n, d)
    if any(
        chunk.chunk_exponent > 0 and chunk.landing_column is None
        for chunk in chunks
    ):
        return False

    owner_product = prod(chunk.chunk for chunk in chunks)
    lower_product = block_product(k, n)
    loss = factorial(k - 1) ** 2
    return (
        lower_product % owner_product == 0
        and loss * owner_product % lower_product == 0
        and centered_lcm(k, d) % owner_product == 0
        and compression_rhs(k, d) % lower_product == 0
    )
