#!/usr/bin/env python3
"""Exact reflection-lcm and owner-correlation certificates for Erdos 686.

All calculations are integer calculations.  The verifier deliberately keeps
the residual exponent

    max(v_p(S) - v_p(c) - v_p((k-1)!), 0)

visible for every prime divisor of ``S=2*n+d+k+1``.  For an equation
solution, a maximum-valuation lower owner and a maximum-valuation upper owner
make the corresponding prime power divide both

    d+k+1-2*i  and  d+j-i.

Their difference is the signed owner offset ``i+j-(k+1)``.  Thus every
non-reflected residual owner is absorbed by ``lcm(1,...,k-1)``; reflected
owners are the exact obstruction.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial, prod

from .large_k_rows import factor
from .matching_compression import factorial_valuation, lcm, valuation


def reflection_coefficient(k: int) -> int:
    if k < 0:
        raise ValueError("k must be nonnegative")
    return 3 if k % 2 == 0 else 5


def reflection_center(k: int, n: int, d: int) -> int:
    if min(k, n, d) < 0:
        raise ValueError("expected natural inputs")
    return 2 * n + d + k + 1


def positive_reflection_values(k: int, d: int) -> list[int]:
    """Return ``d+k-1,d+k-3,...,d-k+1`` in owner-index order."""
    if k < 1 or d < k:
        raise ValueError("positive reflection lcm requires 1 <= k <= d")
    values = [d + k + 1 - 2 * i for i in range(1, k + 1)]
    assert all(value > 0 for value in values)
    return values


def reflection_lcm(k: int, d: int) -> int:
    return lcm(positive_reflection_values(k, d))


def reflection_product(k: int, d: int) -> int:
    return prod(positive_reflection_values(k, d))


def small_index_lcm(k: int) -> int:
    if k < 2:
        raise ValueError("small-index lcm requires k >= 2")
    return lcm(list(range(1, k)))


def block_terms(k: int, start: int) -> list[int]:
    if k < 1 or start < 0:
        raise ValueError("invalid positive block")
    return [start + i for i in range(1, k + 1)]


def block_valuation(k: int, start: int, prime: int) -> int:
    return sum(valuation(term, prime) for term in block_terms(k, start))


def first_max_owner(k: int, start: int, prime: int) -> tuple[int, int]:
    exponents = [valuation(term, prime) for term in block_terms(k, start)]
    exponent = max(exponents)
    return exponents.index(exponent) + 1, exponent


@dataclass(frozen=True)
class ReflectionOwnerCorrelation:
    prime: int
    center_exponent: int
    coefficient_exponent: int
    factorial_exponent: int
    residual_exponent: int
    residual_power: int
    lower_block_exponent: int
    upper_block_exponent: int
    lower_owner: int
    upper_owner: int
    lower_owner_exponent: int
    upper_owner_exponent: int
    reflection_difference: int
    centered_difference: int
    owner_offset: int

    @property
    def reflected(self) -> bool:
        return self.owner_offset == 0

    @property
    def lower_landing(self) -> bool:
        return self.lower_owner_exponent >= self.residual_exponent

    @property
    def upper_landing(self) -> bool:
        return self.upper_owner_exponent >= self.residual_exponent

    @property
    def reflection_landing(self) -> bool:
        return self.reflection_difference % self.residual_power == 0

    @property
    def centered_landing(self) -> bool:
        return self.centered_difference % self.residual_power == 0

    @property
    def offset_landing(self) -> bool:
        return self.owner_offset % self.residual_power == 0


def owner_correlations(k: int, n: int, d: int) -> list[ReflectionOwnerCorrelation]:
    """Return deterministic maximum-owner correlations for primes of ``S``.

    The divisibility conclusions are guaranteed only when the exact equation
    holds.  Returning the raw ledger for non-solutions is useful for hostile
    fixture checks: missing premises remain visible instead of being inferred.
    """
    if k < 1 or n < 0 or d < 0:
        raise ValueError("invalid inputs")
    center = reflection_center(k, n, d)
    coefficient = reflection_coefficient(k)
    rows: list[ReflectionOwnerCorrelation] = []
    for prime, center_exponent in factor(center):
        coefficient_exponent = valuation(coefficient, prime)
        loss = factorial_valuation(k - 1, prime)
        residual_exponent = max(
            center_exponent - coefficient_exponent - loss, 0
        )
        lower_owner, lower_owner_exponent = first_max_owner(k, n, prime)
        upper_owner, upper_owner_exponent = first_max_owner(k, n + d, prime)
        rows.append(
            ReflectionOwnerCorrelation(
                prime=prime,
                center_exponent=center_exponent,
                coefficient_exponent=coefficient_exponent,
                factorial_exponent=loss,
                residual_exponent=residual_exponent,
                residual_power=prime**residual_exponent,
                lower_block_exponent=block_valuation(k, n, prime),
                upper_block_exponent=block_valuation(k, n + d, prime),
                lower_owner=lower_owner,
                upper_owner=upper_owner,
                lower_owner_exponent=lower_owner_exponent,
                upper_owner_exponent=upper_owner_exponent,
                reflection_difference=d + k + 1 - 2 * lower_owner,
                centered_difference=d + upper_owner - lower_owner,
                owner_offset=abs(lower_owner + upper_owner - (k + 1)),
            )
        )
    return rows


def exact_equation(k: int, n: int, d: int) -> bool:
    lower = prod(block_terms(k, n))
    upper = prod(block_terms(k, n + d))
    return upper == 4 * lower


def reflection_congruence(k: int, n: int, d: int) -> bool:
    center = reflection_center(k, n, d)
    lower = prod(block_terms(k, n))
    return reflection_coefficient(k) * lower % center == 0


def reflection_lcm_compression(k: int, n: int, d: int) -> bool:
    """Check ``S | c*(k-1)!*lcm(reflection differences)`` exactly."""
    center = reflection_center(k, n, d)
    rhs = reflection_coefficient(k) * factorial(k - 1) * reflection_lcm(k, d)
    return rhs % center == 0


def reflection_product_compression(k: int, n: int, d: int) -> bool:
    center = reflection_center(k, n, d)
    rhs = reflection_coefficient(k) * reflection_product(k, d)
    return rhs % center == 0


def nonreflected_residual_bound(k: int, n: int, d: int) -> bool:
    """Check whether all deterministic residual chunks are non-reflected.

    Under the exact equation, this condition makes every residual power divide
    ``lcm(1,...,k-1)``.  It is intentionally a structural restriction, not an
    encoding of nonexistence.
    """
    return all(
        row.residual_exponent == 0 or not row.reflected
        for row in owner_correlations(k, n, d)
    )


def uniform_large_gap_threshold(k: int) -> int:
    """Least ``d`` with ``5*(k-1)!*lcm(1..k-1) <= 19*d``."""
    numerator = 5 * factorial(k - 1) * small_index_lcm(k)
    return (numerator + 18) // 19


def exact_large_gap_threshold(k: int) -> int:
    """Parity-sharp threshold using coefficient 3 or 5."""
    numerator = reflection_coefficient(k) * factorial(k - 1) * small_index_lcm(k)
    return (numerator + 18) // 19
