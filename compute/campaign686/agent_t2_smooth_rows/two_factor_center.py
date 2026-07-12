#!/usr/bin/env python3
"""Exact arithmetic model for the two-large-factor center exclusion.

This file mirrors the *pure arithmetic* premises of
``Erdos686ReflectedAlignmentTwoFactor.lean``.  It does not attempt to infer
the reflected square lifts from row-prefix survival: callers must supply a
factorization ``S=q*r`` and the two exact square divisibilities.

All calculations use Python integers.  No floating-point comparisons occur.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial, isqrt


def reflection_center(k: int, n: int, d: int) -> int:
    if min(k, n, d) < 0:
        raise ValueError("expected natural k,n,d")
    return 2 * n + d + k + 1


def even_reflected_linear(k: int, n: int, d: int, owner: int) -> int:
    if not 1 <= owner <= k:
        raise ValueError("owner must lie in 1..k")
    return 5 * n + d + k + 1 + 3 * owner


def odd_reflected_linear(k: int, n: int, d: int, owner: int) -> int:
    if not 1 <= owner <= k:
        raise ValueError("owner must lie in 1..k")
    value = 3 * n - d - k - 1 + 5 * owner
    if value < 0:
        raise ValueError("odd reflected linear is negative")
    return value


def factor_pairs(value: int) -> list[tuple[int, int]]:
    """Return both orientations of every positive factor pair."""
    if value <= 0:
        raise ValueError("value must be positive")
    pairs: list[tuple[int, int]] = []
    for q in range(1, isqrt(value) + 1):
        if value % q:
            continue
        r = value // q
        pairs.append((q, r))
        if q != r:
            pairs.append((r, q))
    return pairs


def prime_factors(value: int) -> tuple[int, ...]:
    """Distinct prime factors, obtained by exact trial division."""
    if value <= 0:
        raise ValueError("value must be positive")
    factors: list[int] = []
    candidate = 2
    while candidate * candidate <= value:
        if value % candidate:
            candidate += 1
            continue
        factors.append(candidate)
        while value % candidate == 0:
            value //= candidate
        candidate += 1
    if value > 1:
        factors.append(value)
    return tuple(factors)


def large_prime_supported(k: int, value: int) -> bool:
    """Every prime divisor of ``value`` is strictly larger than ``k``."""
    return value > 1 and all(k < prime for prime in prime_factors(value))


def valuation(value: int, prime: int) -> int:
    if value <= 0 or prime < 2:
        raise ValueError("expected positive value and prime >= 2")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def reflection_loss_exponent(k: int, prime: int) -> int:
    if k < 1:
        raise ValueError("expected k >= 1")
    coefficient = 3 if k % 2 == 0 else 5
    return valuation(coefficient, prime) + valuation(factorial(k - 1), prime)


@dataclass(frozen=True)
class TwoFactorRow:
    k: int
    n: int
    d: int
    q: int
    r: int
    i: int
    j: int

    @property
    def center(self) -> int:
        return reflection_center(self.k, self.n, self.d)

    @property
    def first_linear(self) -> int:
        function = even_reflected_linear if self.k % 2 == 0 else odd_reflected_linear
        return function(self.k, self.n, self.d, self.i)

    @property
    def second_linear(self) -> int:
        function = even_reflected_linear if self.k % 2 == 0 else odd_reflected_linear
        return function(self.k, self.n, self.d, self.j)

    @property
    def target_range(self) -> bool:
        return 16 <= self.k <= self.d and 9 * self.d < self.n

    @property
    def center_factorization(self) -> bool:
        return self.center == self.q * self.r

    @property
    def large_factors(self) -> bool:
        return self.k < self.q and self.k < self.r

    @property
    def residue_units(self) -> bool:
        modulus = 3 if self.k % 2 == 0 else 5
        return self.q % modulus != 0 and self.r % modulus != 0

    @property
    def square_lifts(self) -> bool:
        return (
            self.first_linear % (self.q**2) == 0
            and self.second_linear % (self.r**2) == 0
        )

    @property
    def cofactors(self) -> tuple[int, int]:
        if not self.square_lifts:
            raise ValueError("square-lift premise is absent")
        return self.first_linear // self.q**2, self.second_linear // self.r**2

    @property
    def product_window(self) -> bool:
        product = self.first_linear * self.second_linear
        center_square = self.center**2
        if self.k % 2 == 0:
            return 5 * center_square < product < 8 * center_square
        return center_square < product < 4 * center_square

    @property
    def pure_theorem_premises(self) -> bool:
        return (
            self.target_range
            and self.center_factorization
            and self.large_factors
            and self.residue_units
            and self.square_lifts
        )


def candidate_rows(k: int, n: int, d: int) -> list[TwoFactorRow]:
    """Enumerate rows satisfying every pure-theorem premise.

    The Lean theorem proves that this list is empty throughout the target
    range.  This routine is only a finite falsification tool, not a proof.
    """
    if not (16 <= k <= d and 9 * d < n):
        raise ValueError("outside the target range")
    center = reflection_center(k, n, d)
    modulus = 3 if k % 2 == 0 else 5
    result: list[TwoFactorRow] = []
    for q, r in factor_pairs(center):
        if q <= k or r <= k or q % modulus == 0 or r % modulus == 0:
            continue
        first_owners = [
            i
            for i in range(1, k + 1)
            if (even_reflected_linear(k, n, d, i) if k % 2 == 0
                else odd_reflected_linear(k, n, d, i)) % q**2 == 0
        ]
        second_owners = [
            j
            for j in range(1, k + 1)
            if (even_reflected_linear(k, n, d, j) if k % 2 == 0
                else odd_reflected_linear(k, n, d, j)) % r**2 == 0
        ]
        for i in first_owners:
            for j in second_owners:
                row = TwoFactorRow(k, n, d, q, r, i, j)
                assert row.pure_theorem_premises
                result.append(row)
    return result


def owner_aggregated_candidate_rows(k: int, n: int, d: int) -> list[TwoFactorRow]:
    """Finite falsifier for the two-reflected-owner aggregate theorem."""
    return [
        row
        for row in candidate_rows(k, n, d)
        if large_prime_supported(k, row.q) and large_prime_supported(k, row.r)
    ]


def residue_obstruction_tables() -> dict[str, tuple[tuple[int, int], ...]]:
    """List multiplier pairs surviving the product window, before residues."""
    return {
        "even_uv_6": ((1, 6), (2, 3), (3, 2), (6, 1)),
        "even_uv_7": ((1, 7), (7, 1)),
        "odd_uv_2": ((1, 2), (2, 1)),
        "odd_uv_3": ((1, 3), (3, 1)),
    }
