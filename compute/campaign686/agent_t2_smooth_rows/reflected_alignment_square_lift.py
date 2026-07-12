#!/usr/bin/env python3
"""Exact verifier for the reflected-owner quadratic lift.

Put ``A=n+i`` and ``B=n+d+(k+1-i)``.  If ``q`` divides both ``A`` and
``B``, expansion of the two block products at these reflected factors gives

    upper - 4*lower
      == W_i*((-1)^(k-1)*B - 4*A)                 (mod q^2),

where ``W_i=(-1)^(i-1)*(i-1)!*(k-i)!``.  Hence an exact equation makes the
right side divisible by ``q^2``.  If every prime divisor of ``q`` is larger
than ``k``, the weight is coprime to ``q`` and can be cancelled.

All operations are exact integers.  The equation premise is deliberately
kept explicit: the synthetic reflected-owner fixtures satisfy the older
reflection restrictions but fail this quadratic lift.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial, gcd, prod


def block_product(k: int, start: int) -> int:
    if k < 1 or start < 0:
        raise ValueError("expected k >= 1 and start >= 0")
    return prod(start + r for r in range(1, k + 1))


def signed_owner_weight(k: int, owner: int) -> int:
    if k < 1 or not 1 <= owner <= k:
        raise ValueError("owner must lie in 1..k")
    return (-1) ** (owner - 1) * factorial(owner - 1) * factorial(k - owner)


def reflected_upper_index(k: int, owner: int) -> int:
    if k < 1 or not 1 <= owner <= k:
        raise ValueError("owner must lie in 1..k")
    return k + 1 - owner


def reflected_owner_terms(k: int, n: int, d: int, owner: int) -> tuple[int, int]:
    if min(n, d) < 0:
        raise ValueError("expected natural n,d")
    upper_owner = reflected_upper_index(k, owner)
    return n + owner, n + d + upper_owner


def parity_linear(k: int, lower_owner_term: int, upper_owner_term: int) -> int:
    return (-1) ** (k - 1) * upper_owner_term - 4 * lower_owner_term


@dataclass(frozen=True)
class SquareLiftRow:
    k: int
    n: int
    d: int
    owner: int
    modulus: int
    lower_owner_term: int
    upper_owner_term: int
    owner_weight: int
    equation_error: int
    parity_linear: int
    congruence_error: int

    @property
    def owner_landings(self) -> bool:
        return (
            self.lower_owner_term % self.modulus == 0
            and self.upper_owner_term % self.modulus == 0
        )

    @property
    def quadratic_congruence(self) -> bool:
        return self.congruence_error % (self.modulus**2) == 0

    @property
    def exact_equation(self) -> bool:
        return self.equation_error == 0

    @property
    def weighted_square_lift(self) -> bool:
        return (
            self.owner_weight * self.parity_linear
        ) % (self.modulus**2) == 0

    @property
    def cancellable_square_lift(self) -> bool:
        return gcd(abs(self.owner_weight), self.modulus) == 1 and (
            self.parity_linear % (self.modulus**2) == 0
        )


def square_lift_row(k: int, n: int, d: int, owner: int, modulus: int) -> SquareLiftRow:
    if modulus < 1:
        raise ValueError("modulus must be positive")
    lower_owner_term, upper_owner_term = reflected_owner_terms(k, n, d, owner)
    weight = signed_owner_weight(k, owner)
    equation_error = block_product(k, n + d) - 4 * block_product(k, n)
    linear = parity_linear(k, lower_owner_term, upper_owner_term)
    return SquareLiftRow(
        k=k,
        n=n,
        d=d,
        owner=owner,
        modulus=modulus,
        lower_owner_term=lower_owner_term,
        upper_owner_term=upper_owner_term,
        owner_weight=weight,
        equation_error=equation_error,
        parity_linear=linear,
        congruence_error=equation_error - weight * linear,
    )


def prime_power(value: int, prime: int) -> int:
    if value <= 0 or prime < 2:
        raise ValueError("expected positive value and prime >= 2")
    result = 1
    while value % prime == 0:
        value //= prime
        result *= prime
    return result


def center_large_prime_row(
    k: int, n: int, d: int, prime: int, owner: int
) -> SquareLiftRow:
    """Build the target corollary row for ``p^v_p(S)``.

    The caller must establish the equation-level owner landing.  This helper
    refuses to infer it from reflection congruence or row-prefix survival.
    """
    center = 2 * n + d + k + 1
    modulus = prime_power(center, prime)
    row = square_lift_row(k, n, d, owner, modulus)
    if not prime > k:
        raise ValueError("large-center corollary requires prime > k")
    if not row.owner_landings:
        raise ValueError("the reflected owner landing is absent")
    return row
