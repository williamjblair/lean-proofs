#!/usr/bin/env python3
"""Exact third-modulus check for the next reflected local coefficient.

This is a falsification model for the reflection analogue of the second
local lift.  It keeps the equation error explicit; an exact equation makes
the reported obstruction divisible by ``h``.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, prod

from compute.campaign686.agent_t2_smooth_rows.reflected_alignment_square_lift import (
    block_product,
    reflected_owner_terms,
)


def local_coefficients(k: int, owner: int) -> tuple[int, int]:
    offsets = [index - owner for index in range(1, k + 1) if index != owner]
    constant = prod(offsets)
    linear = sum(prod(offsets[:t] + offsets[t + 1 :]) for t in range(len(offsets)))
    return constant, linear


@dataclass(frozen=True)
class ReflectedSecondLiftRow:
    k: int
    n: int
    d: int
    owner: int
    h: int
    x: int
    m: int
    a: int
    constant: int
    linear: int
    obstruction: int
    equation_error: int

    @property
    def cubic_congruence(self) -> bool:
        return (self.equation_error + self.h**2 * self.obstruction) % self.h**3 == 0

    @property
    def exact_equation(self) -> bool:
        return self.equation_error == 0

    @property
    def next_lift(self) -> bool:
        return self.obstruction % self.h == 0


def reflected_second_lift_row(
    k: int, n: int, d: int, owner: int, h: int
) -> ReflectedSecondLiftRow:
    if h <= 0:
        raise ValueError("h must be positive")
    lower, upper = reflected_owner_terms(k, n, d, owner)
    if lower % h or upper % h:
        raise ValueError("reflected owner landing is absent")
    x = lower // h
    m = (lower + upper) // h
    if k % 2 == 0:
        residual = m + 3 * x
    else:
        residual = 5 * x - m
    if residual < 0 or residual % h:
        raise ValueError("quadratic reflected residual is absent")
    a = residual // h
    constant, linear = local_coefficients(k, owner)
    obstruction = (
        constant * a - 12 * linear * x**2
        if k % 2 == 0
        else constant * a + 20 * linear * x**2
    )
    return ReflectedSecondLiftRow(
        k, n, d, owner, h, x, m, a, constant, linear, obstruction,
        block_product(k, n + d) - 4 * block_product(k, n),
    )


def common_divisors(left: int, right: int) -> list[int]:
    common = gcd(left, right)
    return [value for value in range(1, common + 1) if common % value == 0]
