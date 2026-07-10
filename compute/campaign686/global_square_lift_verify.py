#!/usr/bin/env python3
"""Exact verifier for the global quadratic residual lift in Erdős 686."""

from __future__ import annotations

from math import prod
from random import Random


def block_product(k: int, n: int) -> int:
    if k < 0 or n < 0:
        raise ValueError("expected nonnegative k,n")
    return prod(n + i for i in range(1, k + 1))


def residuals(k: int, n: int, d: int) -> list[int]:
    if min(k, n, d) < 0:
        raise ValueError("expected natural inputs")
    return [3 * (n + i) - d for i in range(1, k + 1)]


def affine_product_coefficients(values: list[int]) -> list[int]:
    """Coefficients of ``prod_x (x+z)``, in increasing powers of z."""

    coefficients = [1]
    for value in values:
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += value * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return coefficients


def residual_quotient_formula(k: int, n: int, d: int) -> int:
    """The exact polynomial quotient forced when the block equation holds."""

    coefficients = affine_product_coefficients(residuals(k, n, d))
    return sum(
        ((4**degree - 4) // 3) * coefficient * d ** (degree - 2)
        for degree, coefficient in enumerate(coefficients)
        if degree >= 2
    )


def transformed_equation_holds(k: int, n: int, d: int) -> bool:
    values = residuals(k, n, d)
    return prod(value + 4 * d for value in values) == 4 * prod(
        value + d for value in values
    )


def verify_square_lift(k: int, n: int, d: int) -> bool:
    if block_product(k, n + d) != 4 * block_product(k, n):
        return False
    values = residuals(k, n, d)
    residual_product = prod(values)
    if d == 0:
        return residual_product == 0
    return (
        transformed_equation_holds(k, n, d)
        and residual_product % (d * d) == 0
        and residual_product // (d * d) == residual_quotient_formula(k, n, d)
    )


def exact_small_solutions() -> list[tuple[int, int, int]]:
    return [
        (k, n, d)
        for k in range(1, 16)
        for d in range(1, 30)
        for n in range(200)
        if block_product(k, n + d) == 4 * block_product(k, n)
    ]


def random_polynomial_identity(seed: int = 686, samples: int = 200) -> bool:
    rng = Random(seed)
    for _ in range(samples):
        k = rng.randrange(0, 18)
        n = rng.randrange(0, 500)
        d = rng.randrange(0, 500)
        values = residuals(k, n, d)
        coefficients = affine_product_coefficients(values)
        left = prod(value + 4 * d for value in values)
        right = 4 * prod(value + d for value in values)
        correction = sum(
            (4**degree - 4) * coefficient * d**degree
            for degree, coefficient in enumerate(coefficients)
            if degree >= 2
        )
        if left - right + 3 * prod(values) != correction:
            return False
        if correction % (3 * d * d if d else 1) != 0:
            return False
    return True


if __name__ == "__main__":
    solutions = exact_small_solutions()
    print(
        {
            "small_solutions": solutions,
            "all_square_lifts": all(verify_square_lift(*row) for row in solutions),
            "random_identity": random_polynomial_identity(),
            "deep_fixtures_are_not_equations": [
                block_product(k, n + d) != 4 * block_product(k, n)
                for k, n, d in ((984, 3177026, 4480), (244, 48502, 277))
            ],
        }
    )
