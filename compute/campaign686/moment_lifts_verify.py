#!/usr/bin/env python3
"""Exact arithmetic checks for the two #686 cubic moment combinations."""

from __future__ import annotations

from math import prod


def polynomial_coefficients(roots: list[int]) -> list[int]:
    coefficients = [1]
    for root in roots:
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += coefficient * root
            updated[degree + 1] += coefficient
        coefficients = updated
    return coefficients


def evaluate(coefficients: list[int], value: int) -> int:
    return sum(coefficient * value**degree for degree, coefficient in enumerate(coefficients))


def moment_remainders(coefficients: list[int], d: int) -> tuple[int, int]:
    """The two corrected evaluation differences, before using an equation.

    Both entries are divisible by ``d**3`` for every integer polynomial.  At
    ``d == 0`` they vanish exactly, which is the meaning of divisibility by
    zero in the corresponding Lean statements.
    """

    constant = coefficients[0] if coefficients else 0
    linear = coefficients[1] if len(coefficients) > 1 else 0
    direct = (
        evaluate(coefficients, 2 * d)
        - 4 * evaluate(coefficients, d)
        + 3 * constant
        + 2 * d * linear
    )
    reflected = (
        evaluate(coefficients, 2 * d)
        - 4 * evaluate(coefficients, -d)
        + 3 * constant
        - 6 * d * linear
    )
    return direct, reflected


def block(k: int, n: int) -> int:
    return prod(n + i for i in range(1, k + 1))


def moment_certificate(k: int, n: int, d: int) -> dict[str, int | bool]:
    lower = polynomial_coefficients([n + i - d for i in range(1, k + 1)])
    upper = polynomial_coefficients([3 * (n + i) + d for i in range(1, k + 1)])
    equation = block(k, n + d) == 4 * block(k, n)
    lower_identity = evaluate(lower, 2 * d) - 4 * evaluate(lower, d)
    upper_identity = evaluate(upper, 2 * d) - 4 * evaluate(upper, -d)
    lower_combination = 3 * lower[0] + 2 * d * lower[1]
    upper_combination = 3 * upper[0] - 6 * d * upper[1]
    return {
        "equation": equation,
        "lower_identity": lower_identity,
        "upper_identity": upper_identity,
        "lower_combination": lower_combination,
        "upper_combination": upper_combination,
        "lower_cube_divides": lower_combination % d**3 == 0 if equation and d else True,
        "upper_cube_divides": upper_combination % d**3 == 0 if equation and d else True,
    }


def main() -> None:
    fixtures = [(3, 0, 1), (6, 1, 1), (9, 2, 1), (15, 4, 1)]
    for fixture in fixtures:
        certificate = moment_certificate(*fixture)
        assert certificate["equation"]
        assert certificate["lower_identity"] == 0
        assert certificate["upper_identity"] == 0
        assert certificate["lower_cube_divides"]
        assert certificate["upper_cube_divides"]
    print({"fixtures": len(fixtures), "all_exact": True})


if __name__ == "__main__":
    main()
