#!/usr/bin/env python3
"""Exact reproduction of the k=5 Runge/number-field obstruction certificate."""

from __future__ import annotations

from fractions import Fraction
import json
from typing import Any


PRIME = 11


def trim(poly: list[int]) -> list[int]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def remainder_mod_prime(
    dividend: list[int], divisor: list[int], prime: int
) -> list[int]:
    value = [coefficient % prime for coefficient in dividend]
    divisor = trim([coefficient % prime for coefficient in divisor])
    inverse = pow(divisor[-1], -1, prime)
    while len(trim(value)) >= len(divisor) and value != [0]:
        shift = len(value) - len(divisor)
        coefficient = value[-1] * inverse % prime
        for index, entry in enumerate(divisor):
            value[index + shift] = (value[index + shift] - coefficient * entry) % prime
        trim(value)
    return trim(value)


def irreducible_mod_11_certificate() -> dict[str, int]:
    """A quintic is reducible only if it has a factor of degree 1 or 2."""
    polynomial = [-4, 0, 0, 0, 0, 1]
    checked_linear = 0
    for constant in range(PRIME):
        checked_linear += 1
        if remainder_mod_prime(polynomial, [constant, 1], PRIME) == [0]:
            raise AssertionError(("linear factor", constant))
    checked_quadratic = 0
    for constant in range(PRIME):
        for linear in range(PRIME):
            checked_quadratic += 1
            if remainder_mod_prime(polynomial, [constant, linear, 1], PRIME) == [0]:
                raise AssertionError(("quadratic factor", constant, linear))
    return {
        "prime": PRIME,
        "monic_linear_divisors_checked": checked_linear,
        "monic_quadratic_divisors_checked": checked_quadratic,
    }


def multiply(left: list[int], right: list[int]) -> list[int]:
    product = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            product[i + j] += a * b
    return trim(product)


def subtract(left: list[int], right: list[int]) -> list[int]:
    size = max(len(left), len(right))
    result = [0] * size
    for index in range(size):
        result[index] = (left[index] if index < len(left) else 0) - (
            right[index] if index < len(right) else 0
        )
    return trim(result)


def unit_identity_certificate() -> dict[str, Any]:
    epsilon = [1, 1, 0, -1]
    inverse = [9, 7, 5, 4, 3]
    quotient = [-2, -4, -3]
    minimal = [-4, 0, 0, 0, 0, 1]
    left = subtract(multiply(epsilon, inverse), [1])
    right = multiply(quotient, minimal)
    if left != right:
        raise AssertionError(("unit identity failed", left, right))
    return {
        "epsilon_coefficients": epsilon,
        "inverse_coefficients": inverse,
        "minimal_polynomial_coefficients": minimal,
        "quotient_coefficients": quotient,
    }


def target_scale_small_unit_certificate() -> dict[str, Any]:
    if not 131**5 < 4 * 100**5 < 132**5:
        raise AssertionError("fifth-root bracket failed")
    lower = 1 + Fraction(131, 100) - Fraction(132, 100) ** 3
    upper = 1 + Fraction(132, 100) - Fraction(131, 100) ** 3
    coarse = Fraction(9, 125)
    if not 0 < lower < upper < coarse < 1:
        raise AssertionError(("small-unit interval failed", lower, upper))
    cutoff = Fraction(1, 10**166)
    exponent = 1
    while coarse**exponent >= cutoff:
        exponent += 1
    if exponent != 146 or coarse**145 < cutoff:
        raise AssertionError("minimal frozen exponent changed")
    return {
        "epsilon_lower": f"{lower.numerator}/{lower.denominator}",
        "epsilon_upper": f"{upper.numerator}/{upper.denominator}",
        "coarse_upper": "9/125",
        "first_coarse_power_below_10^-166": exponent,
        "power_145_still_not_below": coarse**145 >= cutoff,
        "power_146_below": coarse**146 < cutoff,
    }


def full_report() -> dict[str, Any]:
    return {
        "status": (
            "classical Q-Runge has one infinity orbit; a norm-one unit is "
            "already smaller than 10^-166 at the real branch"
        ),
        "infinity_irreducibility": irreducible_mod_11_certificate(),
        "unit_identity": unit_identity_certificate(),
        "target_scale_unit": target_scale_small_unit_certificate(),
    }


def main() -> None:
    print(json.dumps(full_report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
