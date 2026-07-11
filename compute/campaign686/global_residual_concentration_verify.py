#!/usr/bin/env python3
"""Exact verifier for global-residual valuation concentration in Erdős 686.

All arithmetic is integral.  The second-order two-bucket audit uses the signed
local Taylor convention

    Q_i(z) = C_i + D_i z + E_i z^2 + O(z^3).

No floating-point estimates or external factorization oracles are used.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import factorial, prod
from typing import Any


ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
TARGET = 10**120
TWO_PRIME_LOSS_BOUND = 59_049**2
DEEP_FIXTURES = ((984, 3_177_026, 4_480), (244, 48_502, 277))


def valuation(value: int, prime: int) -> int:
    if value <= 0 or prime < 2:
        raise ValueError("valuation expects a positive value and prime >= 2")
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def is_prime(value: int) -> bool:
    return value >= 2 and all(value % q for q in range(2, int(value**0.5) + 1))


def primes_up_to(bound: int) -> list[int]:
    return [value for value in range(2, bound + 1) if is_prime(value)]


def prime_factorization(value: int) -> dict[int, int]:
    if value <= 0:
        raise ValueError("factorization expects a positive integer")
    result: dict[int, int] = {}
    for prime in primes_up_to(int(value**0.5) + 1):
        while value % prime == 0:
            result[prime] = result.get(prime, 0) + 1
            value //= prime
    if value > 1:
        result[value] = result.get(value, 0) + 1
    return result


def block_product(k: int, n: int) -> int:
    return prod(n + i for i in range(1, k + 1))


def residuals(k: int, n: int, d: int) -> list[int]:
    return [3 * (n + i) - d for i in range(1, k + 1)]


def loss_exponent(prime: int, k: int) -> int:
    factorial_valuation = valuation(factorial(k - 1), prime)
    if prime == 3:
        return (k + factorial_valuation) // 2
    return (factorial_valuation + 1) // 2


def clean_exponent(prime: int, exponent: int, k: int) -> int:
    return max(exponent - loss_exponent(prime, k), 0)


def aggregate_loss_budget(k: int) -> int:
    """Product of every possible per-prime cleaning loss for row ``k``."""

    return prod(
        prime ** loss_exponent(prime, k) for prime in primes_up_to(k - 1)
    )


def concentration_owner(k: int, n: int, d: int, prime: int) -> int:
    values = residuals(k, n, d)
    if min(values) <= 0:
        raise ValueError("the natural residual theorem requires positive residuals")
    if prime == 3:
        if d % 3:
            raise ValueError("the p=3 branch requires 3 | d")
        reduced = [n + i - d // 3 for i in range(1, k + 1)]
        return max(range(k), key=lambda index: valuation(reduced[index], prime))
    return max(range(k), key=lambda index: valuation(values[index], prime))


def verify_clean_component(
    k: int, n: int, d: int, prime: int, exponent: int
) -> dict[str, Any]:
    values = residuals(k, n, d)
    residual_product = prod(values)
    if min(values) <= 0 or residual_product % (d * d):
        raise ValueError("expected the positive global-square premise")
    if d % prime**exponent:
        raise ValueError("expected p^e | d")
    owner = concentration_owner(k, n, d, prime)
    retained = clean_exponent(prime, exponent, k)
    clean = prime**retained
    factor = n + owner + 1
    residual = values[owner]
    return {
        "prime": prime,
        "exponent": exponent,
        "owner": owner + 1,
        "loss_exponent": loss_exponent(prime, k),
        "retained_exponent": retained,
        "clean": clean,
        "divides_gap": d % clean == 0,
        "divides_lower_factor": factor % clean == 0,
        "square_divides_residual": residual % (clean * clean) == 0,
        "component_bound": prime**exponent <= prime ** loss_exponent(prime, k) * clean,
    }


def exhaustive_positive_square_checks() -> tuple[int, int]:
    premise_rows = 0
    component_rows = 0
    for k in ROWS:
        for d in range(k, 80):
            for n in range(2 * d + 1, 180):
                values = residuals(k, n, d)
                if prod(values) % (d * d):
                    continue
                premise_rows += 1
                for prime, exponent in prime_factorization(d).items():
                    result = verify_clean_component(k, n, d, prime, exponent)
                    assert all(
                        result[key]
                        for key in (
                            "divides_gap",
                            "divides_lower_factor",
                            "square_divides_residual",
                            "component_bound",
                        )
                    )
                    component_rows += 1
    return premise_rows, component_rows


def local_taylor_coefficients(k: int, index: int) -> tuple[int, int, int]:
    if not 1 <= index <= k:
        raise ValueError("expected 1 <= index <= k")
    coefficients = [1]
    for column in range(1, k + 1):
        if column == index:
            continue
        offset = column - index
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return coefficients[0], coefficients[1], coefficients[2]


def evaluate_local_cofactor(k: int, index: int, value: int) -> int:
    return prod(
        value + column - index
        for column in range(1, k + 1)
        if column != index
    )


def third_order_remainder(k: int, index: int, value: int) -> int:
    constant, linear, quadratic = local_taylor_coefficients(k, index)
    return (
        evaluate_local_cofactor(k, index, value)
        - constant
        - linear * value
        - quadratic * value * value
    )


def verify_third_algebra_identity(
    x: int, m: int, a: int, h: int, constant: int, linear: int, quadratic: int
) -> bool:
    """Verify the exact identity used after `3*x-m=a*h`.

    The expression `T` is the quotient after removing `h^2` from the local
    equation through quadratic order.  The returned congruence is

        9*T == -3*(3*C*a-4*D*m^2) + 20*E*h*m^3  (mod h^2).
    """

    if h <= 0 or 3 * x - m != a * h:
        raise ValueError("expected h>0 and 3*x-m=a*h")
    b2 = (x + m) ** 2 - 4 * x**2
    b3 = (x + m) ** 3 - 4 * x**3
    quotient = -constant * a + linear * b2 + h * quadratic * b3
    obstruction = (
        -3 * (3 * constant * a - 4 * linear * m * m)
        + 20 * quadratic * h * m**3
    )
    return (9 * quotient - obstruction) % (h * h) == 0


def two_bucket_row_report(k: int, bound_a: int) -> dict[str, Any]:
    budget = aggregate_loss_budget(k)
    generic_pairs: list[tuple[int, int]] = []
    reflected_exceptions: list[dict[str, Any]] = []
    generic_majorant = 0
    third_majorant = 0
    for i in range(1, k + 1):
        ci, di, ei = local_taylor_coefficients(k, i)
        for j in range(1, k + 1):
            if i == j:
                continue
            cj, dj, ej = local_taylor_coefficients(k, j)
            delta = i - j
            determinant = cj * di + ci * dj
            pair_majorant = max(
                3 * (abs(ci) * bound_a**2 + 4 * abs(di) * abs(delta)),
                3 * (abs(cj) * bound_a**2 + 4 * abs(dj) * abs(delta)),
            )
            generic_majorant = max(generic_majorant, pair_majorant)
            if determinant:
                generic_pairs.append((i, j))
                continue
            slope = Fraction(-4 * di * delta, ci)
            assert j == k + 1 - i
            assert slope > 0
            if i < j:
                third_bound = (
                    3600
                    * abs(delta) ** 2
                    * abs(ei * ej)
                    * budget**7
                )
                third_majorant = max(third_majorant, third_bound)
                reflected_exceptions.append(
                    {
                        "i": i,
                        "j": j,
                        "slope_numerator": slope.numerator,
                        "slope_denominator": slope.denominator,
                        "quadratic_i": ei,
                        "quadratic_j": ej,
                        "quadratics_nonzero": ei != 0 and ej != 0,
                        "third_gcd_bound": third_bound,
                        "third_gcd_bound_below_target": third_bound < TARGET,
                    }
                )
    generic_gap_bound = bound_a * generic_majorant**2 * budget**6
    return {
        "k": k,
        "A": bound_a,
        "aggregate_loss_budget": budget,
        "ordered_distinct_pairs": k * (k - 1),
        "generic_ordered_pair_count": len(generic_pairs),
        "reflected_exception_count": len(reflected_exceptions),
        "generic_obstruction_majorant": generic_majorant,
        "generic_gap_bound": generic_gap_bound,
        "generic_gap_bound_below_target": generic_gap_bound < TARGET,
        "reflected_exceptions": reflected_exceptions,
        "maximum_third_gcd_bound": third_majorant,
        "all_third_gcd_bounds_below_target": all(
            item["third_gcd_bound_below_target"] for item in reflected_exceptions
        ),
    }


def report() -> dict[str, Any]:
    premise_rows, component_rows = exhaustive_positive_square_checks()
    row_reports = [two_bucket_row_report(k, bound) for k, bound in ROWS.items()]
    return {
        "loss_exponents": {
            k: {prime: loss_exponent(prime, k) for prime in primes_up_to(k - 1)}
            for k in ROWS
        },
        "aggregate_loss_budgets": {k: aggregate_loss_budget(k) for k in ROWS},
        "exhaustive_positive_square_premises": premise_rows,
        "exhaustive_clean_components": component_rows,
        "two_bucket_rows": row_reports,
        "all_generic_bounds_below_target": all(
            row["generic_gap_bound_below_target"] for row in row_reports
        ),
        "all_reflected_third_gcd_bounds_below_target": all(
            row["all_third_gcd_bounds_below_target"] for row in row_reports
        ),
        "two_prime_uniform_loss_bound": TWO_PRIME_LOSS_BOUND,
        "lean_two_prime_generic_bound": 35 * (10**30) ** 2 * TWO_PRIME_LOSS_BOUND**6,
        "lean_two_prime_third_bound": (
            400 * (10**12) ** 2 * 35**2 * TWO_PRIME_LOSS_BOUND**9
        ),
        "lean_two_prime_bounds_below_target": (
            35 * (10**30) ** 2 * TWO_PRIME_LOSS_BOUND**6 < TARGET
            and 400 * (10**12) ** 2 * 35**2 * TWO_PRIME_LOSS_BOUND**9 < TARGET
        ),
        "d1_telescopes_are_outside_separated_range": [
            (k, k // 3 - 1, 1) for k in (3, 6, 9, 12, 15)
        ],
        "deep_fixtures_are_not_equations": [
            block_product(k, n + d) != 4 * block_product(k, n)
            for k, n, d in DEEP_FIXTURES
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
