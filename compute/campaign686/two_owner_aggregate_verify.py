#!/usr/bin/env python3
"""Exact arithmetic audit for the Erdős 686 two-owner aggregate closure.

The verifier mirrors only the finite arithmetic used by the standalone Lean
module.  It uses Python integers throughout; no floating-point estimates,
probabilistic factorization, or external solvers are involved.
"""

from __future__ import annotations

import argparse
import json
from math import factorial, gcd, prod
from typing import Any

TARGET = 10**120
SECOND_OBSTRUCTION_BOUND = 10**16
COEFFICIENT_BOUND = 10**12
INDEX_DISTANCE_BOUND = 15
ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}

AGGREGATE_LOSS_BUDGETS = {
    5: 108,
    7: 1_620,
    9: 136_080,
    11: 1_224_720,
    13: 242_494_560,
    15: 18_914_575_680,
}


def valuation(value: int, prime: int) -> int:
    if value <= 0 or prime < 2:
        raise ValueError("valuation expects a positive value and prime >= 2")
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def is_prime(value: int) -> bool:
    return value >= 2 and all(value % divisor for divisor in range(2, value))


def aggregate_loss_budget(k: int) -> int:
    factors = []
    for prime in range(2, k):
        if not is_prime(prime):
            continue
        factorial_valuation = valuation(factorial(k - 1), prime)
        exponent = (
            (k + factorial_valuation) // 2
            if prime == 3
            else (factorial_valuation + 1) // 2
        )
        factors.append(prime**exponent)
    return prod(factors)


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


def exact_obstruction_majorant(k: int) -> int:
    """Largest exact second-obstruction coefficient before the ``g^2`` factor."""

    bound_a = ROWS[k]
    largest = 0
    for i in range(1, k + 1):
        ci, di, _ = local_taylor_coefficients(k, i)
        for j in range(1, k + 1):
            if i == j:
                continue
            cj, dj, _ = local_taylor_coefficients(k, j)
            delta = abs(i - j)
            largest = max(
                largest,
                3 * (abs(ci) * bound_a**2 + 4 * abs(di) * delta),
                3 * (abs(cj) * bound_a**2 + 4 * abs(dj) * delta),
            )
    return largest


def generic_cutoff_bound(k: int) -> int:
    """Lean's uniform nonzero-second-obstruction bound in row ``k``."""

    budget = AGGREGATE_LOSS_BUDGETS[k]
    return 35 * SECOND_OBSTRUCTION_BOUND**2 * budget**6


def uniform_cubic_cutoff_bound(k: int) -> int:
    """Lean's coefficient-uniform gcd-refined cubic bound in row ``k``."""

    budget = AGGREGATE_LOSS_BUDGETS[k]
    return (
        3_600
        * INDEX_DISTANCE_BOUND**2
        * COEFFICIENT_BOUND**2
        * budget**7
    )


def exact_cubic_pair_bound(k: int, i: int, j: int) -> int:
    """The paper-exact gcd-refined cubic bound for one ordered owner pair."""

    if i == j or not (1 <= i <= k and 1 <= j <= k):
        raise ValueError("expected two distinct indices in the target row")
    _, _, ei = local_taylor_coefficients(k, i)
    _, _, ej = local_taylor_coefficients(k, j)
    budget = AGGREGATE_LOSS_BUDGETS[k]
    return 3_600 * abs(i - j) ** 2 * abs(ei * ej) * budget**7


def cancellation_implication_holds(
    modulus: int, factor: int, coefficient: int, delta_multiple: int
) -> bool:
    """Check ``m|K*b`` and ``gcd(m,b)|D`` imply ``m|K*D`` exactly."""

    if min(modulus, factor, delta_multiple) <= 0 or coefficient < 0:
        raise ValueError("expected positive modulus/factors and nonnegative coefficient")
    if (coefficient * factor) % modulus:
        raise ValueError("first divisibility premise is false")
    if delta_multiple % gcd(modulus, factor):
        raise ValueError("gcd divisibility premise is false")
    return (coefficient * delta_multiple) % modulus == 0


def pell_gcd_consequences_hold(a: int, b: int, p: int, q: int, delta: int) -> bool:
    """Check both gcd consequences of ``a*p^2-b*q^2=3*delta``."""

    if min(a, b, p, q) <= 0:
        raise ValueError("expected positive Pell data")
    if a * p * p - b * q * q != 3 * delta:
        raise ValueError("Pell premise is false")
    scale = 3 * abs(delta)
    return scale % gcd(p, b) == 0 and scale % gcd(q, a) == 0


def row_report(k: int) -> dict[str, Any]:
    pair_bounds = [
        exact_cubic_pair_bound(k, i, j)
        for i in range(1, k + 1)
        for j in range(1, k + 1)
        if i != j
    ]
    return {
        "k": k,
        "A": ROWS[k],
        "aggregate_loss_budget": AGGREGATE_LOSS_BUDGETS[k],
        "recomputed_aggregate_loss_budget": aggregate_loss_budget(k),
        "exact_second_obstruction_majorant": exact_obstruction_majorant(k),
        "second_obstruction_below_10_pow_16": (
            exact_obstruction_majorant(k) < SECOND_OBSTRUCTION_BOUND
        ),
        "generic_cutoff_bound": generic_cutoff_bound(k),
        "generic_cutoff_below_target": generic_cutoff_bound(k) < TARGET,
        "uniform_cubic_cutoff_bound": uniform_cubic_cutoff_bound(k),
        "uniform_cubic_cutoff_below_target": (
            uniform_cubic_cutoff_bound(k) < TARGET
        ),
        "ordered_pair_count": len(pair_bounds),
        "maximum_exact_cubic_pair_bound": max(pair_bounds),
        "all_exact_cubic_pair_bounds_below_target": max(pair_bounds) < TARGET,
    }


def report() -> dict[str, Any]:
    rows = [row_report(k) for k in AGGREGATE_LOSS_BUDGETS]
    return {
        "aggregate_loss_budgets": AGGREGATE_LOSS_BUDGETS,
        "rows": rows,
        "all_budgets_recomputed_exactly": all(
            row["aggregate_loss_budget"] == row["recomputed_aggregate_loss_budget"]
            for row in rows
        ),
        "all_second_obstructions_below_10_pow_16": all(
            row["second_obstruction_below_10_pow_16"] for row in rows
        ),
        "all_generic_cutoffs_below_target": all(
            row["generic_cutoff_below_target"] for row in rows
        ),
        "all_uniform_cubic_cutoffs_below_target": all(
            row["uniform_cubic_cutoff_below_target"] for row in rows
        ),
        "all_exact_cubic_pair_bounds_below_target": all(
            row["all_exact_cubic_pair_bounds_below_target"] for row in rows
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
