#!/usr/bin/env python3
"""Exact verifier for the Erdős 686 two-prime second local lift.

All calculations use Python integers.  The signed convention is

    Q_i(z) = product_{j != i} (z + j - i) = C_i + D_i*z + O(z^2).

For delta=i-j and t=a*b, the two fixed obstruction integers after the
second lift and Pell substitution are

    X = C_i*t + 4*D_i*delta,
    Y = C_j*t - 4*D_j*delta.
"""

from __future__ import annotations

import argparse
import json
from math import prod
from typing import Any


ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
LEAN_ABS_BOUND = 10**20


def local_coefficients(k: int, index: int) -> tuple[int, int]:
    if k < 1 or not 1 <= index <= k:
        raise ValueError("expected 1 <= index <= k")
    offsets = [column - index for column in range(1, k + 1) if column != index]
    constant = prod(offsets)
    linear = sum(
        prod(offsets[:position] + offsets[position + 1 :])
        for position in range(len(offsets))
    )
    return constant, linear


def evaluate_local_cofactor(k: int, index: int, value: int) -> int:
    return prod(
        value + column - index
        for column in range(1, k + 1)
        if column != index
    )


def second_order_remainder(k: int, index: int, value: int) -> int:
    constant, linear = local_coefficients(k, index)
    return evaluate_local_cofactor(k, index, value) - constant - linear * value


def obstruction_pair(k: int, i: int, j: int, product_ab: int) -> tuple[int, int]:
    if product_ab <= 0:
        raise ValueError("a*b must be positive")
    constant_i, linear_i = local_coefficients(k, i)
    constant_j, linear_j = local_coefficients(k, j)
    delta = i - j
    return (
        constant_i * product_ab + 4 * linear_i * delta,
        constant_j * product_ab - 4 * linear_j * delta,
    )


def row_report(k: int, bound_a: int) -> dict[str, Any]:
    center = (k + 1) // 2
    simultaneous_zeros: list[tuple[int, int, int]] = []
    single_zeros: list[tuple[int, int, int, int, int]] = []
    maximum = -1
    maximizer: tuple[int, int, int, int, int] | None = None
    cases = 0
    for i in range(1, k + 1):
        if i == center:
            continue
        for j in range(1, k + 1):
            if j == center or i == j:
                continue
            for product_ab in range(1, bound_a * bound_a):
                left, right = obstruction_pair(k, i, j, product_ab)
                cases += 1
                if left == 0 and right == 0:
                    simultaneous_zeros.append((i, j, product_ab))
                if left == 0 or right == 0:
                    single_zeros.append((i, j, product_ab, left, right))
                size = max(abs(3 * left), abs(3 * right))
                if size > maximum:
                    maximum = size
                    maximizer = (i, j, product_ab, left, right)
    return {
        "k": k,
        "A": bound_a,
        "cases": cases,
        "simultaneous_zeros": simultaneous_zeros,
        "single_zero_count": len(single_zeros),
        "maximum_three_times_abs_obstruction": maximum,
        "maximizer": maximizer,
        "below_lean_abs_bound": maximum < LEAN_ABS_BOUND,
    }


def report() -> dict[str, Any]:
    rows = [row_report(k, bound_a) for k, bound_a in ROWS.items()]
    maximum = max(row["maximum_three_times_abs_obstruction"] for row in rows)
    return {
        "coefficient_tables": {
            k: [local_coefficients(k, index) for index in range(1, k + 1)]
            for k in ROWS
        },
        "rows": rows,
        "global_maximum_three_times_abs_obstruction": maximum,
        "lean_abs_bound": LEAN_ABS_BOUND,
        "all_nonzero": all(not row["simultaneous_zeros"] for row in rows),
        "all_below_lean_abs_bound": all(row["below_lean_abs_bound"] for row in rows),
        "final_product_bound": 35 * LEAN_ABS_BOUND**2,
        "target_cutoff": 10**120,
        "final_product_bound_below_cutoff": 35 * LEAN_ABS_BOUND**2 < 10**120,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
