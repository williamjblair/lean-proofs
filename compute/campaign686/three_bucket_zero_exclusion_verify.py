#!/usr/bin/env python3
"""Exact certificate for the target-row three-bucket zero exclusion.

The script reconstructs the local Taylor coefficients directly from the
finite affine product.  It checks every ordered triple of distinct owners in
the six odd target rows and independently reproduces the deliberately coarse
Lean ceilings.
"""

from __future__ import annotations

import argparse
import json
from itertools import permutations
from typing import Any


ROWS = (5, 7, 9, 11, 13, 15)
CROSS_BOUND = 10**30
THIRD_BOUND = 10**18
LOSS_BOUND = 18_914_575_680
CUTOFF = 10**120


def multiply_affine(coefficients: list[int], offset: int) -> list[int]:
    result = [0] * (len(coefficients) + 1)
    for degree, coefficient in enumerate(coefficients):
        result[degree] += offset * coefficient
        result[degree + 1] += coefficient
    return result


def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    coefficients = [1]
    for column in range(1, k + 1):
        if column != owner:
            coefficients = multiply_affine(coefficients, column - owner)
    return tuple(coefficients)


def delta(owner: int, left: int, right: int) -> int:
    return (owner - left) * (owner - right)


def cross_numerator(k: int, owner: int, zero: int, other: int) -> int:
    c_owner, d_owner = local_coefficients(k, owner)[:2]
    c_zero, d_zero = local_coefficients(k, zero)[:2]
    return 36 * (
        c_owner * d_zero * delta(zero, owner, other)
        - d_owner * delta(owner, zero, other) * c_zero
    )


def third_coefficient(k: int, zero: int, owner: int, other: int) -> int:
    quadratic = local_coefficients(k, zero)[2]
    return 180 * quadratic * delta(zero, owner, other)


def report() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    global_max_cross = 0
    global_max_third = 0
    global_cross_case: tuple[int, int, int, int] | None = None
    global_third_case: tuple[int, int, int, int] | None = None
    for k in ROWS:
        count = 0
        row_max_cross = 0
        row_max_third = 0
        for owner, zero, other in permutations(range(1, k + 1), 3):
            count += 1
            cross = abs(cross_numerator(k, owner, zero, other))
            third = abs(third_coefficient(k, zero, owner, other))
            if cross == 0 or third == 0:
                raise AssertionError((k, owner, zero, other, cross, third))
            if not cross < CROSS_BOUND or not third < THIRD_BOUND:
                raise AssertionError("coarse certificate ceiling failed")
            row_max_cross = max(row_max_cross, cross)
            row_max_third = max(row_max_third, third)
            if cross > global_max_cross:
                global_max_cross = cross
                global_cross_case = (k, owner, zero, other)
            if third > global_max_third:
                global_max_third = third
                global_third_case = (k, owner, zero, other)
        rows.append(
            {
                "k": k,
                "ordered_distinct_owner_triples": count,
                "maximum_cross_numerator": row_max_cross,
                "maximum_third_coefficient": row_max_third,
            }
        )
    numeric_majorant = CROSS_BOUND**2 * THIRD_BOUND * LOSS_BOUND**4
    if not numeric_majorant < CUTOFF:
        raise AssertionError("rounded global majorant reached the cutoff")
    return {
        "rows": rows,
        "ordered_distinct_owner_triples": sum(
            row["ordered_distinct_owner_triples"] for row in rows
        ),
        "global_maximum_cross_numerator": global_max_cross,
        "global_maximum_cross_case": global_cross_case,
        "global_maximum_third_coefficient": global_max_third,
        "global_maximum_third_case": global_third_case,
        "cross_bound": CROSS_BOUND,
        "third_bound": THIRD_BOUND,
        "loss_bound": LOSS_BOUND,
        "numeric_majorant": numeric_majorant,
        "cutoff": CUTOFF,
        "cutoff_margin_floor": CUTOFF // numeric_majorant,
        "all_zero_obstruction_branches_excluded_above_cutoff": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
