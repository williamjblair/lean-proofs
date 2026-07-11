#!/usr/bin/env python3
"""Independent exact verifier for the three-bucket short-CRT LCM filter.

This module deliberately imports no Erdős 686 producer artifact.  It
reconstructs the local Taylor coefficients from the finite affine product,
enumerates every target-row owner triple, and verifies two consequences:

1. A vanishing second obstruction forces ``d < 10^120``.  The other two
   components divide fixed multiples of ``g^2``.  The vanishing owner's
   third obstruction makes its component divide a fixed multiple of ``g^3``.
   Pairwise coprimality packs all three into one LCM, so ``d | L*g^4``.
2. Above the cutoff all three second obstructions are nonzero.  Their exact
   coefficient majorants then give a row-specific lower bound on ``abc``.

All arithmetic is over Python integers and ``Fraction``; there are no floats.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import lcm
from typing import Any, Iterable, Sequence


TARGET = 10**120
ROWS = {
    5: (14, 108),
    7: (17, 1_620),
    9: (23, 136_080),
    11: (26, 1_224_720),
    13: (29, 242_494_560),
    15: (35, 18_914_575_680),
}


def multiply_affine(coefficients: Sequence[int], offset: int) -> list[int]:
    result = [0] * (len(coefficients) + 1)
    for degree, coefficient in enumerate(coefficients):
        result[degree] += offset * coefficient
        result[degree + 1] += coefficient
    return result


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    if not 1 <= owner <= k:
        raise ValueError("owner outside row")
    coefficients = [1]
    for column in range(1, k + 1):
        if column != owner:
            coefficients = multiply_affine(coefficients, column - owner)
    if len(coefficients) != k:
        raise AssertionError("local cofactor has wrong degree")
    return tuple(coefficients)


def owner_delta(owner: int, triple: Sequence[int]) -> int:
    others = [index for index in triple if index != owner]
    if len(others) != 2:
        raise ValueError("owner must occur exactly once")
    return (owner - others[0]) * (owner - others[1])


def second_zero_slope(k: int, owner: int, triple: Sequence[int]) -> Fraction:
    constant, linear = local_coefficients(k, owner)[:2]
    if constant == 0:
        raise AssertionError("target-row constant coefficient vanished")
    return Fraction(12 * linear * owner_delta(owner, triple), constant)


def triples(k: int) -> Iterable[tuple[int, int, int]]:
    return combinations(range(1, k + 1), 3)


def zero_case(k: int, indices: tuple[int, int, int], zero_owner: int) -> dict[str, Any]:
    slopes = {
        owner: second_zero_slope(k, owner, indices) for owner in indices
    }
    if len(set(slopes.values())) != 3:
        raise AssertionError("audited second slopes ceased to be distinct")
    zero_slope = slopes[zero_owner]
    if zero_slope <= 0:
        raise ValueError("positive abc cannot realize this zero")

    numerator_coefficients: list[int] = []
    denominator_coefficients: list[int] = []
    for owner in indices:
        if owner == zero_owner:
            continue
        constant = local_coefficients(k, owner)[0]
        # If t = zero_slope*g^2, then
        # O_owner/g^2 = 3*C_owner*(zero_slope-slope_owner).
        # Writing this as N/D gives D*O_owner=N*g^2.  Thus every
        # component dividing O_owner also divides |N|*g^2.
        coefficient = 3 * constant * (zero_slope - slopes[owner])
        if coefficient == 0:
            raise AssertionError("two second obstructions vanished")
        numerator_coefficients.append(abs(coefficient.numerator))
        denominator_coefficients.append(coefficient.denominator)

    quadratic = local_coefficients(k, zero_owner)[2]
    delta = owner_delta(zero_owner, indices)
    third_coefficient = abs(180 * quadratic * delta)
    if third_coefficient == 0:
        raise AssertionError("third-order repair coefficient vanished")

    common_lcm = lcm(
        numerator_coefficients[0],
        numerator_coefficients[1],
        third_coefficient,
    )
    return {
        "indices": list(indices),
        "zero_owner": zero_owner,
        "zero_slope": {
            "numerator": zero_slope.numerator,
            "denominator": zero_slope.denominator,
        },
        "other_numerators": numerator_coefficients,
        "other_denominators": denominator_coefficients,
        "third_coefficient": third_coefficient,
        "lcm": common_lcm,
    }


@cache
def majorant_factors(
    k: int, G: int
) -> tuple[tuple[tuple[int, int, int], tuple[tuple[int, int], ...]], ...]:
    records = []
    for indices in triples(k):
        factors = []
        for owner in indices:
            constant, linear = local_coefficients(k, owner)[:2]
            delta = abs(owner_delta(owner, indices))
            factors.append(
                (3 * abs(constant), 36 * abs(linear) * G**2 * delta)
            )
        records.append((indices, tuple(factors)))
    return tuple(records)


def obstruction_majorant(k: int, indices: tuple[int, int, int], t: int, G: int) -> int:
    """Upper-bound ``g*product |O_s|`` for ``g<=G`` and fixed ``abc=t``."""

    value = G
    for owner in indices:
        constant, linear = local_coefficients(k, owner)[:2]
        delta = abs(owner_delta(owner, indices))
        value *= 3 * abs(constant) * t + 36 * abs(linear) * G**2 * delta
    return value


def maximum_obstruction_majorant(k: int, t: int, G: int) -> tuple[int, tuple[int, int, int]]:
    maximum = -1
    maximizing_triple: tuple[int, int, int] | None = None
    for indices, factors in majorant_factors(k, G):
        value = G
        for coefficient, constant in factors:
            value *= coefficient * t + constant
        if value > maximum:
            maximum = value
            maximizing_triple = indices
    if maximizing_triple is None:
        raise AssertionError("empty target row")
    return maximum, maximizing_triple


def minimum_abc_from_nonzero_obstructions(k: int, G: int) -> tuple[int, int, int, tuple[int, int, int]]:
    """Return the first t whose uniform obstruction majorant reaches TARGET."""

    low = 0
    high = TARGET
    while low + 1 < high:
        middle = (low + high) // 2
        if maximum_obstruction_majorant(k, middle, G)[0] < TARGET:
            low = middle
        else:
            high = middle
    below, _ = maximum_obstruction_majorant(k, high - 1, G)
    at, maximizing_triple = maximum_obstruction_majorant(k, high, G)
    if not below < TARGET <= at:
        raise AssertionError("abc threshold search lost its boundary")
    return high, below, at, maximizing_triple


@cache
def row_report(k: int) -> dict[str, Any]:
    window, loss_budget = ROWS[k]
    all_zero_cases: list[dict[str, Any]] = []
    nonpositive_zero_slopes = 0
    for indices in triples(k):
        for owner in indices:
            slope = second_zero_slope(k, owner, indices)
            if slope > 0:
                all_zero_cases.append(zero_case(k, indices, owner))
            else:
                nonpositive_zero_slopes += 1

    maximum_case = max(all_zero_cases, key=lambda case: case["lcm"])
    maximum_lcm = maximum_case["lcm"]
    zero_branch_bound = maximum_lcm * loss_budget**4
    if not zero_branch_bound < TARGET:
        raise AssertionError("zero-obstruction LCM bound missed the target")

    minimum_abc, below, at, threshold_case = minimum_abc_from_nonzero_obstructions(
        k, loss_budget
    )
    return {
        "k": k,
        "window": window,
        "loss_budget": loss_budget,
        "unordered_triples": len(list(triples(k))),
        "positive_zero_cases": len(all_zero_cases),
        "nonpositive_zero_slopes": nonpositive_zero_slopes,
        "maximum_lcm": maximum_lcm,
        "maximum_lcm_case": maximum_case,
        "zero_branch_bound": zero_branch_bound,
        "zero_branch_margin_factor": TARGET // zero_branch_bound,
        "minimum_abc": minimum_abc,
        "abc_bound_at_predecessor": below,
        "abc_bound_at_minimum": at,
        "abc_threshold_case": list(threshold_case),
    }


def report() -> dict[str, Any]:
    rows = [row_report(k) for k in ROWS]
    return {
        "target": TARGET,
        "rows": rows,
        "all_zero_branches_below_target": all(
            row["zero_branch_bound"] < TARGET for row in rows
        ),
        "proved_restriction": (
            "every target-size exactly-three-bucket tuple has all three "
            "second obstructions nonzero and abc at least the row threshold"
        ),
        "remaining_gap": (
            "exclude the short-window tuples after imposing those nonzero "
            "obstructions, the row abc threshold, and all three square "
            "third-order divisibilities"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
