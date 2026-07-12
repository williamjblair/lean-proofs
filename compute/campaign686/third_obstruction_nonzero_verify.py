#!/usr/bin/env python3
"""Exact coefficient audit for the Erdős 686 third-obstruction route.

For one owner in an ordered distinct triple, write ``C,D,E`` for the
constant, linear, and quadratic coefficients of

    product_{1 <= j <= k, j != owner} (z + j - owner).

If the three selected residuals are at least ``L*d``, their exact cleaned
factorization gives ``abc >= L^3*g^2*d``.  The two inequalities checked here
then make the ``-9*C*abc`` term strictly dominate both correction terms in
the composed third obstruction at every ``d >= 10^120``.

All arithmetic is integral.  The coefficients are reconstructed directly;
no generated Lean table or campaign verifier is imported.
"""

from __future__ import annotations

import json
from itertools import permutations
from typing import Any


TARGET = 10**120
TARGET_ROWS = (5, 7, 9, 11, 13, 15)
RESIDUAL_FLOOR = {5: 8, 7: 12, 9: 15, 11: 20, 13: 23, 15: 29}
MULTI_OWNER_THIRD_BOUND = 56 * 10**12 * 3**14 * 15**14 + 1


def block_product(k: int, n: int) -> int:
    product = 1
    for index in range(1, k + 1):
        product *= n + index
    return product


def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
    """Return the first three exact local-cofactor coefficients."""

    coefficients = [1]
    for index in range(1, k + 1):
        if index == owner:
            continue
        offset = index - owner
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return coefficients[0], coefficients[1], coefficients[2]


def audit_target_rows() -> dict[str, Any]:
    per_row: dict[int, dict[str, Any]] = {}
    total = 0
    minimum_main: tuple[int, tuple[int, int, int, int]] | None = None
    minimum_cutoff: tuple[int, tuple[int, int, int, int]] | None = None

    for k in TARGET_ROWS:
        floor = RESIDUAL_FLOOR[k]
        row_count = 0
        row_main: tuple[int, tuple[int, int, int]] | None = None
        row_cutoff: tuple[int, tuple[int, int, int]] | None = None
        for owner, left, right in permutations(range(1, k + 1), 3):
            constant, linear, quadratic = local_coefficients(k, owner)
            if constant == 0:
                raise AssertionError(("zero constant", k, owner))
            delta = (owner - left) * (owner - right)
            main_margin = (
                9 * abs(constant) * floor**3
                - 180 * abs(quadratic * delta)
            )
            cutoff_margin = (
                TARGET * main_margin - 108 * abs(linear * delta)
            )
            if main_margin <= 0 or cutoff_margin <= 0:
                raise AssertionError(
                    {
                        "k": k,
                        "owners": (owner, left, right),
                        "coefficients": (constant, linear, quadratic),
                        "delta": delta,
                        "main_margin": main_margin,
                        "cutoff_margin": cutoff_margin,
                    }
                )
            case = (owner, left, right)
            if row_main is None or main_margin < row_main[0]:
                row_main = (main_margin, case)
            if row_cutoff is None or cutoff_margin < row_cutoff[0]:
                row_cutoff = (cutoff_margin, case)
            full_case = (k, owner, left, right)
            if minimum_main is None or main_margin < minimum_main[0]:
                minimum_main = (main_margin, full_case)
            if minimum_cutoff is None or cutoff_margin < minimum_cutoff[0]:
                minimum_cutoff = (cutoff_margin, full_case)
            row_count += 1

        if row_main is None or row_cutoff is None:
            raise AssertionError(("empty row", k))
        per_row[k] = {
            "ordered_distinct_triples": row_count,
            "residual_floor": floor,
            "minimum_main_margin": row_main[0],
            "minimum_main_case": row_main[1],
            "minimum_cutoff_margin": row_cutoff[0],
            "minimum_cutoff_case": row_cutoff[1],
        }
        total += row_count

    if minimum_main is None or minimum_cutoff is None:
        raise AssertionError("no target rows")
    return {
        "verdict": "PASS",
        "target": TARGET,
        "residual_floor": RESIDUAL_FLOOR,
        "ordered_distinct_triples": total,
        "minimum_main_margin": minimum_main[0],
        "minimum_main_case": minimum_main[1],
        "minimum_cutoff_margin": minimum_cutoff[0],
        "minimum_cutoff_case": minimum_cutoff[1],
        "per_row": per_row,
    }


def reproduce_telescopes() -> list[dict[str, Any]]:
    fixtures = [(9, 2, 1), (15, 4, 1)]
    return [
        {
            "k": k,
            "n": n,
            "d": d,
            "equation": block_product(k, n + d) == 4 * block_product(k, n),
            "in_target": TARGET <= d,
        }
        for k, n, d in fixtures
    ]


def audit_multi_owner_constant() -> dict[str, Any]:
    """Independently reproduce the complete-grid uniform coefficient bound.

    The Lean proof uses ``|D|,|E| < 10^12``, at most fourteen opposite
    owners, ``|Delta| <= 15^14``, and ``d >= 1``.  Checking the extremal
    integer values is enough because every factor is monotone in absolute
    value.
    """

    coefficient_cap = 10**12 - 1
    exponent_cap = 14
    delta_cap = 15**14
    samples: dict[int, dict[str, int | bool]] = {}
    for d in (1, 10**120, 10**166):
        exact_extremal = (
            12 * coefficient_cap + 20 * coefficient_cap * d
        ) * 3**exponent_cap * delta_cap
        upper = MULTI_OWNER_THIRD_BOUND * d
        if not exact_extremal < upper:
            raise AssertionError((d, exact_extremal, upper))
        samples[d] = {
            "extremal_correction": exact_extremal,
            "uniform_upper": upper,
            "strict": True,
        }
    target_margin = 625 * TARGET - MULTI_OWNER_THIRD_BOUND
    if target_margin <= 0:
        raise AssertionError((MULTI_OWNER_THIRD_BOUND, target_margin))
    return {
        "verdict": "PASS",
        "multi_owner_third_bound": MULTI_OWNER_THIRD_BOUND,
        "target_product_margin": target_margin,
        "samples": samples,
    }


def main() -> None:
    print(
        json.dumps(
            {
                "coefficient_audit": audit_target_rows(),
                "multi_owner_constant_audit": audit_multi_owner_constant(),
                "telescope_boundary": reproduce_telescopes(),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
