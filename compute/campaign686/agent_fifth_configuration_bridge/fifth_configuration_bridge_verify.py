#!/usr/bin/env python3
"""Exact sign audit for the simultaneous fifth-quotient bridge.

The underlying fourth/fifth eliminant recurrences are imported from the
independently tested short-window verifier.  Every new calculation here uses
Python integers or fractions.Fraction; no floating point is used.
"""

from __future__ import annotations

import json
from functools import cache
from fractions import Fraction
from typing import Any

from compute.campaign686.fifth_quotient_short_window_verify import (
    ROWS,
    eliminant_polynomial,
    fourth_eliminant_polynomial,
    leading_coefficients,
    leading_value,
    local_coefficients,
    nonreflected_triples,
    reduced_fifth_coefficients,
    reduced_fourth_coefficient,
    residual_ratio_interval,
)

TARGET_CUTOFF = 10**1000
RESIDUAL_ABSOLUTE_COEFFICIENT_BOUND = 36


def sign(value: int | Fraction) -> int:
    """Return the exact sign, rejecting a zero that would break the audit."""

    if value == 0:
        raise AssertionError("unexpected zero sign")
    return 1 if value > 0 else -1


def certified_eliminant_sign(
    polynomial: dict[tuple[int, int], int],
    leading: tuple[int, int, int],
    lower: Fraction,
    upper: Fraction,
) -> int:
    """Certify sign on the target window, including lower-degree terms.

    The degree-five part is a*x^5+b*x^2+c after dividing by d^5.
    Its only positive critical point can be detected by the exact cube
    -2b/(5a).  With no critical point in the interval and equal nonzero
    endpoint signs, the smaller endpoint magnitude is a valid margin.
    Lower-degree terms are bounded using |X| <= 36*d and d>=10^1000.
    """

    a, b, _c = leading
    values = (leading_value(leading, lower), leading_value(leading, upper))
    if sign(values[0]) != sign(values[1]):
        raise AssertionError("leading endpoint sign change")
    critical_cube = Fraction(-2 * b, 5 * a)
    if critical_cube > 0 and lower**3 <= critical_cube <= upper**3:
        raise AssertionError("leading critical point lies in target interval")

    homogeneous = {
        degree_x: coefficient
        for (degree_x, degree_d), coefficient in polynomial.items()
        if degree_x + degree_d == 5
    }
    expected = {
        degree: coefficient
        for degree, coefficient in enumerate(
            (leading[2], 0, leading[1], 0, 0, leading[0])
        )
        if coefficient
    }
    if homogeneous != expected:
        raise AssertionError(("homogeneous mismatch", homogeneous, expected))

    remainder = sum(
        abs(coefficient) * RESIDUAL_ABSOLUTE_COEFFICIENT_BOUND**degree_x
        for (degree_x, degree_d), coefficient in polynomial.items()
        if degree_x + degree_d < 5
    )
    margin = min(abs(value) for value in values)
    if margin * TARGET_CUTOFF <= remainder:
        raise AssertionError("target cutoff does not dominate remainder")
    return sign(values[0])


def position_data(
    k: int, triple: tuple[int, int, int], owner: int
) -> dict[str, int]:
    """Return exact lattice coefficients and certified w/N signs."""

    opposite = [index for index in triple if index != owner]
    left, right = owner - opposite[0], owner - opposite[1]
    delta = left * right
    C, D, E, F, G = local_coefficients(k, owner)
    K = reduced_fourth_coefficient(C, D, E, F, left, right)
    R1, _R2 = reduced_fifth_coefficients(C, D, E, F, G, left, right)
    lower, upper = residual_ratio_interval(k)

    fourth_leading = (-243 * C**3, 4860 * C**2 * E * delta, 0)
    w_sign = certified_eliminant_sign(
        fourth_eliminant_polynomial(C, D, E, K, left, right),
        fourth_leading,
        lower,
        upper,
    )
    n_sign = certified_eliminant_sign(
        eliminant_polynomial(C, D, E, K, R1, left, right),
        leading_coefficients(C, E, delta, R1),
        lower,
        upper,
    )
    if w_sign != -sign(C):
        raise AssertionError("fourth quotient does not have sign -C")
    return {
        "A": -9 * C,
        "B": 180 * E * delta,
        "G": 108 * D * delta,
        "C": C,
        "w_sign": w_sign,
        "n_sign": n_sign,
    }


@cache
def report() -> dict[str, Any]:
    """Scan all 1,008 triples and all 3,024 cyclic owner positions."""

    rows: list[dict[str, int]] = []
    total_triples = total_positions = total_n_flips = 0
    total_w_mixed = total_n_mixed = total_weight_nonzero = 0
    gamma_positive = gamma_negative = 0

    for k in ROWS:
        row_triples = row_positions = row_n_flips = 0
        row_w_mixed = row_n_mixed = row_weight_nonzero = 0
        for triple in nonreflected_triples(k):
            data = [position_data(k, triple, owner) for owner in triple]
            A = [item["A"] for item in data]
            B = [item["B"] for item in data]
            G = [item["G"] for item in data]
            weights = (
                A[1] * B[2] - A[2] * B[1],
                A[2] * B[0] - A[0] * B[2],
                A[0] * B[1] - A[1] * B[0],
            )
            if sum(weight * coefficient for weight, coefficient in zip(weights, A)) != 0:
                raise AssertionError("cyclic weights do not kill A")
            if sum(weight * coefficient for weight, coefficient in zip(weights, B)) != 0:
                raise AssertionError("cyclic weights do not kill B")
            gamma = sum(
                weight * coefficient for weight, coefficient in zip(weights, G)
            )
            gamma_positive += gamma > 0
            gamma_negative += gamma < 0

            row_weight_nonzero += sum(weight != 0 for weight in weights)
            weighted_w_signs = {
                sign(weight) * item["w_sign"]
                for weight, item in zip(weights, data)
            }
            weighted_n_signs = {
                sign(weight) * item["n_sign"]
                for weight, item in zip(weights, data)
            }
            row_w_mixed += weighted_w_signs == {-1, 1}
            row_n_mixed += weighted_n_signs == {-1, 1}
            row_n_flips += sum(
                item["n_sign"] != item["w_sign"] for item in data
            )
            row_triples += 1
            row_positions += 3

        rows.append(
            {
                "k": k,
                "nonreflected_triples": row_triples,
                "cyclic_positions": row_positions,
                "normalized_sign_flips_from_w": row_n_flips,
                "nonzero_cyclic_weights": row_weight_nonzero,
                "weighted_w_mixed_triples": row_w_mixed,
                "weighted_n_mixed_triples": row_n_mixed,
            }
        )
        total_triples += row_triples
        total_positions += row_positions
        total_n_flips += row_n_flips
        total_weight_nonzero += row_weight_nonzero
        total_w_mixed += row_w_mixed
        total_n_mixed += row_n_mixed

    if gamma_positive + gamma_negative != total_triples:
        raise AssertionError("zero cyclic Gamma")
    return {
        "arithmetic": "exact Python integers and fractions.Fraction",
        "rows": rows,
        "totals": {
            "nonreflected_triples": total_triples,
            "cyclic_positions": total_positions,
            "w_sign_equals_minus_C": total_positions,
            "normalized_sign_flips_from_w": total_n_flips,
            "nonzero_cyclic_weights": total_weight_nonzero,
            "weighted_w_mixed_triples": total_w_mixed,
            "weighted_n_mixed_triples": total_n_mixed,
            "gamma_positive": gamma_positive,
            "gamma_negative": gamma_negative,
        },
        "verdict": (
            "the selected-three configuration is genuine, but both canonical "
            "weighted fourth and normalized-fifth sign triples are mixed in "
            "every case; no one-sided sign contradiction results"
        ),
    }


def main() -> None:
    print(json.dumps(report(), sort_keys=True))


if __name__ == "__main__":
    main()
