#!/usr/bin/env python3
"""Exact audit of the quadratic-strip / even-Runge-tail interface.

The script reconstructs the canonical rational square-root part for the live
even row ``k = 34``.  It uses ``Fraction`` and integer arithmetic
only.  In particular, it checks the coefficient-growth obstruction that
survives parity-aware bounds and the best constant fixed-divisor rescaling on
odd centers.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction


R = 17
K = 2 * R
QUADRATIC_LAST_GAP = 64
FIRST_COMPLEMENT_GAP = 65
RATIO_NUMERATOR = 1_218_443
RATIO_DENOMINATOR = 1_853_952
FOURTH_ROOT_LOWER = 1_041_616
FOURTH_ROOT_DENOMINATOR = 1_000_000


def poly_mul(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return out


def poly_sub(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * max(len(left), len(right))
    for i in range(len(out)):
        out[i] = (
            (left[i] if i < len(left) else Fraction(0))
            - (right[i] if i < len(right) else Fraction(0))
        )
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_eval(poly: list[int], value: int) -> int:
    out = 0
    for coefficient in reversed(poly):
        out = out * value + coefficient
    return out


def centered_polynomial(r: int) -> list[Fraction]:
    out = [Fraction(1)]
    for odd in range(1, 2 * r, 2):
        out = poly_mul(out, [Fraction(-(odd**2)), Fraction(0), Fraction(1)])
    return out


def square_root_part(source: list[Fraction], r: int) -> list[Fraction]:
    """The unique monic Q with degree(Q^2-source) < r."""

    out = [Fraction(0)] * (r + 1)
    out[r] = Fraction(1)
    for j in range(r - 1, -1, -1):
        deficit = poly_sub(poly_mul(out, out), source)
        coefficient = deficit[r + j] if r + j < len(deficit) else Fraction(0)
        out[j] = -coefficient / 2
    assert len(poly_sub(poly_mul(out, out), source)) <= r
    return out


def denominator_lcm(values: list[Fraction]) -> int:
    out = 1
    for value in values:
        out = math.lcm(out, value.denominator)
    return out


def strict_integer_root(bound: Fraction, exponent: int) -> int:
    """Largest d with d**exponent < bound."""

    lo, hi = 0, 1
    while hi**exponent * bound.denominator < bound.numerator:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**exponent * bound.denominator < bound.numerator:
            lo = mid
        else:
            hi = mid
    return lo


def audit() -> dict[str, object]:
    source = centered_polynomial(R)
    root_part = square_root_part(source, R)

    odd_square_sum = sum(odd**2 for odd in range(1, 2 * R, 2))
    formula_sum = R * (4 * R**2 - 1) // 3
    assert odd_square_sum == formula_sum
    assert root_part[R - 1] == 0
    assert root_part[R - 2] == -Fraction(R * (4 * R**2 - 1), 6)

    denominator = denominator_lcm(root_part)
    integral_root = [int(denominator * coefficient) for coefficient in root_part]
    assert all(Fraction(value) == denominator * coefficient
               for value, coefficient in zip(integral_root, root_part))

    rational_deficit = poly_sub(poly_mul(root_part, root_part), source)
    integral_deficit = [
        int(denominator**2 * coefficient) for coefficient in rational_deficit
    ]
    deficit_degree = max(i for i, value in enumerate(integral_deficit) if value)
    leading_deficit = abs(integral_deficit[deficit_degree])

    coefficient_a = sum(abs(value) for value in integral_root[:R])
    coefficient_e = sum(abs(value) for value in integral_deficit[: deficit_degree + 1])
    coefficient_f = sum(abs(value) for value in integral_deficit[:deficit_degree])
    minimal_certificate_threshold = max(
        K,
        2 * coefficient_a + 1,
        7 * coefficient_f + 1,
        10 * coefficient_e + 1,
    )

    # A degree-r integer polynomial on the progression 2a+1 has fixed divisor
    # equal to the gcd of its first r+1 values (finite-difference basis).
    odd_values = [poly_eval(integral_root, 2 * a + 1) for a in range(R + 1)]
    fixed_divisor = 0
    for value in odd_values:
        fixed_divisor = math.gcd(fixed_divisor, abs(value))
    assert all(poly_eval(integral_root, 2 * a + 1) % fixed_divisor == 0
               for a in range(-100, 101))

    d = FIRST_COMPLEMENT_GAP
    ratio_left = RATIO_NUMERATOR * K * d
    least_ratio_n = ratio_left // RATIO_DENOMINATOR + 1
    least_ratio_center = 2 * least_ratio_n + K + 1
    assert RATIO_DENOMINATOR * (least_ratio_n - 1) <= ratio_left
    assert ratio_left < RATIO_DENOMINATOR * least_ratio_n

    # Reproduce both halves of the equation-facing power window.  The exact
    # rational bracket for 4^(1/34) converts them to linear inequalities:
    #
    #   B*(n+d+k) < (A+1)*(n+k),
    #   A*(n+1) < B*(n+d+1).
    #
    # Their exact integer boundary points are n=1528 and n=1560.  Monotonicity
    # of these linear inequalities then gives the complete necessary interval,
    # not merely a lower bound on the center.
    root_lower = FOURTH_ROOT_LOWER
    root_upper = root_lower + 1
    root_denominator = FOURTH_ROOT_DENOMINATOR
    assert root_lower**K < 4 * root_denominator**K < root_upper**K
    window_least_n = 1528
    window_greatest_n = 1560
    assert root_denominator * (
        window_least_n - 1 + d + K
    ) >= root_upper * (window_least_n - 1 + K)
    assert root_denominator * (
        window_least_n + d + K
    ) < root_upper * (window_least_n + K)
    assert root_lower * (window_greatest_n + 1) < root_denominator * (
        window_greatest_n + d + 1
    )
    assert root_lower * (window_greatest_n + 2) >= root_denominator * (
        window_greatest_n + d + 2
    )
    assert (window_least_n - 1 + d + K) ** K > 4 * (
        window_least_n - 1 + K
    ) ** K
    assert (window_least_n + d + K) ** K <= 4 * (
        window_least_n + K
    ) ** K
    assert 4 * (window_greatest_n + 1) ** K <= (
        window_greatest_n + d + 1
    ) ** K
    assert 4 * (window_greatest_n + 2) ** K > (
        window_greatest_n + d + 2
    ) ** K
    window_least_center = 2 * window_least_n + K + 1
    window_greatest_center = 2 * window_greatest_n + K + 1

    # This is deliberately optimistic: it keeps only the leading deficit and
    # grants the full odd-center fixed divisor as a lattice step.
    leading_only_center = (
        10 * leading_deficit // (denominator * fixed_divisor) + 1
    )
    full_norm_center = (
        10 * coefficient_e // (denominator * fixed_divisor) + 1
    )
    assert window_greatest_center < leading_only_center

    # A general interval lcm satisfies B | L*(2k-2)!, so the coefficient of
    # d^(2k-1) in any uniform monomial upper bound cannot be smaller than
    # 1/(2k-2)!.  This is the most optimistic cutoff the resulting size
    # sandwich could ever produce at k=34.
    c = Fraction(RATIO_NUMERATOR, RATIO_DENOMINATOR)
    ideal_lcm_bound = (
        (c * K) ** K
        * math.factorial(2 * K - 2)
        / math.factorial(K - 1)
    )
    ideal_lcm_last_gap = strict_integer_root(ideal_lcm_bound, K - 1)

    assert 18 * QUADRATIC_LAST_GAP <= K**2
    assert K**2 < 18 * FIRST_COMPLEMENT_GAP
    assert minimal_certificate_threshold > K**2 // 18

    return {
        "row": {"r": R, "k": K},
        "quadratic_boundary": {
            "last_gap": QUADRATIC_LAST_GAP,
            "first_complement_gap": FIRST_COMPLEMENT_GAP,
            "18_last_gap": 18 * QUADRATIC_LAST_GAP,
            "k_squared": K**2,
            "18_first_complement_gap": 18 * FIRST_COMPLEMENT_GAP,
        },
        "first_correction": {
            "odd_square_sum": odd_square_sum,
            "q_r_minus_1": int(root_part[R - 1]),
            "q_r_minus_2": str(root_part[R - 2]),
            "structural_threshold_lower_bound": Fraction(
                R * (4 * R**2 - 1), 3
            ).numerator,
        },
        "canonical_certificate": {
            "minimal_denominator": denominator,
            "deficit_degree": deficit_degree,
            "leading_deficit_abs": leading_deficit,
            "A": coefficient_a,
            "E": coefficient_e,
            "F": coefficient_f,
            "minimal_threshold": minimal_certificate_threshold,
            "odd_center_fixed_divisor": fixed_divisor,
        },
        "sharp_ratio_boundary": {
            "d": d,
            "least_n": least_ratio_n,
            "least_center": least_ratio_center,
            "left": ratio_left,
            "predecessor_right": RATIO_DENOMINATOR * (least_ratio_n - 1),
            "right": RATIO_DENOMINATOR * least_ratio_n,
        },
        "equation_power_window": {
            "d": d,
            "root_lower_numerator": root_lower,
            "root_upper_numerator": root_upper,
            "root_denominator": root_denominator,
            "least_n": window_least_n,
            "greatest_n": window_greatest_n,
            "least_center": window_least_center,
            "greatest_center": window_greatest_center,
        },
        "parity_rescaling_obstruction": {
            "optimistic_leading_only_center": leading_only_center,
            "full_norm_center": full_norm_center,
        },
        "ideal_general_lcm_ceiling": {
            "last_gap_excluded_by_size_sandwich": ideal_lcm_last_gap,
            "first_gap_not_reached": ideal_lcm_last_gap + 1,
        },
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
