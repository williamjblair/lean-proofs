#!/usr/bin/env python3
"""Independent hostile verifier for the #730 full strict-band payment.

Nothing is imported from the producer calculator or its near-band helpers.
All finite arithmetic uses integers or ``Fraction``.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd, isqrt
from typing import Any


ROWS_CHECK_BOUND = 512
X0 = 2**57
M_UPPER = 2**77
BIT_BOUND = 78
WEIGHT_BOUND = BIT_BOUND**2
Y_EXPECTED = 3_441_480


def nat_sub(left: int, right: int) -> int:
    if left < 0 or right < 0:
        raise ValueError("natural subtraction requires nonnegative inputs")
    return max(left - right, 0)


def paid_band(a: int, r: int) -> bool:
    if a < 1 or r < 1:
        raise ValueError("positive a,r required")
    return nat_sub(2 * r, a) < r


def band_boundary_audit(bound: int = ROWS_CHECK_BOUND) -> dict[str, Any]:
    paid = 0
    unpaid = 0
    prime_power_checks = 0
    for r in range(1, bound + 1):
        # Exact transition at a=r / a=r+1, including r=1.
        if paid_band(r, r):
            raise AssertionError((r, r, "boundary should be unpaid"))
        if not paid_band(r + 1, r):
            raise AssertionError((r + 1, r, "boundary should be paid"))
        for a in range(1, bound + 1):
            s = nat_sub(2 * r, a)
            envelope = s < r
            expected_paid = r + 1 <= a
            expected_unpaid = a <= r
            if envelope != expected_paid:
                raise AssertionError((a, r, s, envelope, expected_paid))
            if (s >= r) != expected_unpaid:
                raise AssertionError((a, r, s, expected_unpaid))
            if envelope:
                if a < 2 or r + 1 > a:
                    raise AssertionError("high-exponent clearance failed")
                paid += 1
                for p in (1, 2, 3, 5, 7, 11, 97):
                    if p ** (r + 1) > p**a:
                        raise AssertionError("prime-power monotonicity failed")
                    prime_power_checks += 1
            else:
                unpaid += 1
    expected_paid_count = bound * (bound - 1) // 2
    if paid != expected_paid_count:
        raise AssertionError((paid, expected_paid_count))

    # Reproduce the producer's exact 160-by-160 count independently.
    producer_grid_paid = sum(
        1
        for a in range(1, 161)
        for r in range(1, 161)
        if nat_sub(2 * r, a) < r
    )
    if producer_grid_paid != 12_720:
        raise AssertionError(producer_grid_paid)
    return {
        "grid_bound": bound,
        "paid_pairs": paid,
        "unpaid_pairs": unpaid,
        "prime_power_checks": prime_power_checks,
        "producer_160_grid_paid_pairs": producer_grid_paid,
        "first_power_boundary": {
            "a": 1,
            "r": 1,
            "s": 1,
            "paid": False,
        },
    }


def maximality_chain_audit() -> dict[str, Any]:
    """Reproduce every exact inequality in ``X < 2 W q^2``."""

    fixtures = 0
    smallest_final_margin: Fraction | None = None
    for p in (5, 7, 11, 97):
        for r in range(1, 7):
            pnext = p ** (r + 1)
            for a in range(r + 1, r + 6):
                q = p**a
                if pnext > q:
                    raise AssertionError("band power clearance failed")
                for n in (0, 1, pnext - 1, pnext, 2 * pnext + 3):
                    next_weight = max(Fraction(1, 1), Fraction(n + 1, pnext))
                    global_weight = next_weight + Fraction(1, 7)
                    x = q * (n + 1)

                    # Premises, all in exact arithmetic.
                    if x > q * (n + 1):
                        raise AssertionError
                    if not Fraction(n, 1) < pnext * next_weight:
                        raise AssertionError("maximality premise failed")
                    if next_weight < 1 or next_weight > global_weight:
                        raise AssertionError("weight premise failed")

                    block = pnext * next_weight
                    if block < 1:
                        raise AssertionError
                    if not Fraction(n + 1, 1) < 2 * block:
                        raise AssertionError("N+1 strict step failed")
                    bound_next = q * (2 * pnext * next_weight)
                    bound_global = q * (2 * pnext * global_weight)
                    bound_power = q * (2 * q * global_weight)
                    final_bound = 2 * global_weight * q**2
                    if not Fraction(x, 1) < bound_next:
                        raise AssertionError("residue-count composition failed")
                    if bound_next > bound_global:
                        raise AssertionError("global weight cast/order failed")
                    if bound_global > bound_power:
                        raise AssertionError("prime-power substitution failed")
                    if bound_power != final_bound:
                        raise AssertionError("final ring identity failed")
                    margin = final_bound - x
                    if margin <= 0:
                        raise AssertionError("final threshold is not strict")
                    smallest_final_margin = (
                        margin
                        if smallest_final_margin is None
                        else min(smallest_final_margin, margin)
                    )
                    fixtures += 1
    if fixtures != 4 * 6 * 5 * 5:
        raise AssertionError(fixtures)
    assert smallest_final_margin is not None
    return {
        "exact_fraction_fixtures": fixtures,
        "smallest_final_margin": [
            smallest_final_margin.numerator,
            smallest_final_margin.denominator,
        ],
    }


def dyadic_base(m: int) -> Fraction:
    return Fraction(2**m, 2 * (m + 21) ** 2)


def integer_cuberoot_newton(value: int) -> int:
    if value < 0:
        raise ValueError
    if value < 8:
        return 0 if value == 0 else 1
    estimate = 1 << ((value.bit_length() + 2) // 3)
    while True:
        updated = (2 * estimate + value // estimate**2) // 3
        if updated >= estimate:
            break
        estimate = updated
    while (estimate + 1) ** 3 <= value:
        estimate += 1
    while estimate**3 > value:
        estimate -= 1
    return estimate


def power_two_boundary_pair_envelope(m: int) -> tuple[int, int]:
    upper = 2 ** (m + 20)
    square_floor = isqrt(upper)
    square_ceiling = (
        square_floor if square_floor**2 == upper else square_floor + 1
    )
    cube_floor = integer_cuberoot_newton(upper)
    cube_ceiling = cube_floor if cube_floor**3 == upper else cube_floor + 1
    return square_ceiling + (m + 21) * cube_ceiling, 2**m


def dyadic_monotonicity_audit() -> dict[str, Any]:
    steps = 0
    minimum_threshold_margin: int | None = None
    minimum_cube_margin: int | None = None
    for m in range(57, 4097):
        threshold_margin = 2 * (m + 21) ** 2 - (m + 22) ** 2
        if threshold_margin <= 0 or not dyadic_base(m) < dyadic_base(m + 1):
            raise AssertionError((m, threshold_margin))
        cube_margin = 4 * (m + 21) ** 3 - (m + 22) ** 3
        if cube_margin <= 0:
            raise AssertionError((m, cube_margin))

        # Cleared positive-real boundary-envelope comparisons.  The square
        # term gains a factor 2 in M but a factor 4 in X^2.  The cuberoot
        # term is exactly the preceding cube inequality.
        square_left = 2 ** (m + 21) * 2 ** (2 * m)
        square_right = 2 ** (m + 20) * 2 ** (2 * (m + 1))
        if not square_left < square_right:
            raise AssertionError("square boundary envelope did not decrease")
        current_boundary = power_two_boundary_pair_envelope(m)
        next_boundary = power_two_boundary_pair_envelope(m + 1)
        if not (
            next_boundary[0] * current_boundary[1]
            < current_boundary[0] * next_boundary[1]
        ):
            raise AssertionError("exact ceiling boundary did not decrease")
        minimum_threshold_margin = (
            threshold_margin
            if minimum_threshold_margin is None
            else min(minimum_threshold_margin, threshold_margin)
        )
        minimum_cube_margin = (
            cube_margin
            if minimum_cube_margin is None
            else min(minimum_cube_margin, cube_margin)
        )
        steps += 1
    return {
        "steps_checked": steps,
        "m_range": [57, 4096],
        "minimum_threshold_cleared_margin": minimum_threshold_margin,
        "minimum_cuberoot_cleared_margin": minimum_cube_margin,
        "exact_ceiling_boundary_steps": steps,
        "endpoint_bit_bound": BIT_BOUND,
        "branch_ceiling_gap_at_X_eq_one": 2**19 - 380_808 - 19,
    }


def floor_root(value: int, degree: int) -> int:
    if value < 0 or degree < 1:
        raise ValueError
    low = 0
    high = 1
    while high**degree <= value:
        high *= 2
    while low + 1 < high:
        middle = (low + high) // 2
        if middle**degree <= value:
            low = middle
        else:
            high = middle
    return low


def ceil_root(value: int, degree: int) -> int:
    root = floor_root(value, degree)
    return root if root**degree == value else root + 1


def reciprocal_tail_envelope_audit(y: int) -> dict[str, Any]:
    """Check the rational relaxations used after the paper-level tail lemma."""

    square_floor = floor_root(y, 2)
    cube_floor = floor_root(y, 3)
    square_start = ceil_root(y, 2)
    if square_start <= 1 or cube_floor <= 0:
        raise AssertionError

    # Integral-test envelope for the a=2 tail.
    square_integral = Fraction(1, square_start - 1)
    square_relaxation = Fraction(2, square_floor)
    if square_integral > square_relaxation:
        raise AssertionError("square tail relaxation failed")

    # p <= y^(1/3): at most cube_floor bases, each at most 2/y.
    small_base_higher = Fraction(2 * cube_floor, y)
    small_base_relaxation = Fraction(2, cube_floor**2)
    if small_base_higher > small_base_relaxation:
        raise AssertionError("small-base higher tail failed")

    # p > y^(1/3): 2*sum_{n>=cube_floor+1}n^-3 is bounded by
    # 2*integral_{cube_floor}^infinity x^-3 dx = 1/cube_floor^2.
    large_base_integral = Fraction(1, cube_floor**2)
    higher_relaxation = Fraction(3, cube_floor**2)
    if small_base_relaxation + large_base_integral != higher_relaxation:
        raise AssertionError
    return {
        "square_floor": square_floor,
        "cube_floor": cube_floor,
        "square_integral_envelope": [
            square_integral.numerator,
            square_integral.denominator,
        ],
        "square_relaxation": [
            square_relaxation.numerator,
            square_relaxation.denominator,
        ],
        "small_base_higher_envelope": [
            small_base_higher.numerator,
            small_base_higher.denominator,
        ],
        "higher_relaxation": [
            higher_relaxation.numerator,
            higher_relaxation.denominator,
        ],
    }


def endpoint_audit() -> dict[str, Any]:
    y = isqrt(X0 // (2 * WEIGHT_BOUND))
    while 2 * WEIGHT_BOUND * (y + 1) ** 2 <= X0:
        y += 1
    while 2 * WEIGHT_BOUND * y**2 > X0:
        y -= 1
    if y != Y_EXPECTED:
        raise AssertionError(y)
    threshold_lower_margin = X0 - 2 * WEIGHT_BOUND * y**2
    threshold_upper_margin = 2 * WEIGHT_BOUND * (y + 1) ** 2 - X0
    if threshold_lower_margin < 0 or threshold_upper_margin <= 0:
        raise AssertionError

    sqrt_y = floor_root(y, 2)
    cbrt_y = floor_root(y, 3)
    if (sqrt_y, cbrt_y) != (1_855, 150):
        raise AssertionError((sqrt_y, cbrt_y))
    sqrt_m_ceiling = ceil_root(M_UPPER, 2)
    cbrt_m_ceiling = ceil_root(M_UPPER, 3)
    if (sqrt_m_ceiling, cbrt_m_ceiling) != (388_736_063_997, 53_264_341):
        raise AssertionError((sqrt_m_ceiling, cbrt_m_ceiling))

    tail = 4 * (Fraction(2, sqrt_y) + Fraction(3, cbrt_y**2))
    boundary_pair_count = sqrt_m_ceiling + BIT_BOUND * cbrt_m_ceiling
    boundary = Fraction(4 * boundary_pair_count, X0)
    payment = tail + boundary
    expected_payment = Fraction(
        121_726_379_332_007_683_003,
        25_062_531_926_316_810_240_000,
    )
    if tail != Fraction(3_371, 695_625):
        raise AssertionError(tail)
    if boundary != Fraction(392_890_682_595, 36_028_797_018_963_968):
        raise AssertionError(boundary)
    if payment != expected_payment or payment >= Fraction(1, 100):
        raise AssertionError(payment)
    cleared_margin = payment.denominator - 100 * payment.numerator
    if cleared_margin != 12_889_893_993_116_041_939_700:
        raise AssertionError(cleared_margin)

    tail_audit = reciprocal_tail_envelope_audit(y)
    return {
        "X0": X0,
        "M_upper": M_UPPER,
        "bit_bound": BIT_BOUND,
        "weight_bound": WEIGHT_BOUND,
        "Y": y,
        "threshold_lower_margin": threshold_lower_margin,
        "threshold_upper_margin": threshold_upper_margin,
        "sqrt_Y_floor": sqrt_y,
        "cuberoot_Y_floor": cbrt_y,
        "sqrt_M_ceiling": sqrt_m_ceiling,
        "cuberoot_M_ceiling": cbrt_m_ceiling,
        "tail": [tail.numerator, tail.denominator],
        "boundary_pair_count": boundary_pair_count,
        "boundary": [boundary.numerator, boundary.denominator],
        "payment": [payment.numerator, payment.denominator],
        "cleared_margin": cleared_margin,
        "tail_envelope_audit": tail_audit,
    }


def report() -> dict[str, Any]:
    return {
        "band_boundaries": band_boundary_audit(),
        "maximality_chain": maximality_chain_audit(),
        "dyadic_monotonicity": dyadic_monotonicity_audit(),
        "endpoint": endpoint_audit(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
