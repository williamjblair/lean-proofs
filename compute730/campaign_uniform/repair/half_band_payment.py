#!/usr/bin/env python3
"""Exact arithmetic for paying the enlarged #730 affine band ``2s<r``.

The stronger progression obstruction extends beyond the old
``(kappa_p+1/12)r`` cut.  The same valuation-rarity argument still pays the
uniform envelope ``s<r/2`` below one percent.  This file reproduces every
finite constant in that enlarged payment with integers and ``Fraction``.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compute730.campaign_uniform.repair.near_affine_payment import (
    ceil_nth_root,
    floor_nth_root,
    rational_tail_upper,
)


def half_band_envelope(a: int, r: int) -> bool:
    if a < 1 or r < 1:
        raise ValueError("require a,r>=1")
    return 2 * max(2 * r - a, 0) < r


def half_band_exponent_clearance(a: int, r: int) -> bool:
    """Check the exact consequences ``3r<2a`` and ``6(r+1)<7a``."""

    if not half_band_envelope(a, r):
        raise ValueError("tuple is outside the half band")
    return a >= 2 and 3 * r < 2 * a and 6 * (r + 1) < 7 * a


def _threshold_integer_floor(X: int, weight_upper: Fraction) -> int:
    """Largest ``y`` with ``y^13 (2W)^6 <= X^6``."""

    target = Fraction(X**6, 1) / (2 * weight_upper) ** 6
    low, high = 0, 1
    while Fraction(high**13, 1) <= target:
        high *= 2
    while low + 1 < high:
        middle = (low + high) // 2
        if Fraction(middle**13, 1) <= target:
            low = middle
        else:
            high = middle
    return low


def dyadic_half_band_one_percent_certificate() -> dict[str, object]:
    X0 = 2**57
    M_upper = 2**77
    bit_length_upper = 78
    weight_upper = Fraction((7 * bit_length_upper) ** 2, 6**2)
    Y_integer_lower = _threshold_integer_floor(X0, weight_upper)
    threshold_lower = Fraction(Y_integer_lower**13, 1) * (
        2 * weight_upper
    ) ** 6 <= Fraction(X0**6, 1)
    threshold_upper = Fraction((Y_integer_lower + 1) ** 13, 1) * (
        2 * weight_upper
    ) ** 6 > Fraction(X0**6, 1)
    sqrt_Y_floor = floor_nth_root(Y_integer_lower, 2)
    cuberoot_Y_floor = floor_nth_root(Y_integer_lower, 3)
    tail_for_four_branches = 4 * rational_tail_upper(Y_integer_lower)
    boundary_for_four_branches = Fraction(
        4 * (ceil_nth_root(M_upper, 2) + bit_length_upper * ceil_nth_root(M_upper, 3)),
        X0,
    )
    payment_upper = tail_for_four_branches + boundary_for_four_branches
    return {
        "X0": X0,
        "M_upper": M_upper,
        "bit_length_upper": bit_length_upper,
        "weight_upper": weight_upper,
        "Y_integer_lower": Y_integer_lower,
        "threshold_lower": threshold_lower,
        "threshold_upper": threshold_upper,
        "sqrt_Y_floor": sqrt_Y_floor,
        "cuberoot_Y_floor": cuberoot_Y_floor,
        "tail_for_four_branches": tail_for_four_branches,
        "boundary_for_four_branches": boundary_for_four_branches,
        "payment_upper": payment_upper,
        "payment_below_one_percent": payment_upper < Fraction(1, 100),
        "cleared_margin": payment_upper.denominator - 100 * payment_upper.numerator,
    }


def main() -> None:
    certificate = dyadic_half_band_one_percent_certificate()
    serializable = {
        key: (
            f"{value.numerator}/{value.denominator}"
            if isinstance(value, Fraction)
            else value
        )
        for key, value in certificate.items()
    }
    print(json.dumps(serializable, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
