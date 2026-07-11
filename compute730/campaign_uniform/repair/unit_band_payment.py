#!/usr/bin/env python3
"""Exact arithmetic for paying the full high-valuation band ``s<r``.

Here ``s=max(2r-a,0)`` and ``q=p^a``.  The strict band forces
``r+1<=a``.  Maximality of the analytic block length therefore gives the
clean threshold ``X < 2 B^2 q^2``.  All computations below use integers or
``Fraction``.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt
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


def unit_band_envelope(a: int, r: int) -> bool:
    if a < 1 or r < 1:
        raise ValueError("require a,r>=1")
    return max(2 * r - a, 0) < r


def unit_band_exponent_clearance(a: int, r: int) -> bool:
    """Check the exact consequences ``a>=2`` and ``r+1<=a``."""

    if not unit_band_envelope(a, r):
        raise ValueError("tuple is outside the unit band")
    return a >= 2 and r + 1 <= a


def threshold_integer_floor(X: int, weight_upper: int) -> int:
    """Largest ``y`` with ``2*weight_upper*y^2<=X``."""

    if X < 0 or weight_upper < 1:
        raise ValueError("invalid threshold inputs")
    y = isqrt(X // (2 * weight_upper))
    while 2 * weight_upper * (y + 1) ** 2 <= X:
        y += 1
    while 2 * weight_upper * y**2 > X:
        y -= 1
    return y


def dyadic_unit_band_one_percent_certificate() -> dict[str, object]:
    X0 = 2**57
    M_upper = 2**77
    bit_length_upper = 78
    weight_upper = bit_length_upper**2
    Y_integer_lower = threshold_integer_floor(X0, weight_upper)
    threshold_lower = 2 * weight_upper * Y_integer_lower**2 <= X0
    threshold_upper = X0 < 2 * weight_upper * (Y_integer_lower + 1) ** 2
    sqrt_Y_floor = floor_nth_root(Y_integer_lower, 2)
    cuberoot_Y_floor = floor_nth_root(Y_integer_lower, 3)
    tail_for_four_branches = 4 * rational_tail_upper(Y_integer_lower)
    boundary_for_four_branches = Fraction(
        4
        * (
            ceil_nth_root(M_upper, 2)
            + bit_length_upper * ceil_nth_root(M_upper, 3)
        ),
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
        "cleared_margin": payment_upper.denominator
        - 100 * payment_upper.numerator,
    }


def main() -> None:
    certificate = dyadic_unit_band_one_percent_certificate()
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
