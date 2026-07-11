from __future__ import annotations

from fractions import Fraction

import pytest

from compute730.campaign_uniform.repair.unit_band_payment import (
    dyadic_unit_band_one_percent_certificate,
    threshold_integer_floor,
    unit_band_envelope,
    unit_band_exponent_clearance,
)


def test_unit_band_clearance_exhaustive_boundary_grid() -> None:
    checked = 0
    for a in range(1, 161):
        for r in range(1, 161):
            if unit_band_envelope(a, r):
                checked += 1
                assert unit_band_exponent_clearance(a, r)
    assert checked == 12_720


def test_unit_band_strictly_extends_the_half_band() -> None:
    assert unit_band_envelope(4, 3)
    assert not 2 * max(2 * 3 - 4, 0) < 3
    assert not unit_band_envelope(1, 1)


def test_prime_power_clearance_exact_grid() -> None:
    for p in (2, 3, 5, 7, 11, 97):
        for a in range(1, 20):
            for r in range(1, 20):
                if unit_band_envelope(a, r):
                    assert p ** (r + 1) <= p**a


def test_threshold_floor_boundary() -> None:
    X = 2**57
    W = 78**2
    Y = threshold_integer_floor(X, W)
    assert Y == 3_441_480
    assert 2 * W * Y**2 <= X
    assert X < 2 * W * (Y + 1) ** 2


def test_endpoint_roots_and_payment() -> None:
    certificate = dyadic_unit_band_one_percent_certificate()
    assert certificate["threshold_lower"]
    assert certificate["threshold_upper"]
    assert certificate["sqrt_Y_floor"] == 1_855
    assert certificate["cuberoot_Y_floor"] == 150
    assert certificate["tail_for_four_branches"] == Fraction(3371, 695625)
    assert certificate["payment_upper"] == Fraction(
        121726379332007683003,
        25062531926316810240000,
    )
    assert certificate["payment_below_one_percent"]
    assert certificate["cleared_margin"] == 12_889_893_993_116_041_939_700


def test_invalid_inputs_rejected() -> None:
    with pytest.raises(ValueError):
        unit_band_envelope(0, 1)
    with pytest.raises(ValueError):
        threshold_integer_floor(1, 0)
