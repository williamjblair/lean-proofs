from fractions import Fraction

from compute730.campaign_uniform.repair.half_band_payment import (
    dyadic_half_band_one_percent_certificate,
    half_band_envelope,
    half_band_exponent_clearance,
)


def test_half_band_forces_the_sharpened_exponent_clearance() -> None:
    for a in range(1, 80):
        for r in range(1, 80):
            if half_band_envelope(a, r):
                assert half_band_exponent_clearance(a, r)


def test_half_band_is_strictly_wider_than_old_rational_envelope() -> None:
    # 12s<5r was the old paid envelope; 2s<r is the new one.
    a, r = 19, 12
    s = max(2 * r - a, 0)
    assert not 12 * s < 5 * r
    assert half_band_envelope(a, r)


def test_exact_half_band_endpoint_payment() -> None:
    certificate = dyadic_half_band_one_percent_certificate()
    assert certificate["weight_upper"] == Fraction(8281, 1)
    assert certificate["Y_integer_lower"] == 937_824
    assert certificate["threshold_lower"]
    assert certificate["threshold_upper"]
    assert certificate["sqrt_Y_floor"] == 968
    assert certificate["cuberoot_Y_floor"] == 97
    assert certificate["payment_upper"] == Fraction(
        391756066143304555403,
        41018389089323268964352,
    )
    assert certificate["payment_below_one_percent"]
    assert certificate["cleared_margin"] == 1842782474992813424052
