from .bounded_lift_sieve import coefficient_ball_bound


def test_height_20000_coefficient_ball() -> None:
    result = coefficient_ball_bound(20000, 1077517601)
    assert result["curve_height_power_of_two_exponent"] == 15
    assert result["delta_power_of_two_exponent"] == 31
    assert result["canonical_height_upper_rational"] == "181/3"
    assert result["squared_coefficient_norm_upper_rational"] == "36200/129"
    assert result["squared_coefficient_norm_bound"] == 280
