from k5_primitive_matching_verify import (
    AFFINE_FIXTURE_INPUTS,
    EXPECTED_SCAN_PAIRS,
    affine_resultant_fixture,
    one_direction_point,
    primitive_scan,
    verify_one_direction,
)


def test_exhaustive_primitive_scan() -> None:
    rows = primitive_scan()
    assert [(row["u"], row["v"]) for row in rows] == EXPECTED_SCAN_PAIRS
    assert all(row["upper_quotient"] != row["lower_quotient"] for row in rows)


def test_unbounded_forward_matching_boundary() -> None:
    for index in (0, 1, 10**6, 10**40):
        data = verify_one_direction(one_direction_point(index))
        assert data["coprime"]
        assert data["ratio_strip"]
        assert data["scale_remainder"] == 0
        assert data["upper_matching_remainder"] == 0
        assert data["lower_matching_remainder"] != 0
        assert data["equation_residual"] != 0


def test_target_scale_member_is_genuinely_large() -> None:
    data = verify_one_direction(one_direction_point(10**40))
    assert data["gap"] >= 10**120


def test_affine_resultant_two_direction_fixtures() -> None:
    rows = [affine_resultant_fixture(*values) for values in AFFINE_FIXTURE_INPUTS]
    assert rows[-1]["u"] == 73_847_134_203_073
    assert rows[-1]["v"] == 56_125_318_669_499
    assert all(row["upper_quotient"] != row["lower_quotient"] for row in rows)
