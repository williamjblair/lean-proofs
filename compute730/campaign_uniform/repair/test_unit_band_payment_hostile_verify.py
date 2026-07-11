from fractions import Fraction

from compute730.campaign_uniform.repair.unit_band_payment_hostile_verify import (
    band_boundary_audit,
    dyadic_monotonicity_audit,
    endpoint_audit,
    maximality_chain_audit,
)


def test_exact_nat_subtraction_partition() -> None:
    result = band_boundary_audit()
    assert result["paid_pairs"] == 130_816
    assert result["unpaid_pairs"] == 131_328
    assert result["producer_160_grid_paid_pairs"] == 12_720
    assert result["first_power_boundary"]["paid"] is False


def test_maximality_chain_is_exact() -> None:
    result = maximality_chain_audit()
    assert result["exact_fraction_fixtures"] == 600
    assert Fraction(*result["smallest_final_margin"]) > 0


def test_dyadic_envelopes_move_in_the_claimed_directions() -> None:
    result = dyadic_monotonicity_audit()
    assert result["steps_checked"] == 4_040
    assert result["exact_ceiling_boundary_steps"] == 4_040
    assert result["minimum_threshold_cleared_margin"] > 0
    assert result["minimum_cuberoot_cleared_margin"] > 0
    assert result["branch_ceiling_gap_at_X_eq_one"] == 143_461


def test_endpoint_rebuild() -> None:
    result = endpoint_audit()
    assert result["Y"] == 3_441_480
    assert result["sqrt_Y_floor"] == 1_855
    assert result["cuberoot_Y_floor"] == 150
    assert result["sqrt_M_ceiling"] == 388_736_063_997
    assert result["cuberoot_M_ceiling"] == 53_264_341
    assert result["tail"] == [3_371, 695_625]
    assert result["boundary"] == [392_890_682_595, 36_028_797_018_963_968]
    assert result["payment"] == [
        121_726_379_332_007_683_003,
        25_062_531_926_316_810_240_000,
    ]
    assert result["cleared_margin"] == 12_889_893_993_116_041_939_700
