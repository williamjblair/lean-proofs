from compute.campaign686.agent_t1_high_order_window.high_order_window_verify import (
    composition_grid,
    determinant_scan,
    local_identity_grid,
    ordered_view_scan,
    report,
)


def test_local_sixth_seventh_identities() -> None:
    assert local_identity_grid() == {
        "exact_local_sixth_seventh_checks": 9_000,
        "signed_checks": 7_380,
        "component_three_checks": 3_000,
    }


def test_cyclic_composition_grid() -> None:
    grid = composition_grid()
    assert grid["exact_composition_checks"] == 74_520
    assert grid["component_three_checks"] == 49_680
    assert grid["negative_loss_checks"] == 37_260


def test_all_ordered_target_views() -> None:
    scan = ordered_view_scan()
    assert scan["totals"]["ordered_views"] == 6_210
    assert scan["totals"]["generic_views"] == 6_156
    assert scan["totals"]["center_reflected_views"] == 54
    assert scan["totals"]["sixth_W6_sign_certificates"] == 6_210
    assert scan["totals"]["seventh_root_inside_views"] == 144
    assert scan["totals"]["seventh_root_outside_sign_certificates"] == 6_066


def test_row_maxima_are_frozen() -> None:
    rows = ordered_view_scan()["by_row"]
    assert rows["5"]["max_C6"] == 31_560_952_364_928
    assert rows["5"]["max_C7"] == 100_027_008_273_024
    assert rows["15"]["max_C6"] == 1_168_644_904_444_759_933_478_206_080
    assert rows["15"]["max_C7"] == 4_518_604_044_513_372_125_636_553_600


def test_seventh_leading_determinant_is_everywhere_mixed() -> None:
    scan = determinant_scan()["totals"]
    assert scan == {
        "unordered_triples": 1_035,
        "exact_lambda_cells": 1_105,
        "mixed_weight_cells": 1_105,
        "one_sided_weight_cells": 0,
        "rational_boundaries": 2_140,
        "mixed_boundaries": 2_138,
        "all_zero_boundaries": 2,
        "one_sided_boundaries": 0,
        "zero_primitive_weights": 33,
        "equal_root_pairs": 33,
        "equal_root_pairs_inside_window": 2,
        "minimum_unequal_root_separation": "800/789",
    }


def test_scaling_verdict_is_strict_in_every_row() -> None:
    scaling = report()["scaling"]
    assert scaling["existing_bound"] == "P^2 < U_k*d"
    for row in scaling["row_comparison"].values():
        assert row["sixth_is_weaker_than_existing_square_bound"]
        assert row["seventh_is_weaker_than_existing_square_bound"]
        assert row["existing_square_bound_at_target"] < row["sixth_bound_rhs_at_target"]
        assert row["existing_square_bound_at_target"] < row["seventh_square_bound_rhs_at_target"]
