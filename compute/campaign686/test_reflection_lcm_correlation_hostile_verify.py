from math import factorial

from compute.campaign686.reflection_lcm_correlation_hostile_verify import (
    DEEP_16,
    DEEP_17,
    EVEN_SYNTHETIC,
    ODD_SYNTHETIC,
    SMOOTH_REFLECTION_984,
    center,
    compression_flags,
    concentration_grid,
    conditional_composition_scan,
    exact_equation,
    named_fixture_report,
    owner_rows,
    reflection_lcm,
    reflection_product,
    reflection_values,
    row_passes,
    small_lcm,
    structural_report,
)


def test_positive_reflection_interval_and_lcm() -> None:
    assert reflection_values(5, 7) == [11, 9, 7, 5, 3]
    assert reflection_lcm(5, 7) == 3_465
    assert reflection_product(5, 7) == 10_395


def test_raw_lcm_and_product_rhs_are_incomparable() -> None:
    result = structural_report()
    directions = [
        entry["lcm_rhs_lt_product_rhs"]
        for entry in result["flags"].values()
    ]
    assert any(directions) and not all(directions)
    odd = result["flags"][str(ODD_SYNTHETIC)]
    assert odd["lcm_rhs_divides_product_rhs"] is False
    assert odd["product_rhs_divides_lcm_rhs"] is False


def test_prefix_fixtures_do_not_supply_the_equation_premise() -> None:
    assert all(row_passes(*DEEP_17, row) for row in range(1, 17))
    assert not row_passes(*DEEP_17, 17)
    assert not exact_equation(*DEEP_17)
    assert all(row_passes(*DEEP_16, row) for row in range(1, 16))
    assert not row_passes(*DEEP_16, 16)
    assert not exact_equation(*DEEP_16)


def test_synthetic_points_only_demonstrate_the_reflected_obstruction() -> None:
    for point in (SMOOTH_REFLECTION_984, EVEN_SYNTHETIC, ODD_SYNTHETIC):
        flags = compression_flags(point)
        assert flags["equation"] is False
        assert flags["reflection_congruence"] is True
        assert flags["product_compression"] is True
        assert flags["lcm_compression"] is True


def test_named_aligned_owner_rows() -> None:
    expected = {
        SMOOTH_REFLECTION_984: [(1_489, 499, 486), (4_271, 597, 388)],
        EVEN_SYNTHETIC: [(5, 13, 4), (59, 7, 10)],
        ODD_SYNTHETIC: [(19, 12, 6), (31, 10, 8), (41, 13, 5), (43, 13, 5)],
    }
    for point, triples in expected.items():
        rows = [row for row in owner_rows(*point) if row.residual_exponent]
        assert [
            (row.prime, row.lower_owner, row.upper_owner) for row in rows
        ] == triples
        assert all(row.reflected for row in rows)


def test_d_one_equations_are_vacuous_and_outside_d_ge_k() -> None:
    report = named_fixture_report()
    assert report["d_eq_one_telescopes"] == [
        {"point": [9, 2, 1], "residual_rows": 0},
        {"point": [15, 4, 1], "residual_rows": 0},
    ]


def test_nonreflected_residuals_are_absorbed_by_small_lcm() -> None:
    result = conditional_composition_scan()
    assert result["premise_points"] == 499
    assert result["nonzero_residual_rows"] > 0
    assert result["nonreflected_nonzero_rows"] > 0


def test_threshold_arithmetic() -> None:
    assert small_lcm(16) == 360_360
    exact = 3 * factorial(15) * small_lcm(16)
    uniform = 5 * factorial(15) * small_lcm(16)
    exact_threshold = (exact + 18) // 19
    uniform_threshold = (uniform + 18) // 19
    assert 19 * (exact_threshold - 1) < exact <= 19 * exact_threshold
    assert exact_threshold < uniform_threshold


def test_center_values_and_concentration_grid() -> None:
    assert center(*DEEP_17) == 6_359_517
    assert center(*DEEP_16) == 97_526
    assert center(*SMOOTH_REFLECTION_984) == 6_359_519
    assert concentration_grid()["maximum_owner_concentration_checks"] == 17_271
