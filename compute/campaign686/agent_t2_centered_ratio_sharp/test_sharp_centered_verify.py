from __future__ import annotations

from .sharp_centered_verify import (
    maximal_fixed_bracket_ratio_audit,
    root_bracket_audit,
    seven_tenths_bracket_incompatibility,
    seven_tenths_counterboundary,
    sharp_linear_boundary_audit,
)


def test_maximal_fixed_bracket_ratio_is_exact() -> None:
    assert maximal_fixed_bracket_ratio_audit() == {
        "numerator": 1_218_443,
        "denominator": 1_853_952,
        "maximal_cofactor_left": 3_707_904,
        "maximal_cofactor_right": 1_218_443,
        "clean_corollary": "23/35",
    }


def test_seven_term_root_bracket_is_exact() -> None:
    audit = root_bracket_audit(1_024)
    assert audit["partial_sum_numerator"] == 2_048_194_856_715_132_747_962_308_721
    assert audit["partial_sum_denominator"] == 512_000_000_000_000_000_000_000_000
    assert audit["excess_numerator"] == 194_856_715_132_747_962_308_721
    assert audit["excess_denominator"] == 512_000_000_000_000_000_000_000_000


def test_sharp_linear_boundary_starts_with_positive_k16_slack() -> None:
    audit = sharp_linear_boundary_audit(10_000)
    assert audit["samples"][0] == {"k": 16, "worst_case_slack": 4_609}


def test_seven_tenths_counterboundary_passes_all_power_windows() -> None:
    row = seven_tenths_counterboundary()
    assert (row["k"], row["n"], row["d"]) == (16, 175, 16)
    assert row["ten_n"] == 1_750 <= 1_792 == row["seven_kd"]
    assert row["centered_margin"] > 0
    assert row["lower_endpoint_margin"] >= 0
    assert row["upper_endpoint_margin"] >= 0
    assert row["is_equation"] is False


def test_seven_tenths_rational_bracket_requirements_are_incompatible() -> None:
    audit = seven_tenths_bracket_incompatibility()
    assert audit == {
        "root_lower_bound": "7/5",
        "linear_ceiling_numerator": 2_560,
        "linear_ceiling_denominator": 1_877,
        "strictly_incompatible": True,
    }
