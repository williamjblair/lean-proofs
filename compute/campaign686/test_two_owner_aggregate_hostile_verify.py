from __future__ import annotations

from compute.campaign686.two_owner_aggregate_hostile_verify import (
    TARGET,
    aggregate_loss,
    cancellation_boundary_certificate,
    coarse_obstruction_certificate,
    finite_grouping_arithmetic_certificate,
    parse_lean_loss_table,
    pell_gcd_boundary_certificate,
    refined_cubic_boundary_certificate,
    report,
    row_pair_certificate,
    same_owner_boundary_certificate,
    source_gate_certificate,
    unit_bucket_abstract_certificate,
)


EXPECTED_LOSSES = {
    5: 108,
    7: 1_620,
    9: 136_080,
    11: 1_224_720,
    13: 242_494_560,
    15: 18_914_575_680,
}


def test_loss_table_is_recomputed_and_matches_lean() -> None:
    assert {k: aggregate_loss(k) for k in EXPECTED_LOSSES} == EXPECTED_LOSSES
    assert parse_lean_loss_table() == EXPECTED_LOSSES


def test_coarse_10_pow_16_obstruction_is_strict() -> None:
    certificate = coarse_obstruction_certificate()
    assert certificate["coarse_coefficient"] == 3_855_000_000_000_000
    assert certificate["bound"] == 10_000_000_000_000_000
    assert certificate["margin"] == 6_145_000_000_000_000
    assert certificate["strict"] is True


def test_all_610_pair_and_cutoff_certificates() -> None:
    certificate = row_pair_certificate()
    assert certificate["ordered_pair_count"] == 610
    assert {
        k: row["maximum_second_majorant"][0]
        for k, row in certificate["rows"].items()
    } == {
        5: 16_512,
        7: 751_248,
        9: 74_507_904,
        11: 8_634_643_200,
        13: 1_422_568_811_520,
        15: 368_002_448_916_480,
    }
    assert certificate["global_maximum_exact_generic"][0] < TARGET
    assert certificate["global_maximum_exact_cubic"][0] == (
        93_984_078_683_194_682_557_325_451_381_987_070_845_762_855_139_556_197_071_318_510_982_175_649_195_251_213_580_361_531_392_000_000_000
    )


def test_generic_gcd_cancellation_including_all_zero_boundaries() -> None:
    certificate = cancellation_boundary_certificate()
    assert certificate["premise_cases"] > 10_000
    assert min(
        certificate["m_zero"],
        certificate["b_zero"],
        certificate["K_zero"],
        certificate["D_zero"],
    ) > 0


def test_pell_gcd_divisibilities_include_signs_and_zero_data() -> None:
    certificate = pell_gcd_boundary_certificate()
    assert certificate["pell_cases"] > 1_000
    assert min(
        certificate["negative_delta"],
        certificate["zero_delta"],
        certificate["positive_delta"],
        certificate["P_zero"],
        certificate["Q_zero"],
        certificate["a_zero"],
        certificate["b_zero"],
    ) > 0


def test_refined_cubic_has_exact_factors_signs_and_zero_delta() -> None:
    certificate = refined_cubic_boundary_certificate()
    assert certificate["refined_cases"] > 10_000
    assert certificate["factor_three_needed_witness"] is not None
    assert min(
        certificate["negative_E"],
        certificate["zero_E"],
        certificate["positive_E"],
        certificate["negative_delta"],
        certificate["zero_delta"],
        certificate["positive_delta"],
        certificate["P_one"],
        certificate["Q_zero"],
        certificate["a_zero"],
    ) > 0


def test_same_owner_and_unit_clean_buckets() -> None:
    same = same_owner_boundary_certificate()
    units = unit_bucket_abstract_certificate()
    assert same["premise_cases"] > 0
    assert min(same["P_one_cases"], same["Q_one_cases"], same["both_one_cases"]) > 0
    assert min(
        units["both_unit_fixtures"],
        units["P_unit_only_fixtures"],
        units["Q_unit_only_fixtures"],
        units["both_unit_negative_delta"],
        units["both_unit_positive_delta"],
    ) > 0


def test_finite_grouping_arithmetic_is_proper_and_exact() -> None:
    certificate = finite_grouping_arithmetic_certificate()
    assert certificate["assignment_cases"] > 10_000
    assert min(
        certificate["both_clean_buckets_unit"],
        certificate["left_bucket_unit"],
        certificate["right_bucket_unit"],
    ) > 0


def test_source_gate_and_exact_nine_public_theorems() -> None:
    certificate = source_gate_certificate()
    assert certificate["source_sha256"] == (
        "35959fee7b3080b2d0a91885a7a465455fcbed4ead9ecc1d652024ec7eabe009"
    )
    assert certificate["forbidden"] == {}
    assert certificate["public_theorem_count"] == 9


def test_full_hostile_report() -> None:
    result = report()
    assert result["loss_table"]["lean"] == EXPECTED_LOSSES
    assert result["coarse_obstruction"]["strict"] is True
