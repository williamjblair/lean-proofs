from compute.campaign686.three_bucket_zero_exclusion_repair_hostile_verify import (
    CROSS_BOUND,
    HISTORICAL_FAILED_SOURCE_SHA,
    THIRD_BOUND,
    finite_row_report,
    forbidden_source_report,
    freeze_report,
    hostile_boundary_report,
    numeric_cutoff_report,
    public_surface_report,
    report,
)


EXPECTED_ROWS = {
    5: (60, 691_200, [1, 5, 2], 75_600, [1, 5, 2]),
    7: (210, 1_646_023_680, [1, 7, 2], 8_769_600, [1, 7, 2]),
    9: (504, 10_180_055_531_520, [1, 9, 2], 1_190_689_920, [1, 9, 2]),
    11: (
        990,
        138_849_151_795_200_000,
        [1, 11, 2],
        206_607_931_200,
        [1, 11, 2],
    ),
    13: (
        1_716,
        3_691_052_156_423_503_872_000,
        [1, 13, 2],
        45_893_854_955_520,
        [1, 13, 2],
    ),
    15: (
        2_730,
        174_368_230_097_267_947_732_992_000,
        [1, 15, 2],
        12_847_056_696_714_240,
        [1, 15, 2],
    ),
}


def test_repaired_and_historical_boundaries_are_frozen_separately() -> None:
    frozen = freeze_report()
    assert frozen["repaired_all_match"] is True
    assert frozen["historical_audit_all_match"] is True
    assert frozen["historical_failed_source_sha"] == HISTORICAL_FAILED_SOURCE_SHA
    assert frozen["current_source_sha"] != HISTORICAL_FAILED_SOURCE_SHA
    assert frozen["historical_fail_report_preserved"] is True


def test_every_public_declaration_and_theorem_is_enumerated() -> None:
    surface = public_surface_report()
    assert surface["public_declarations"] == 16
    assert surface["public_theorems_and_lemmas"] == 8
    assert surface["theorem_names"] == [
        "target_three_bucket_zero_table_certificate",
        "target_three_bucket_zero_coefficient_certificate",
        "three_bucket_zero_target_numeric_cutoff",
        "three_bucket_zero_gap_lt_cutoff_of_target_coefficients",
        "targetThreeBucketSecondObstruction_swap",
        "targetThreeBucketThirdObstruction_swap",
        "target_three_bucket_designated_zero_gap_lt",
        "target_three_bucket_all_second_obstructions_nonzero",
    ]


def test_all_six_rows_and_6210_ordered_triples_reconstruct_exactly() -> None:
    result = finite_row_report()
    assert result["ordered_distinct_owner_triples"] == 6_210
    assert result["zero_cross_cases"] == 0
    assert result["zero_third_cases"] == 0
    for row in result["rows"]:
        expected = EXPECTED_ROWS[row["k"]]
        assert (
            row["ordered_distinct_owner_triples"],
            row["maximum_cross_numerator"],
            row["maximum_cross_case"],
            row["maximum_third_coefficient"],
            row["maximum_third_case"],
        ) == expected


def test_cross_third_swap_and_cyclic_identities_cover_every_triple() -> None:
    result = finite_row_report()
    assert result["cross_identity_checks"] == 6_210
    assert result["third_identity_checks"] == 6_210
    assert result["second_swap_checks"] == 6_210
    assert result["third_swap_checks"] == 6_210
    assert result["cyclic_designated_zero_checks"] == 18_630


def test_exact_cutoff_and_margin_reproduce() -> None:
    numeric = numeric_cutoff_report()
    assert numeric["cross_bound"] == CROSS_BOUND == 10**30
    assert numeric["third_bound"] == THIRD_BOUND == 10**18
    assert numeric["majorant"] < numeric["cutoff"] == 10**120
    assert numeric["cutoff_margin_floor"] == 7


def test_hostile_mutations_hit_every_load_bearing_boundary() -> None:
    hostile = hostile_boundary_report()
    assert hostile["owner_collision"]["cross"] == 0
    assert hostile["owner_collision"]["third"] == 0
    assert hostile["outside_target_row"]["k"] == 17
    assert hostile["outside_target_row"]["cross_exceeds_bound"] is True
    assert hostile["outside_target_row"]["third_exceeds_bound"] is True
    assert hostile["drop_pairwise_coprime"]["all_divisibility_premises"] is True
    assert hostile["drop_pairwise_coprime"]["packing_conclusion"] is False
    assert hostile["replace_g4_by_g3"]["g4_conclusion"] is True
    assert hostile["replace_g4_by_g3"]["g3_conclusion"] is False
    assert all(item["large_gap_hypothesis"] is False for item in hostile["d_eq_one"])


def test_forbidden_construct_gate_is_clean() -> None:
    forbidden = forbidden_source_report()
    assert forbidden["clean"] is True
    assert forbidden["hits"] == {}


def test_final_scope_is_partial_but_safe_to_integrate() -> None:
    result = report()
    assert result["verdict"] == "PASS repaired candidate"
    assert result["safe_to_integrate"] is True
    assert result["closes_zero_branch_only"] is True
    assert result["closes_nonzero_branch"] is False
    assert result["closes_erdos_686"] is False
