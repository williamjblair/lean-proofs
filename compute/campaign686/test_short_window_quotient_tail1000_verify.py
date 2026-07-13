from compute.campaign686.short_window_quotient_tail1000_verify import (
    EXPECTED_COEFFICIENT_TABLE_SHA256,
    EXPECTED_R5_TARGET_TABLE_SHA256,
    assert_report,
    coefficient_table_report,
    cutoff_report,
    fifth_decomposition_report,
    report,
    support_subset_ledger,
    tail_hensel_replay_report,
)


def test_independent_coefficient_table_and_reflection_symmetry() -> None:
    table = coefficient_table_report()
    assert table["owner_rows"] == 60
    assert table["reflection_checks"] == 60
    assert table["sha256"] == EXPECTED_COEFFICIENT_TABLE_SHA256
    assert table["rows"][:5] == [
        {"k": 5, "owner": 1, "coefficients": [24, 50, 35, 10, 1]},
        {"k": 5, "owner": 2, "coefficients": [-6, -5, 5, 5, 1]},
        {"k": 5, "owner": 3, "coefficients": [4, 0, -5, 0, 1]},
        {"k": 5, "owner": 4, "coefficients": [-6, 5, 5, -5, 1]},
        {"k": 5, "owner": 5, "coefficients": [24, -50, 35, -10, 1]},
    ]


def test_reduced_fifth_decomposition_and_target_degree_ledger() -> None:
    fifth = fifth_decomposition_report()
    assert fifth["signed_fixture_checks"] == 8_640
    assert fifth["ordered_target_views"] == 6_210
    assert fifth["target_decomposition_checks"] == 18_630
    assert fifth["linear_nonzero_views"] == 6_210
    assert fifth["minimum_abs_linear"] == 27_818_640
    assert fifth["maximum_abs_linear"] == (
        277_726_044_983_936_190_440_323_571_987_184_359_571_456_000
    )
    assert fifth["quadratic_nonzero_views"] == 6_156
    assert fifth["quadratic_zero_views"] == 54
    assert fifth["all_quadratic_zeros_are_oriented_center_reflections"] is True
    assert fifth["target_table_sha256"] == EXPECTED_R5_TARGET_TABLE_SHA256
    assert all(
        row["owner"] == (row["k"] + 1) // 2
        and row["left"] + row["right"] == row["k"] + 1
        and row["R2"] == 0
        for row in fifth["quadratic_zero_cases"]
    )


def test_all_2603_historical_two_zero_placements_close_at_tail1000() -> None:
    cutoff = cutoff_report()
    assert cutoff["placements"] == 2_603
    assert cutoff["zero_weight_contradictions"] == 27
    assert cutoff["numeric_records"] == 2_576
    assert cutoff["numeric_closed_at_10_120"] == 2_294
    assert cutoff["numeric_closed_at_10_1000"] == 2_576
    assert cutoff["all_closed_at_10_1000"] is True
    assert cutoff["new_numeric_closures_beyond_10_120"] == 282
    assert cutoff["open_at_10_130"] == 2
    assert cutoff["open_at_10_131"] == 0
    assert [row["placements"] for row in cutoff["rows"]] == [
        18,
        75,
        196,
        405,
        726,
        1_183,
    ]
    assert [row["zero_weight_contradictions"] for row in cutoff["rows"]] == [
        2,
        3,
        4,
        5,
        6,
        7,
    ]
    assert [
        row["new_numeric_closures_beyond_10_120"] for row in cutoff["rows"]
    ] == [0, 0, 0, 0, 0, 282]
    assert [row["maximum_Dmin_digits"] for row in cutoff["rows"]] == [
        28,
        45,
        67,
        82,
        107,
        131,
    ]


def test_every_numeric_cutoff_has_the_exact_integer_square_boundary() -> None:
    cutoff = cutoff_report()
    numeric = [
        record for record in cutoff["records"] if record["kind"] == "numeric_cutoff"
    ]
    assert len(numeric) == 2_576
    assert all(
        record["sharp_lower_check"]
        <= record["majorant"]
        < record["sharp_upper_check"]
        for record in numeric
    )
    assert all(record["closed_at_10_1000"] for record in numeric)


def test_sharp_131_digit_maximum_and_two_reflected_attainers() -> None:
    cutoff = cutoff_report()
    assert cutoff["maximum_Dmin"] == (
        15_855_065_204_701_151_051_583_570_030_869_346_558_944_133_017_237_495_757_148_583_758_790_408_893_113_026_893_763_598_192_399_346_355_860_926_337_293_559_495_864_273_423_092
    )
    maximum = cutoff["maximum_records"]
    assert len(maximum) == 2
    assert [
        (record["owners"], record["zero_owners"], record["remaining_owner"])
        for record in maximum
    ] == [
        ([1, 2, 15], [1, 2], 15),
        ([1, 14, 15], [14, 15], 1),
    ]
    assert maximum[0]["remaining_weight"] == maximum[1]["remaining_weight"]
    assert maximum[0]["gamma"] == maximum[1]["gamma"]
    assert maximum[0]["coefficient_lcm"] == maximum[1]["coefficient_lcm"]
    assert maximum[0]["majorant"] == maximum[1]["majorant"]


def test_support_subset_ledger_separates_27_reflected_closures() -> None:
    support = support_subset_ledger()
    assert [
        row["support_subsets_size_at_least_three"] for row in support["rows"]
    ] == [16, 99, 466, 1_981, 8_100, 32_647]
    assert [row["closed_center_reflected"] for row in support["rows"]] == [
        2,
        3,
        4,
        5,
        6,
        7,
    ]
    assert [row["open_non_center_reflected"] for row in support["rows"]] == [
        14,
        96,
        462,
        1_976,
        8_094,
        32_640,
    ]
    assert support == {
        "rows": support["rows"],
        "support_subsets_size_at_least_three": 43_309,
        "closed_center_reflected": 27,
        "open_non_center_reflected": 43_282,
    }


def test_frozen_fifth_hensel_constructor_replays_above_tail1000() -> None:
    replay = tail_hensel_replay_report()
    assert replay["exponent"] == 166
    assert replay["gap_digits"] == 1_004
    assert replay["n_digits"] == 6_023
    assert replay["all_third_obstructions_nonzero"] is True
    assert replay["all_local_and_reduced_remainders_zero"] is True
    assert replay["block_equation"] is False
    assert replay["upper_window_holds"] is False


def test_full_report_self_audit_and_scope_guard() -> None:
    result = report()
    assert_report(result)
    assert "historical quotient-zero arithmetic only" in result["scope"]
    assert "no all-nonzero closure is claimed" in result["scope"]
