from compute.campaign686.fifth_quotient_short_window_verify import report


def test_exact_ledger_counts_and_zero_sets() -> None:
    ledger = report()["ledger"]
    assert ledger["totals"] == {
        "nonreflected_triples": 1008,
        "cyclic_positions": 3024,
        "r1_zero": 0,
        "r2_zero": 0,
        "critical_points_inside": 0,
        "endpoint_sign_changes": 0,
        "decomposition_checks": 12096,
    }
    assert [row["nonreflected_triples"] for row in ledger["rows"]] == [
        8,
        32,
        80,
        160,
        280,
        448,
    ]
    assert [row["cyclic_positions"] for row in ledger["rows"]] == [
        24,
        96,
        240,
        480,
        840,
        1344,
    ]
    assert all(
        row["interval"]["root_bracket_adjacent_and_exact"] is True
        for row in ledger["rows"]
    )
    assert all(
        row["interval"]["padding_dominates_exact_finite_correction"] is True
        for row in ledger["rows"]
    )
    assert [
        row["interval"]["maximum_power_window_correction"]
        for row in ledger["rows"]
    ] == [
        [10556, 213],
        [2194218, 21901],
        [699912, 4163],
        [1134310, 4477],
        [1335036, 3751],
        [2303322, 4841],
    ]


def test_w_and_v_extrema_are_frozen_exactly() -> None:
    ledger = report()["ledger"]
    assert ledger["global_w_min"] == (8516648448, (5, (1, 2, 3), 3))
    assert ledger["global_w_max"] == (
        20714179680564865272345420107181874741248000,
        (15, (1, 14, 15), 1),
    )
    assert ledger["global_v_min"] == (230722131456, (5, (1, 2, 3), 3))
    assert ledger["global_v_max"] == (
        837008896359187552793649914881094977585152000,
        (15, (1, 14, 15), 1),
    )


def test_leading_sign_and_remainder_certificates() -> None:
    ledger = report()["ledger"]
    assert ledger["minimum_endpoint_margin"] == {
        "numerator": 78561122159975755860732369169163215593189,
        "denominator": 5202861943105675888242343750000,
        "case": (5, (1, 3, 4), 3, "lower"),
    }
    assert ledger["maximum_remainder_majorant"] == {
        "value": 5803459849500468008887094102834483923255296000,
        "case": (15, (1, 2, 15), 15),
        "below_10_pow_46": True,
    }
    assert ledger["minimum_endpoint_margin_gt_one"] is True
    assert ledger["target_cutoff_dominates_remainder"] is True
    assert report()["fourth_nonvanishing"] == {
        "cyclic_positions": 3024,
        "critical_points_inside": 0,
        "endpoint_sign_changes": 0,
        "minimum_endpoint_margin": {
            "numerator": 3058554623558303407428783455243082059007,
            "denominator": 5202861943105675888242343750000,
            "case": (5, (1, 3, 4), 3, "lower"),
        },
        "minimum_endpoint_margin_gt_one": True,
        "maximum_remainder_majorant": {
            "value": 214942957388906222551373855660536441602048000,
            "case": (15, (1, 2, 15), 15),
            "below_10_pow_46": True,
        },
        "target_cutoff_dominates_remainder": True,
    }


def test_1004_digit_hensel_fixture_is_congruence_only() -> None:
    fixture = report()["hensel_fixture"]
    assert fixture["exponent"] == 166
    assert fixture["gap_digits"] == 1004
    assert fixture["n_digits"] == 6023
    assert fixture["local_fifth_remainders"] == [0, 0, 0]
    assert fixture["reduced_remainders"] == [0, 0, 0]
    assert fixture["normalized_remainders"] == [0, 0, 0]
    assert fixture["all_z_nonzero"] is True
    assert fixture["all_w_nonzero"] is True
    assert fixture["all_normalized_nonzero"] is True
    assert fixture["upper_window"] is False
    assert fixture["block_equation"] is False
