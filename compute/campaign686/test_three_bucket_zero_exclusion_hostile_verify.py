from compute.campaign686.three_bucket_zero_exclusion_hostile_verify import (
    CROSS_BOUND,
    CUTOFF,
    THIRD_BOUND,
    boundary_report,
    frozen_hash_report,
    report,
)


EXPECTED_HASHES = {
    "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean":
        "5b802dd3db2d63254b251465f96093358389c0eca4d72cdd7608d2238e549ff2",
    "compute/campaign686/three_bucket_zero_exclusion_verify.py":
        "106f7686c30eed5150d922fa1e0acbd1b7439f1bc000a356df541af724fb4c78",
    "compute/campaign686/test_three_bucket_zero_exclusion_verify.py":
        "6d7f2aa138e344fed21700b86a58e98a50ebbbbb3976c2d42fd95c9a66ae4810",
    "compute/campaign686/three_bucket_zero_exclusion_findings.md":
        "459f43e1d11c02186635bfe617a8bfe372acdcc5c3cc407fc7bfb7f1d78a3f20",
    "docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion.md":
        "0ba5ac8c350406eeccc5e4f134f392487dd3045c4de5dd685964d49c6d22c330",
}

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


def test_frozen_hash_manifest_and_live_drift_report_are_exact() -> None:
    hashes = frozen_hash_report()
    assert hashes["expected"] == EXPECTED_HASHES
    assert set(hashes["actual"]) == set(EXPECTED_HASHES)
    assert hashes["drifted_paths_since_audit"] == [
        relative
        for relative, expected in EXPECTED_HASHES.items()
        if hashes["actual"][relative] != expected
    ]
    assert hashes["all_match"] is (not hashes["drifted_paths_since_audit"])


def test_every_ordered_target_triple_and_conversion_is_exact() -> None:
    result = report()
    assert result["ordered_distinct_owner_triples"] == 6_210
    assert result["cross_identity_checks"] == 6_210
    assert result["third_identity_checks"] == 6_210
    assert result["cyclic_designated_zero_checks"] == 18_630
    for row in result["rows"]:
        (
            count,
            maximum_cross,
            maximum_cross_case,
            maximum_third,
            maximum_third_case,
        ) = EXPECTED_ROWS[row["k"]]
        assert row["ordered_distinct_owner_triples"] == count
        assert row["maximum_cross_numerator"] == maximum_cross
        assert row["maximum_cross_case"] == maximum_cross_case
        assert row["maximum_third_coefficient"] == maximum_third
        assert row["maximum_third_case"] == maximum_third_case
        assert row["zero_cross_cases"] == 0
        assert row["zero_third_cases"] == 0


def test_rounded_numeric_cutoff_is_strict_and_exact() -> None:
    numeric = report()["numeric_cutoff"]
    assert numeric["cross_bound"] == CROSS_BOUND == 10**30
    assert numeric["third_bound"] == THIRD_BOUND == 10**18
    assert numeric["cutoff"] == CUTOFF == 10**120
    assert numeric["majorant"] == (
        127_993_057_016_846_539_654_048_809_041_799_413_760_000
        * 10**78
    )
    assert numeric["majorant"] < numeric["cutoff"]
    assert numeric["cutoff_margin_floor"] == 7


def test_small_prime_shared_loss_unit_and_power_boundaries() -> None:
    packing = boundary_report()["packing"]
    small = packing["small_primes_shared_with_g"]
    assert small["components"] == [2, 3, 5]
    assert small["g"] == 30
    assert small["gcds_with_g"] == [2, 3, 5]
    assert small["premises_hold"] is True
    assert small["conclusion_holds"] is True
    assert [fixture["components"] for fixture in packing["unit_fixtures"]] == [
        [1, 2, 3],
        [1, 1, 1],
    ]
    assert all(fixture["premises_hold"] for fixture in packing["unit_fixtures"])
    assert all(fixture["conclusion_holds"] for fixture in packing["unit_fixtures"])
    sharp = packing["g_fourth_power_sharp_fixture"]
    assert sharp["d"] == 810
    assert sharp["d_divides_product_g4"] is True
    assert sharp["d_divides_product_g3"] is False


def test_telescope_and_large_pseudo_witness_scope_is_not_overclaimed() -> None:
    boundaries = boundary_report()
    assert boundaries["d_eq_one_telescopes"] == [
        {
            "k": 9,
            "n": 2,
            "d": 1,
            "equation": True,
            "large_gap_hypothesis": False,
        },
        {
            "k": 15,
            "n": 4,
            "d": 1,
            "equation": True,
            "large_gap_hypothesis": False,
        },
    ]
    pseudo = boundaries["crt_pseudo_witness"]
    assert pseudo["gap_digits"] == 121
    assert pseudo["gap_at_least_cutoff"] is True
    assert pseudo["pairwise_coprime_components"] is True
    assert pseudo["exact_step_three_progression"] is True
    assert pseudo["local_divisibilities"] is True
    assert pseudo["composed_divisibilities"] is True
    assert pseudo["all_second_obstructions_nonzero"] is True
    assert pseudo["zero_exclusion_conclusion_holds"] is True
    assert pseudo["short_window"] is False
    assert pseudo["equation"] is False
    assert report()["scope"]["closes_nonzero_branch"] is False
    assert report()["scope"]["closes_erdos_686"] is False
