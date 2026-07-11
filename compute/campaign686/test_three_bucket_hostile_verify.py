from compute.campaign686.three_bucket_hostile_verify import (
    below_threshold_short_crt_fixture,
    boundary_checks,
    crt_family_prefix_scan,
    global_moment_localization_grid,
    independent_crt_witness,
    independent_slope_scan,
    signed_elimination_grid,
)


def test_named_boundaries_are_exercised() -> None:
    result = boundary_checks()
    assert result["d_eq_one_telescopes"] == [
        {"k": 9, "n": 2, "d": 1},
        {"k": 15, "n": 4, "d": 1},
    ]
    assert result["center_triple_occurrences"] > 0
    assert result["reflected_pair_triple_occurrences"] > 0
    assert result["small_prime_owner_fixtures"] > 0


def test_short_crt_threshold_is_not_vacuous() -> None:
    result = below_threshold_short_crt_fixture()
    assert result["d"] == 6_790
    assert result["short_window_holds"] is True
    assert result["target_threshold_holds"] is False
    assert result["block_equation_holds"] is False
    assert result["local_remainders"] == [[0, 0], [0, 0], [0, 0]]


def test_independent_slope_scan() -> None:
    result = independent_slope_scan()
    assert result["total_unordered_triples"] == 1_035
    assert [row["minimum_separation"] for row in result["rows"]] == [
        [10, 1],
        [7, 1],
        [27, 5],
        [99, 35],
        [117, 70],
        [15, 14],
    ]


def test_independent_signed_elimination_grid() -> None:
    assert signed_elimination_grid() == {
        "signed_elimination_fixtures": 5_216,
        "intermediate_square_fixtures": 5_216,
    }


def test_global_moments_reduce_to_second_local_residue() -> None:
    assert global_moment_localization_grid() == {
        "signed_global_moment_localizations": 2_880
    }


def test_crt_pseudo_witness_has_only_the_claimed_route_failures() -> None:
    result = independent_crt_witness()
    assert result["gap"] == {
        "digits": 121,
        "at_least_10_pow_120": True,
        "decimal_sha256": "027335da1fe1ac90a3e64722c6112adcc6a88359f5628432e13396b3303910b2",
    }
    assert result["n"]["digits"] == 484
    assert result["progression_differences"] == [0, 3, 9]
    assert result["global_square_remainder"] == 0
    assert result["lower_global_moment_remainder"] == 0
    assert result["upper_global_moment_remainder"] == 0
    assert all(
        check["second_remainder"] == 0
        and check["third_remainder"] == 0
        and check["lower_factor_remainder"] == 0
        for check in result["local_checks"]
    )
    assert result["block_equation"]["holds"] is False
    assert result["short_window"]["holds"] is False


def test_parameterized_crt_family_prefix() -> None:
    assert crt_family_prefix_scan() == {
        "exponents_checked": [1, 24],
        "fixtures": 24,
        "gap_formula": "(101*103*107)^t",
        "first_gap_digits": 7,
        "last_gap_digits": 146,
    }
