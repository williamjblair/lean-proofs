from compute.campaign686.short_window_quotient_attack import (
    boundary_audit,
    coefficient_audit,
    exact_small_short_search,
    reduced_fourth_coefficient,
    signed_identity_grid,
    target_size_congruence_family,
    two_zero_quotient_scan,
    validate_short_tuple,
    verify_reduced_fourth_identity,
)


def test_reduced_fourth_identity_and_target_coefficient_scan() -> None:
    signed = signed_identity_grid()
    assert signed == {
        "signed_reduced_fourth_identities": 1_377,
        "all_hold": True,
    }
    scan = coefficient_audit()
    assert scan["ordered_distinct_owner_triples"] == 6_210
    assert scan["center_owner_occurrences"] == 502
    assert scan["zero_reduced_coefficients"] == 502
    assert scan["all_zeros_are_centers"] is True
    assert scan["reflected_triple_occurrences"] == 1_506
    assert scan["rank_two_lattice_triples"] == 1_035
    assert scan["all_lattice_gammas_nonzero"] is True
    assert scan["zero_lattice_weight_components"] == 27
    assert scan["minimum_lattice_gamma"] == 2_160
    assert scan["maximum_lattice_gamma"] == 4_070_625_913_172_821_209_661_440
    assert scan["minimum_nonzero_reduced_coefficient"] == 17_729_280
    assert scan["maximum_reduced_case"] == (15, 1, 14, 15)
    assert scan["maximum_reduced_coefficient"] == (
        7_628_070_240_970_929_200_984_341_763_734_527_541_248_000
    )
    for row in scan["rows"]:
        center = (row["k"] - 1) * (row["k"] - 2)
        assert row["center_owner_occurrences"] == center
        assert row["zero_reduced_coefficients"] == center


def test_identity_keeps_signs_and_center_degeneracy() -> None:
    for t in (-17, -1, 0, 1, 23):
        for g in (-5, -1, 0, 1, 7):
            assert verify_reduced_fourth_identity(15, 1, 8, 15, t, g)
            assert verify_reduced_fourth_identity(15, 8, 1, 15, t, g)
    assert reduced_fourth_coefficient(15, 8, 1, 15) == 0
    assert reduced_fourth_coefficient(15, 1, 8, 15) != 0


def test_small_primes_centers_reflections_and_telescopes() -> None:
    boundary = boundary_audit()
    assert boundary["d_eq_one_telescopes"] == [
        {"k": 9, "n": 2, "d": 1},
        {"k": 15, "n": 4, "d": 1},
    ]
    assert boundary["includes_owner_component_two"] is True
    assert boundary["includes_owner_component_three"] is True
    fixture = boundary["small_prime_fixture"]
    assert fixture["components"] == [3, 5, 2]
    assert fixture["d"] == 720
    assert fixture["residuals"] == [4_122, 4_125, 4_128]
    assert fixture["all_local_lifts"] is True
    assert fixture["all_composed_lifts"] is True
    assert fixture["block_equation"] is False


def test_exact_quotient_normalization_and_new_restrictions() -> None:
    result = validate_short_tuple(
        k=5,
        indices=(1, 2, 3),
        components=(3, 5, 2),
        g=24,
        anchor_residual=4_122,
    )
    assert result["common_floor_quotient"] == 5
    assert result["quotient_remainders"] == [522, 525, 528]
    assert result["component_remainder_quotients"] == [174, 105, 264]
    assert result["quotient_normalization"] is True
    assert result["lattice_identity"] is True
    assert result["all_short_quotient_bounds"] is True
    for row in result["composed_rows"]:
        assert row["reduced_fourth_remainder"] == 0
        assert row["component_quotient_gcd_divides_fixed"] is True
        assert row["left_overlap_divides_offset"] is True
        assert row["right_overlap_divides_offset"] is True
        assert row["product_overlap_divides_offset_product"] is True
        assert row["quotient_bound"] is True


def test_finite_short_search_has_real_fourth_lift_survivors_only_below_cutoff() -> None:
    search = exact_small_short_search(20_000)
    assert search["tested_loss_values"] == 11_786
    assert search["surviving_short_fourth_lift_tuples"] == 33
    assert search["first_survivor"] == {
        "components": [3, 5, 2],
        "g": 24,
        "d": 720,
        "residuals": [4_122, 4_125, 4_128],
        "cofactors": [458, 165, 1_032],
        "n": 1_613,
    }
    assert search["largest_gap_survivor"]["d"] == 3_402
    assert search["all_below_target"] is True
    assert search["all_fail_block_equation"] is True


def test_target_size_hensel_family_still_fails_exactly_the_short_window() -> None:
    result = target_size_congruence_family(20)
    assert result["gap_digits"] == 121
    assert result["gap_at_least_target"] is True
    assert result["all_local_lifts"] is True
    assert result["all_composed_lifts"] is True
    assert result["lattice_identity"] is True
    assert result["lower_window"] is True
    assert result["upper_window"] is False
    assert result["residual_to_gap_floor_digits"] == 484
    assert result["block_equation"] is False


def test_two_noncentral_zero_quotients_are_closed_through_k13() -> None:
    scan = two_zero_quotient_scan()
    expected = {
        5: (18, 18, 2),
        7: (75, 75, 3),
        9: (196, 196, 4),
        11: (405, 405, 5),
        13: (726, 726, 6),
        15: (1_183, 901, 7),
    }
    for row in scan["rows"]:
        total, closed, zero_weight = expected[row["k"]]
        assert row["noncentral_two_zero_cases"] == total
        assert row["closed_cases"] == closed
        assert row["zero_weight_contradictions"] == zero_weight
        assert row["numeric_closures"] == closed - zero_weight
        if row["k"] <= 13:
            assert row["first_open_case"] is None
    assert scan["noncentral_two_zero_cases"] == 2_603
    assert scan["closed_cases"] == 2_321
    assert scan["all_noncentral_two_zero_cases_closed_for_k_le_13"] is True
    assert scan["k15_closed_cases"] == 901
    assert scan["k15_total_cases"] == 1_183
