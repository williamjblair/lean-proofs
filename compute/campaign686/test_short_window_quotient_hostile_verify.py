from compute.campaign686.short_window_quotient_hostile_verify import (
    coefficient_geometry_report,
    freeze_report,
    hostile_scope_report,
    public_surface_report,
    report,
    signed_identity_report,
    small_fixture_report,
    two_zero_report,
)


def test_all_six_producer_hashes_and_prose_duplicate_are_frozen() -> None:
    frozen = freeze_report()
    assert frozen["all_match"] is True
    assert frozen["files"] == 6
    duplicate = frozen["findings_prose_duplicate"]
    assert duplicate == {
        "earlier_line": 83,
        "section_8_line": 353,
        "text": "P_s^3 | 3a_u a_v T_s + P_s^2 J_s,",
        "semantic_effect": False,
    }


def test_public_surface_contains_all_thirteen_theorems() -> None:
    surface = public_surface_report()
    assert surface["public_definitions"] == 5
    assert surface["public_theorems"] == 13
    assert surface["producer_audit_is_importer_only"] is True


def test_signed_reduced_identity_and_six_row_geometry_reconstruct() -> None:
    signed = signed_identity_report()
    assert signed == {"checks": 1_377, "all_hold": True}
    geometry = coefficient_geometry_report()
    assert geometry["ordered_distinct_owner_triples"] == 6_210
    assert geometry["center_owner_occurrences"] == 502
    assert geometry["zero_reduced_coefficients"] == 502
    assert geometry["all_zeros_are_centers"] is True
    assert geometry["rank_two_lattice_triples"] == 1_035
    assert geometry["all_lattice_gammas_nonzero"] is True
    assert geometry["zero_lattice_weight_components"] == 27
    assert geometry["minimum_lattice_gamma"] == 2_160
    assert geometry["maximum_lattice_gamma"] == 4_070_625_913_172_821_209_661_440
    assert geometry["minimum_nonzero_reduced_coefficient"] == 17_729_280
    assert geometry["maximum_reduced_case"] == [15, 1, 14, 15]
    assert geometry["maximum_reduced_coefficient"] == (
        7_628_070_240_970_929_200_984_341_763_734_527_541_248_000
    )


def test_all_2603_noncentral_two_zero_cases_and_both_claims() -> None:
    result = two_zero_report()
    expected = {
        5: (18, 18, 2, 16),
        7: (75, 75, 3, 72),
        9: (196, 196, 4, 192),
        11: (405, 405, 5, 400),
        13: (726, 726, 6, 720),
        15: (1_183, 901, 7, 894),
    }
    for row in result["rows"]:
        assert (
            row["noncentral_two_zero_cases"],
            row["closed_cases"],
            row["zero_weight_contradictions"],
            row["numeric_closures"],
        ) == expected[row["k"]]
    assert result["noncentral_two_zero_cases"] == 2_603
    assert result["closed_cases"] == 2_321
    assert result["all_closed_through_k13"] is True
    assert result["k15_closed"] == 901
    assert result["k15_total"] == 1_183
    assert result["k15_open"] == 282
    assert result["first_open_case"] == {
        "indices": [1, 2, 3],
        "zero_positions": [0, 1],
        "remaining_weight": 827_009_339,
        "coefficient_lcm": 271_807_019_335_111_703_420_341_421_246_717_838_874_046_408_410_791_936_000,
        "gamma": 398_569_323_412_788_480_000,
        "majorant_digits": 257,
        "cutoff_side_digits": 249,
    }


def test_named_short_fixture_reproduces_every_lift_and_restriction() -> None:
    fixture = small_fixture_report()
    assert fixture["components"] == [3, 5, 2]
    assert fixture["g"] == 24
    assert fixture["d"] == 720
    assert fixture["residuals"] == [4_122, 4_125, 4_128]
    assert fixture["cofactors"] == [458, 165, 1_032]
    assert fixture["all_local_lifts"] is True
    assert fixture["all_composed_lifts"] is True
    assert fixture["quotient_normalization"] is True
    assert fixture["lattice_identity"] is True
    assert fixture["all_quotient_restrictions"] is True
    assert fixture["block_equation"] is False


def test_hostile_scope_retains_centers_and_k15_open_cases() -> None:
    scope = hostile_scope_report()
    assert scope["center_reduced_coefficient"] == 0
    assert scope["noncentral_reduced_coefficient"] != 0
    assert scope["zero_weight_contradiction_requires_positive_g"] is True
    assert scope["pairwise_coprimality_is_load_bearing"] is True
    assert scope["center_containing_two_zero_cases_remain"] is True
    assert scope["k15_noncentral_open_cases"] == 282
    assert scope["finite_two_zero_application_is_lean_wrapped"] is False


def test_final_verdict_is_safe_only_at_generic_partial_scope() -> None:
    result = report()
    assert result["verdict"] == "PASS partial package"
    assert result["safe_to_integrate_generic_lean"] is True
    assert result["finite_two_zero_scan_attestation_ready"] is False
    assert result["closes_three_owner_branch"] is False
    assert result["closes_erdos_686"] is False
