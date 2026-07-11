from __future__ import annotations

from compute.campaign686.global_two_prime_hostile_verify import (
    TARGET,
    TWO_PRIME_LOSS_BOUND,
    coefficient_certificate,
    concentration_certificate,
    forbidden_tokens,
    loss_certificate,
    numeric_cutoff_certificate,
    owner_pair_certificate,
    paper_pair_bound_certificate,
    report,
    taylor_remainder_certificate,
    two_three_decomposition_certificate,
)


def test_no_forbidden_code_tokens() -> None:
    assert forbidden_tokens() == {}


def test_all_lean_coefficient_tables_match_definitions() -> None:
    certificate = coefficient_certificate()
    assert certificate["owner_count"] == 60
    assert certificate["second_table_exact"] is True
    assert certificate["third_table_exact"] is True
    assert certificate["index_table_exact"] is True
    assert certificate["all_quadratics_nonzero"] is True
    assert certificate["max_abs_constant"][0] == 87_178_291_200
    assert certificate["max_abs_linear"][0] == 283_465_647_360
    assert certificate["max_abs_quadratic"][0] == 392_156_797_824


def test_owner_partition_and_simultaneous_zero_witnesses() -> None:
    certificate = owner_pair_certificate()
    assert certificate["same_owner_cases"] == 60
    assert certificate["ordered_distinct_owner_cases"] == 610
    assert certificate["center_touching_distinct_cases"] == 108
    assert certificate["generic_determinant_cases"] == 556
    assert certificate["simultaneous_zero_cases"] == 54
    assert certificate["all_simultaneous_zero_witnesses_exact"] is True


def test_sharper_reported_pair_bounds_are_reproduced() -> None:
    certificate = paper_pair_bound_certificate()
    assert certificate["ordered_second_bound_pairs"] == 610
    assert certificate["ordered_nondegenerate_pairs"] == 556
    assert certificate["unordered_reflected_pairs"] == 27
    assert certificate["maximum_second"] == (
        217044647287343042885059609316395849093627507558461004041714015187255309475392782336000000000,
        15,
        15,
        1,
    )
    assert certificate["maximum_nondegenerate"] == (
        213050737784347495930606578667198942482754791108805213567310554501719541255193493504000000000,
        15,
        15,
        2,
    )
    assert certificate["maximum_reflected_third"] == (
        93984078683194682557325451381987070845762855139556197071318510982175649195251213580361531392000000000,
        15,
        1,
        15,
    )
    assert certificate["all_below_target"] is True


def test_prime_losses_include_two_and_three() -> None:
    certificate = loss_certificate()
    assert certificate["uniform_two_prime_loss_bound"] == 3_486_784_401
    assert certificate["all_nonthree_losses_at_most_64"] is True
    assert certificate["all_three_losses_at_most_59049"] is True
    assert certificate["rows"][15]["p2_loss"] == 64
    assert certificate["rows"][15]["p3_loss"] == 59_049


def test_independent_concentration_stress_hits_every_branch() -> None:
    certificate = concentration_certificate()
    assert certificate["global_square_premises"] > 0
    assert certificate["p2_components_checked"] > 0
    assert certificate["p3_components_checked"] > 0
    assert certificate["p2_p3_same_owner_cases"] > 0
    assert certificate["p2_p3_distinct_owner_cases"] > 0
    assert certificate["center_owner_components"] > 0


def test_two_three_clean_decomposition_boundaries() -> None:
    certificate = two_three_decomposition_certificate()
    assert certificate["ordered_p2_p3_exponent_cases"] > 0
    assert certificate["first_clean_component_unit_cases"] > 0
    assert certificate["second_clean_component_unit_cases"] > 0
    assert certificate["all_exact_decompositions"] is True
    assert certificate["all_cofactors_within_uniform_bound"] is True


def test_third_order_coefficients_and_twenty_identity() -> None:
    certificate = taylor_remainder_certificate()
    assert certificate["third_order_remainder_checks"] == 2_100
    assert certificate["third_algebra_congruence_checks"] > 10_000


def test_every_uniform_numeric_cutoff_is_strict() -> None:
    certificate = numeric_cutoff_certificate()
    assert TWO_PRIME_LOSS_BOUND == 59_049**2
    assert certificate["same_owner_bound"] < TARGET
    assert certificate["generic_nonzero_second_bound"] < TARGET
    assert certificate["simultaneous_zero_third_bound"] < TARGET
    assert certificate["all_strict"] is True


def test_full_report() -> None:
    result = report()
    assert result["forbidden_code_tokens"] == {}
    assert result["cutoffs"]["all_strict"] is True
