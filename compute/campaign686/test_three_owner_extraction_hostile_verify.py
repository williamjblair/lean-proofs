from __future__ import annotations

from compute.campaign686.three_owner_extraction_hostile_verify import (
    boundary_fixture_report,
    exhaustive_equivalence_report,
    explicit_boundary_report,
    forbidden_token_report,
    no_two_cover,
    producer_hash_report,
    three_live_distinct_entries,
)


def test_exhaustive_cover_equivalence() -> None:
    result = exhaustive_equivalence_report()
    assert result["universe_sizes"] == [1, 2, 3, 4, 5, 6]
    assert result["support_sizes"] == [0, 1, 2, 3, 4, 5, 6]
    assert result["finite_models"] == sum(
        sum((2 * k) ** size for size in range(7)) for k in range(1, 7)
    )
    assert result["no_two_cover_models"] == result["three_distinct_live_models"]
    assert result["mismatches"] == 0


def test_frozen_producer_hashes_match() -> None:
    assert producer_hash_report()["all_frozen_hashes_match"]


def test_producer_and_audit_lean_sources_have_no_forbidden_executable_tokens() -> None:
    scan = forbidden_token_report()
    assert scan["clean"], scan["matches"]


def test_exhaustive_counts_match_inclusion_exclusion() -> None:
    result = exhaustive_equivalence_report()
    assert result["no_two_cover_models"] == result["inclusion_exclusion_count"]
    assert sum(result["distinct_live_value_counts"].values()) == result["finite_models"]


def test_zero_clean_and_coincident_cover_boundaries() -> None:
    boundary = boundary_fixture_report()
    assert boundary["empty_support_is_two_covered"]
    assert boundary["zero_live_values_are_two_covered"]
    assert boundary["one_live_value_is_covered_with_i_eq_j"]
    assert boundary["two_live_values_are_two_covered"]
    assert boundary["three_live_values_have_no_two_cover"]
    assert boundary["four_live_values_have_no_two_cover"]
    assert boundary["zero_clean_outside_cover_is_ignored"]
    assert boundary["off_support_total_function_values_are_irrelevant"]


def test_endpoints_repetition_and_small_prime_labels() -> None:
    explicit = explicit_boundary_report()
    assert explicit["endpoint_owners_extract"] == [0, 1, 2]
    assert explicit["repeated_owner_entries_do_not_fake_three_values"]
    assert explicit["prime_labels_2_and_3_require_no_special_case"]
    assert explicit["fourth_live_value_is_not_discarded_by_conclusion"]


def test_predicates_directly_distinguish_two_and_three_values() -> None:
    assert not no_two_cover((1, 2, 2, 1), (True, True, True, False), 2)
    assert not three_live_distinct_entries(
        (1, 2, 2, 1), (True, True, True, False)
    )
    assert no_two_cover((1, 2, 3), (True, True, True), 3)
    assert three_live_distinct_entries((1, 2, 3), (True, True, True))
