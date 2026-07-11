from fractions import Fraction

from compute730.campaign_uniform.repair.far.unit_range_block_hostile_verify import (
    aligned_block_audit,
    availability_and_deleted_digit_audit,
    exponent_partition_audit,
    geometric_series_audit,
    prime_sum_audit,
    quadratic_identity_audit,
    root_and_normalization_audit,
    series_at_prime,
    translated_interval_audit,
)


def test_quadratic_identity_and_exact_aligned_low_word_count() -> None:
    identity = quadratic_identity_audit()
    assert identity == {"signed_fixtures": 1_764, "all_exact": True}
    aligned = aligned_block_audit()
    assert aligned["cases"] == 10
    assert aligned["every_low_count_exact"] is True
    assert aligned["every_full_count_at_most_low_bound"] is True
    assert aligned["a_eq_r_eq_2_included"] is True


def test_branch_availability_and_exact_valuation_digit_deletion() -> None:
    audit = availability_and_deleted_digit_audit()
    assert audit["primes_5_through_997"] == 166
    assert audit["availability_histogram"] == {0: 2, 1: 0, 2: 1, 3: 0, 4: 163}
    assert audit["unavailable_branches"] == {
        7: ["P", "R"],
        41: ["P", "Q", "R", "S"],
        43: ["P", "Q", "R", "S"],
    }
    assert audit["p2_p3_have_no_branch_roots"] is True


def test_arbitrary_translated_intervals_use_visible_boundary_blocks() -> None:
    audit = translated_interval_audit()
    assert audit["arbitrary_translation_envelope_holds"] is True
    assert audit["maximum_boundary_blocks_beyond_floor"] == 2
    assert audit["combinatorial_checks"] > 1_000
    assert audit["actual_map_checks"] > 1_000


def test_actual_root_lengths_orientation_maximal_r_and_normalization() -> None:
    audit = root_and_normalization_audit()
    assert audit["root_class_checks"] == 396
    assert audit["qN_minus_one_orientation"] == "q*(N-1)<=X"
    assert audit["maximal_r_unique_when_present"] is True
    assert audit["a_eq_r_eq_2_row"]["a"] == 2
    assert audit["a_eq_r_eq_2_row"]["r"] == 2
    assert all(row["normalized_cross_margin"] >= 0 for row in audit["normalization_rows"])


def test_exponent_ranges_are_disjoint_and_cover_every_long_class() -> None:
    audit = exponent_partition_audit()
    assert audit["abstract_checks"] == 256**2
    assert audit["strict_and_unit_disjoint"] is True
    assert audit["a_eq_r_is_unit"] is True
    assert audit["a_eq_r_plus_one_is_strict"] is True
    assert audit["short_is_no_maximal_r"] is True
    assert audit["top_range_definition_in_candidate"] is False


def test_double_geometric_series_is_rederived_exactly() -> None:
    audit = geometric_series_audit()
    assert audit["formula_exact"] is True
    for row in audit["rows"]:
        p = row["p"]
        assert row["closed"] == Fraction(p + 1, p * (p - 1) * (2 * p + 1))
        assert row["positive_remainder"] > 0
    assert series_at_prime(5) == Fraction(3, 110)


def test_166_prime_sum_tail_and_four_branch_ceiling() -> None:
    audit = prime_sum_audit()
    assert audit["prime_count"] == 166
    assert audit["largest_prime"] == 997
    assert audit["partial_below_57_over_1000_margin"] > 0
    assert audit["integer_tail"] == Fraction(1, 1000)
    assert audit["endpoint_cover_factor"] == 2
    assert audit["branch_union_factor"] == 4
    assert audit["four_branch_bound"] < Fraction(58, 125)
    assert audit["margin_below_half"] > 0
