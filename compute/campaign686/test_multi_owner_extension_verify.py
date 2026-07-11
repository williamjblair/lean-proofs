from __future__ import annotations

from fractions import Fraction

from compute.campaign686.multi_owner_extension_verify import (
    ROWS,
    exponent_selection_report,
    generalized_fixture_report,
    multi_owner_congruence_crt_witness,
    report,
    target_subset_report,
)


def test_generalized_second_third_elimination_signed_grid() -> None:
    grid = generalized_fixture_report()
    assert grid["owner_families_checked"] == sum(k - 2 for k in ROWS)
    assert grid["owner_congruences_checked"] > 0
    assert grid["all_second_compositions_hold"]
    assert grid["all_third_compositions_hold"]


def test_all_four_plus_target_subsets_have_no_positive_zero_collision() -> None:
    scan = target_subset_report()
    assert scan["subset_count"] == 42_274
    assert scan["owner_slope_count"] == 309_329
    # Reflected four-owner families can have two equal positive slopes, but
    # the target-size lower bound excludes each slope before multiplicity is
    # relevant.
    assert scan["maximum_simultaneous_positive_zeros"] == 2
    assert scan["subsets_with_positive_zero_slope_collision"] == 327
    assert scan["all_positive_zero_slopes_excluded_at_target"]


def test_zero_slope_extrema_are_exact() -> None:
    scan = target_subset_report()
    maximum = scan["maximum_positive_zero_slope"]
    assert Fraction(maximum["numerator"], maximum["denominator"]) > 0
    margin = scan["minimum_target_lower_bound_over_positive_slope"]
    assert Fraction(margin["numerator"], margin["denominator"]) > 1


def test_three_bucket_selection_does_not_bound_the_complement() -> None:
    selection = exponent_selection_report()
    assert selection["largest_three_product_lower_exponent"] == Fraction(1, 5)
    assert selection["complement_upper_exponent"] == Fraction(4, 5)
    assert selection["explicit_four_owner_counterfamily"] == [
        Fraction(1, 4),
        Fraction(1, 4),
        Fraction(1, 4),
        Fraction(1, 4),
    ]
    assert not selection["bounded_complement_follows"]


def test_four_owner_local_congruences_have_target_size_non_solution() -> None:
    witness = multi_owner_congruence_crt_witness(
        k=5,
        owners=(1, 2, 4, 5),
        components=(101**16, 103**16, 107**16, 109**16),
    )
    assert witness["gap_above_target"]
    assert witness["all_local_congruences_hold"]
    assert witness["all_composed_obstructions_hold"]
    assert not witness["block_equation_holds"]
    assert not witness["short_window_holds"]


def test_full_report_is_deterministic_and_non_closing() -> None:
    result = report()
    assert result["route_verdict"] == (
        "in a full bounded-loss t-owner decomposition every second "
        "obstruction is nonzero at target size, but its exact "
        "archimedean size grows as d^(t-2); neither the divisibilities "
        "nor top-three selection closes any t>=4 branch"
    )
