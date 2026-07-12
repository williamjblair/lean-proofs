from __future__ import annotations

from math import factorial, gcd, prod

from .consecutive_property_verify import (
    FIXTURES,
    audit_fixture,
    bounded_k_plus_one_data,
    exhaustive_small_audit,
    factorial_quotient,
    bounded_equation_core_multisets,
    maximum_strict_matching_size,
    owner_graph_edge_dichotomy_audit,
    balanced_component_capacity_audit,
    centered_root_bracket_audit,
    cycle_incidence_audit,
    proper_component_separation_audit,
    reflection_compatible_four_cycle_fixture,
    part_block,
    report,
    target_row_mass_counterexample,
)


def test_centered_root_bracket_is_exact_from_k16() -> None:
    audit = centered_root_bracket_audit(512)
    assert audit["partial_sum_numerator"] == 839_241_148_077
    assert audit["partial_sum_denominator"] == 209_715_200_000
    assert audit["excess_numerator"] == 380_348_077
    assert audit["excess_denominator"] == 209_715_200_000
    assert [row["k"] for row in audit["samples"]] == [16, 17, 19, 64, 512]


def test_factorial_divisibility_on_every_hostile_fixture() -> None:
    for _, k, n, d in FIXTURES:
        assert factorial_quotient(k, n) >= 1
        assert factorial_quotient(k, n + d) >= 1


def test_genuine_equations_have_exact_stripped_and_rough_ratios() -> None:
    rows = {row["name"]: row for row in report()["fixtures"]}
    for name in ("d-one-telescope-k9", "d-one-telescope-k15"):
        row = rows[name]
        assert row["equation"] is True
        assert row["small_ratio"] is True
        assert row["rough_ratio"] is True
        assert row["upper_max"] > row["k"] + 1


def test_named_row_and_smooth_pseudo_fixtures_are_not_overclaimed() -> None:
    rows = {row["name"]: row for row in report()["fixtures"]}
    for name in (
        "row-prefix-17",
        "row-prefix-16",
        "smooth-reflection-even",
        "smooth-reflection-odd",
    ):
        row = rows[name]
        assert row["equation"] is False
        assert row["small_ratio"] is False
        assert row["upper_max"] > row["k"] + 1


def test_exact_deep_fixture_maxima() -> None:
    deep17 = audit_fixture("deep17", 984, 3_177_026, 4_480)
    assert (deep17.lower_max, deep17.lower_max_position) == (3_178_010, 984)
    assert (deep17.upper_max, deep17.upper_max_position) == (3_182_487, 981)
    deep16 = audit_fixture("deep16", 244, 48_502, 277)
    assert (deep16.lower_max, deep16.lower_max_position) == (48_741, 239)
    assert (deep16.upper_max, deep16.upper_max_position) == (49_022, 243)


def test_els_theorem4_trivial_target_row_pattern() -> None:
    # For k=19 and any start congruent to 1 modulo the resolving period, the
    # bounded parts are 2,...,20: missing r=1 at the j=19 position of 20.
    row = target_row_mass_counterexample()
    assert row["upper_parts"] == list(range(2, 21))
    assert row["upper_missing"] == 1
    assert row["upper_k_plus_one_position"] == 19


def test_mass_only_target_row_counterexample_is_exact() -> None:
    row = target_row_mass_counterexample()
    assert row["k"] == 19
    assert row["period"] == 2_258_015_666_306_400
    assert row["d"] == 2_258_015_666_304_861
    assert row["lower_product_over_factorial"] == 5
    assert row["small_product_ratio_four"] is True
    assert row["full_equation"] is False


def test_published_bounded_classifications_on_small_exact_box() -> None:
    counts = exhaustive_small_audit()
    assert counts == {
        "lengths": 11,
        "starts": 22_000,
        "theorem1_bounded_cases": 1_511,
        "theorem4_bounded_cases": 1_773,
    }


def test_no_strict_perfect_matching_in_every_bounded_equation_branch() -> None:
    audit = owner_graph_edge_dichotomy_audit(2_000)
    assert audit["arithmetic_branches"] == 3_182
    for row in audit["samples"]:
        assert row["maximum_strict_pairs"] < row["k"]
        assert row["owner_edges_required"] == row["k"] + 1


def test_two_extremal_obstructions_to_perfect_matching() -> None:
    # r=1: lower and upper both contain the maximum K (K>=20 here).
    lower, upper = bounded_equation_core_multisets(19, 1)
    assert max(lower) == max(upper) == 20
    assert maximum_strict_matching_size(lower, upper) == 18 < 19

    # r>1: lower and upper both contain the minimum 1.
    lower, upper = bounded_equation_core_multisets(23, 2)
    assert min(lower) == min(upper) == 1
    assert maximum_strict_matching_size(lower, upper) < 23


def test_explicit_large_d_component_balance_capacity() -> None:
    audit = balanced_component_capacity_audit(256)
    assert audit["unequal_component_size_pairs"] == 5_591_200
    rows = {row["k"]: row for row in audit["samples"]}
    assert rows[16]["threshold"] == 34**16
    assert rows[19]["threshold"] == 40**19
    for k, row in rows.items():
        assert row["balanced_nontrivial_min_edges"] == k + 2


def test_even_cycle_has_only_the_global_rough_product_dependency() -> None:
    audit = cycle_incidence_audit(24)
    assert len(audit["cycles"]) == 23
    for row in audit["cycles"]:
        assert row["rank"] == 2 * row["vertices_per_side"] - 1
        assert row["nullity"] == 1


def test_reflection_compatible_four_cycle_is_exact_but_outside_window() -> None:
    row = reflection_compatible_four_cycle_fixture()
    assert row["edges"] == {
        "1,19": 163,
        "1,1": 113,
        "3,19": 79,
        "3,1": 433,
    }
    assert row["lower_values"] == {1: 239_447, 3: 239_449}
    assert row["upper_values"] == {19: 244_663, 1: 244_645}
    assert row["n_gt_9d"] is True
    assert row["reflection_compression"] is True
    assert row["upper_ratio_window"] is True
    assert row["lower_ratio_window"] is False


def test_only_half_size_proper_component_has_rational_target_ratio() -> None:
    audit = proper_component_separation_audit(512)
    assert audit["proper_component_sizes"] == 130_711
    assert all(row["s"] * 2 == row["k"] for row in audit["rational_exceptions"])
    assert all(row["value"] == 2 for row in audit["rational_exceptions"])
