import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from short_window_lattice_sign_attack import (
    TARGET,
    coefficient_counterfixture,
    one_sided_cases,
    ordering_stability_audit,
    realized_counterfixtures,
    remaining_cancellation_lemma,
    sign_cell_audit,
    verify_frozen_package,
    weight_and_correction_audit,
)


def test_frozen_quotient_package_hashes() -> None:
    hashes = verify_frozen_package()
    assert len(hashes) == 6
    assert all(len(digest) == 64 for digest in hashes.values())


def test_target_threshold_order_is_exactly_stable() -> None:
    audit = ordering_stability_audit()
    assert audit["minimum_unequal_root_or_endpoint_separation"] == "247/3960"
    assert audit["maximum_absolute_correction"] == "1171733/165"
    assert audit["twice_maximum_correction_over_target_is_smaller"] is True
    assert audit["equal_root_pairs"] == 27
    assert audit["zero_weight_components"] == 27
    assert audit["all_equal_roots_are_reflected_around_the_row_center"] is True


def test_all_1035_triples_and_every_sign_cell_are_counted() -> None:
    audit = sign_cell_audit()
    assert audit["totals"] == {
        "triples": 1_035,
        "zero_weight_components": 27,
        "open_mixed": 2_381,
        "open_positive": 9,
        "open_negative": 0,
        "open_zero": 0,
        "boundary_mixed": 1_337,
        "boundary_positive": 18,
        "boundary_negative": 0,
        "boundary_zero": 0,
    }
    assert [row["triples"] for row in audit["rows"]] == [10, 35, 84, 165, 286, 455]
    assert [row["open_positive"] for row in audit["rows"]] == [1, 1, 1, 2, 2, 2]
    assert [row["boundary_positive"] for row in audit["rows"]] == [2, 2, 2, 4, 4, 4]
    assert audit["quotient_sign_totals"] == {
        "open_mixed": 1_847,
        "open_positive": 285,
        "open_negative": 258,
        "open_zero": 0,
        "boundary_mixed": 699,
        "boundary_positive": 369,
        "boundary_negative": 287,
        "boundary_zero": 0,
    }


def test_all_weight_signs_and_corrections_are_counted() -> None:
    audit = weight_and_correction_audit()
    assert audit["raw_gamma_signs"] == {
        "positive": 514,
        "negative": 521,
        "zero": 0,
    }
    assert audit["oriented_weight_components"] == {
        "positive": 1_539,
        "negative": 1_539,
        "zero": 27,
    }
    assert audit["minimum_positive_gamma"] == 2_160
    assert audit["maximum_positive_gamma"] == 4_070_625_913_172_821_209_661_440


def test_only_nine_reflected_open_slivers_are_one_sided() -> None:
    cases = one_sided_cases()
    assert [(case["k"], tuple(case["indices"])) for case in cases] == [
        (5, (1, 3, 5)),
        (7, (1, 4, 7)),
        (9, (1, 5, 9)),
        (11, (1, 6, 11)),
        (11, (2, 6, 10)),
        (13, (1, 7, 13)),
        (13, (2, 7, 12)),
        (15, (1, 8, 15)),
        (15, (2, 8, 14)),
    ]
    assert all(case["strict_gap_bound_below_target"] for case in cases)
    assert sum(case["zero_boundary_gap_bound_below_target"] for case in cases) == 4
    assert all(case["strict_gap_bound"] < TARGET for case in cases)


def test_target_scale_coefficient_fixture_has_exact_large_cancellation() -> None:
    fixture = coefficient_counterfixture()
    assert fixture["d"] == TARGET
    assert fixture["lambda"] == "188"
    assert fixture["weights"] == [4, 26, 15]
    assert fixture["gamma"] == 57_240
    assert fixture["term_signs"] == [-1, 1, -1]
    assert fixture["weighted_sum"] == 57_240
    assert sum(fixture["weighted_terms"]) == fixture["gamma"]


def test_realized_short_fourth_lift_counterfixtures() -> None:
    fixtures = realized_counterfixtures()
    assert [fixture["components"] for fixture in fixtures] == [
        [3, 5, 2],
        [4, 3, 11],
    ]
    assert [fixture["d"] for fixture in fixtures] == [720, 11_484]
    assert [fixture["lambda"] for fixture in fixtures] == [
        "108317/576",
        "34914989/15138",
    ]
    assert all(fixture["all_local_lifts"] for fixture in fixtures)
    assert all(fixture["all_composed_lifts"] for fixture in fixtures)
    assert all(fixture["short_window"] for fixture in fixtures)
    assert all(fixture["below_target"] for fixture in fixtures)
    assert all(not fixture["block_equation"] for fixture in fixtures)
    assert all(
        sum(fixture["weighted_terms"])
        == fixture["gamma"] * fixture["g"] ** 2
        for fixture in fixtures
    )


def test_remaining_cancellation_budget_is_numeric_and_proper() -> None:
    lemma = remaining_cancellation_lemma()
    assert lemma["status"] == "unproved remaining lemma"
    assert [row["H_k"] for row in lemma["rows"]] == [
        212160590605173551323281417403147323796233912863684428,
        57046695925872527128812620336999351280253887202763,
        82747175828911780468168027732812182306888441,
        106758606375800441629531020205561424117038,
        13022519011656599698255286636722720,
        24979064466336593021876736560,
    ]
    assert all(row["H_k"] > row["maximum_gamma"] for row in lemma["rows"])
    assert all(row["cutoff_check"] < TARGET for row in lemma["rows"])
