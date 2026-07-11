from compute.campaign686.short_window_lattice_sign_hostile_verify import (
    TARGET,
    coefficient_counterfixture,
    freeze_report,
    one_sided_report,
    ordering_stability_report,
    public_surface_report,
    realized_counterfixtures,
    remaining_scope_report,
    report,
    sign_cell_report,
    weight_report,
)


def test_frozen_six_file_boundary_and_public_surface() -> None:
    frozen = freeze_report()
    assert frozen["files"] == 6
    assert frozen["all_match"] is True
    surface = public_surface_report()
    assert surface["public_theorems"] == 9
    assert surface["producer_importer_is_independent"] is False


def test_exact_threshold_order_stability() -> None:
    result = ordering_stability_report()
    assert result["minimum_separation"] == "247/3960"
    assert result["maximum_correction"] == "1171733/165"
    assert result["target_correction_cannot_reorder"] is True
    assert result["equal_root_pairs"] == 27
    assert result["all_equal_pairs_are_reflected"] is True


def test_all_weight_components_reconstruct() -> None:
    result = weight_report()
    assert result["triples"] == 1_035
    assert result["raw_gamma_signs"] == {"positive": 514, "negative": 521, "zero": 0}
    assert result["oriented_weight_components"] == {
        "positive": 1_539,
        "negative": 1_539,
        "zero": 27,
    }
    assert result["minimum_gamma"] == 2_160
    assert result["maximum_gamma"] == 4_070_625_913_172_821_209_661_440


def test_all_1035_sign_cells_and_exact_totals() -> None:
    result = sign_cell_report()
    assert result["totals"] == {
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
    assert result["quotient_sign_totals"] == {
        "open_mixed": 1_847,
        "open_positive": 285,
        "open_negative": 258,
        "open_zero": 0,
        "boundary_mixed": 699,
        "boundary_positive": 369,
        "boundary_negative": 287,
        "boundary_zero": 0,
    }


def test_nine_strict_slivers_and_eighteen_boundaries() -> None:
    result = one_sided_report()
    assert [(row["k"], tuple(row["indices"])) for row in result["rows"]] == [
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
    assert result["strict_slivers"] == 9
    assert result["strict_slivers_excluded"] == 9
    assert result["positive_zero_boundaries"] == 18
    assert result["zero_boundaries_excluded"] == 8
    assert result["zero_boundaries_live"] == 10


def test_uniform_one_sided_claim_has_exact_counterfixtures() -> None:
    coefficient = coefficient_counterfixture()
    assert coefficient["d"] == TARGET
    assert coefficient["weights"] == [4, 26, 15]
    assert coefficient["gamma"] == 57_240
    assert coefficient["term_signs"] == [-1, 1, -1]
    assert sum(coefficient["weighted_terms"]) == coefficient["gamma"]
    realized = realized_counterfixtures()
    assert [row["components"] for row in realized] == [[3, 5, 2], [4, 3, 11]]
    assert [row["d"] for row in realized] == [720, 11_484]
    assert all(row["all_local_lifts"] for row in realized)
    assert all(row["all_composed_lifts"] for row in realized)
    assert all(row["term_signs"] == [-1, 1, -1] for row in realized)
    assert all(not row["block_equation"] for row in realized)


def test_remaining_H_budgets_and_exact_live_scope() -> None:
    remaining = remaining_scope_report()
    assert [row["H_k"] for row in remaining["rows"]] == [
        212160590605173551323281417403147323796233912863684428,
        57046695925872527128812620336999351280253887202763,
        82747175828911780468168027732812182306888441,
        106758606375800441629531020205561424117038,
        13022519011656599698255286636722720,
        24979064466336593021876736560,
    ]
    assert remaining["mixed_open_cells"] == 2_381
    assert remaining["live_positive_zero_boundaries"] == 10
    assert remaining["remaining_size_lemma"] == "OPEN"
    assert remaining["finite_scan_is_lean_wrapped"] is False


def test_final_verdict_is_partial_PASS() -> None:
    result = report()
    assert result["verdict"] == "PASS partial package"
    assert result["safe_to_integrate_generic_lean"] is True
    assert result["finite_row_scan_attestation_ready"] is False
    assert result["closes_three_owner_branch"] is False
    assert result["closes_erdos_686"] is False
