from compute.campaign686.fourth_local_lift_hostile_verify import (
    TARGET,
    coefficient_boundary_report,
    composition_grid,
    crt_witness,
    denominator_grid,
    exponent_family,
    report,
    sensitivity_witnesses,
)


EXPECTED_GAP = int(
    "8528006514942991411329818759017663024603296760011487105481658555774743359"
    "211568625230878556970868752918452276874633718401"
)
EXPECTED_THIRD_ONLY_RESIDUES = [
    439987804685666293694081422867534157888,
    7797703725030760165134404338142874334319,
    35218501497772032758465410169995205298447,
]


def test_reciprocal_coefficients_cover_centers_and_reflections() -> None:
    result = coefficient_boundary_report()
    assert result["total_owners"] == 60
    assert result["reflection_checks"] == 60
    assert result["taylor_remainder_checks"] == 420
    assert [row["center"] for row in result["rows"]] == [3, 4, 5, 6, 7, 8]
    assert all(row["center_D"] == row["center_F"] == 0 for row in result["rows"])


def test_denominator_clearing_keeps_every_correction_and_base_three() -> None:
    result = denominator_grid()
    assert result["exact_identity_checks"] == 15_120
    assert result["owner_component_three_checks"] == 3_240
    assert result["unit_component_checks"] == 3_960
    assert result["signed_checks"] == 12_720
    witness = sensitivity_witnesses()
    remainders = witness["omitted_local_correction_remainders_mod_H3"]
    assert remainders == {
        "minus_9_D_A2": 121,
        "plus_36_E_A_M2": 484,
        "plus_84_F_M4": 726,
    }


def test_cyclic_composition_requires_square_multiplier_and_6804() -> None:
    result = composition_grid()
    assert result["target_triples"] == 1_035
    assert result["cyclic_owner_positions"] == 3_105
    assert result["center_owner_positions"] == 251
    assert result["reflected_pair_triples"] == 251
    assert result["exact_composition_fixtures"] == 111_780
    assert result["owner_component_three_fixtures"] == 55_890
    assert result["coefficient_6804"] == 6_804
    witness = sensitivity_witnesses()["composition_fixture"]
    assert witness["single_bc_remainder"] == 552
    assert witness["wrong_756_remainder"] == 847
    assert witness["omitted_minus_108_remainder"] == 242


def test_target_size_hensel_crt_falsifier_is_directly_reproduced() -> None:
    witness = crt_witness(20)
    assert witness["gap"] == EXPECTED_GAP
    assert witness["gap"] >= TARGET
    assert witness["gap_digits"] == 121
    assert witness["n_digits"] == 604
    assert witness["third_derivatives_are_units"] is True
    assert witness["fourth_derivatives_are_units"] is True
    assert witness["third_only_fourth_quotient_residues"] == EXPECTED_THIRD_ONLY_RESIDUES
    assert witness["third_only_already_fourth"] is False
    assert witness["all_local_checks"] is True
    assert witness["all_composed_checks"] is True
    assert witness["all_residuals_positive"] is True
    assert all(
        check["direct_block_difference_mod_component_fifth"] == 0
        for check in witness["local_checks"]
    )
    assert witness["all_short_window_inequalities"] is False
    assert witness["short_window_checks"] == [False, False, False]
    assert witness["minimum_residual_to_gap_floor_digits"] == 484
    assert min(witness["residual_to_gap_floors"]) >= 10**483
    assert witness["block_equation"] is False


def test_route_is_proper_but_does_not_close_the_short_window() -> None:
    family = exponent_family()
    assert family["all_lifts_hold"] is True
    assert family["all_are_proper_nonshort_nonsolutions"] is True
    assert [row["gap_digits"] for row in family["rows"]] == [
        7,
        13,
        19,
        31,
        49,
        61,
        73,
        97,
        121,
        146,
    ]
    result = report()
    assert result["verdict"] == "PASS"
    assert result["route_scope"].startswith("proper one-owner-adic-digit strengthening")
