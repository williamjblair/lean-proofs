from fifth_local_lift_verify import TARGET, report


EXPECTED_GAP = int(
    "8528006514942991411329818759017663024603296760011487105481658555774743359211568625230878556970868752918452276874633718401"
)


def test_denominator_grid() -> None:
    result = report()["denominator_grid"]
    assert result["exact_denominator_identities"] == 10_080
    assert result["component_three_fixtures"] == 2_520
    assert result["signed_fixtures"] == 8_340
    assert result["omitted_quartic_term_detected"] > 0


def test_composition_and_quadratic_boundary() -> None:
    result = report()["composition_grid"]
    assert result["target_unordered_triples"] == 1_035
    assert result["cyclic_owner_positions"] == 3_105
    assert result["signed_composition_fixtures"] == 111_780
    assert result["component_three_fixtures"] == 55_890
    assert result["ordered_gap_quadratic_nonzero"] == 6_156
    assert result["ordered_gap_quadratic_zero"] == 54


def test_frozen_fourth_fixture_fails_fifth() -> None:
    replay = report()["crt_replay"]
    frozen = replay["fourth_fixture"]
    assert replay["gap"] == EXPECTED_GAP
    assert replay["gap"] >= TARGET
    assert any(frozen["local_fifth_remainders"])
    assert any(frozen["composed_fifth_remainders"])
    assert any(frozen["squared_quotient_remainders"])
    assert not frozen["block_equation"]
    assert not frozen["upper_window_holds"]


def test_fifth_crt_extension_survives_all_new_congruences() -> None:
    extended = report()["crt_replay"]["fifth_extension"]
    assert extended["fifth_derivatives_are_units"]
    assert extended["fifth_lift_nonzero"]
    assert extended["all_third_obstructions_nonzero"]
    assert extended["local_fifth_remainders"] == [0, 0, 0]
    assert extended["composed_fifth_remainders"] == [0, 0, 0]
    assert extended["squared_quotient_remainders"] == [0, 0, 0]
    assert extended["reduced_remainders"] == [0, 0, 0]
    assert extended["block_difference_mod_component_sixth"] == [0, 0, 0]
    assert not extended["block_equation"]
    assert not extended["upper_window_holds"]


def test_telescope_scope() -> None:
    rows = report()["telescope_boundary"]
    assert [(row["k"], row["n"], row["d"]) for row in rows] == [
        (9, 2, 1),
        (15, 4, 1),
    ]
    assert all(row["equation"] for row in rows)
    assert not any(row["target_domain"] for row in rows)
