from compute.campaign686.reflected_second_lift_hostile_verify import run_audit


def test_reflected_second_lift_hostile_audit() -> None:
    audit = run_audit()
    assert audit["cofactor_reflection_rows"] == 4_410
    assert audit["cubic_congruence_rows"] == 66_910
    assert audit["rejected_square_premise_rows"] > 0
    assert audit["even_bridge_survives_three_dividing_modulus"] is True
    assert audit["odd_bridge_survives_five_dividing_modulus"] is True


def test_target_range_congruence_only_pseudo_fixture() -> None:
    fixture = run_audit()["pseudo_fixture"]
    assert fixture["k"] == 16
    assert fixture["g"] == 2**80
    assert fixture["g_factorization"] == {"2": 80}
    assert fixture["components"] == [17, 19, 23]
    assert fixture["owners"] == [1, 7, 16]
    assert fixture["crt_n0"] == 23_283_505
    assert fixture["crt_u0"] == 6_954
    assert fixture["crt_t0"] == 6_421
    assert fixture["crt_s"] == 1_396_681_840_576
    assert fixture["n"] == 4_254_209_959_225_268_127_279_392_844
    assert fixture["d"] == 472_689_995_466_543_884_333_395_799
    assert fixture["target_ratio"] is True
    assert fixture["block_equation"] is False
    assert fixture["block_error_digits"] > 100
    assert all(row["raw_obstruction"] % row["component"] == 0 for row in fixture["rows"])
    assert all(
        row["composed_obstruction"] % row["component"] == 0
        for row in fixture["rows"]
    )
    assert [row["lifted_t_residue"] for row in fixture["hensel_rows"]] == [12, 18, 4]
    assert [row["derivative"] for row in fixture["hensel_rows"]] == [16, 6, 22]
    assert all(
        row["third_obstruction"] % row["component"] ** 2 == 0
        for row in fixture["rows"]
    )
    assert all(
        row["composed_third_obstruction"] % row["component"] ** 2 == 0
        for row in fixture["rows"]
    )
