from compute.campaign686.agent_gptpro_even_uniform import even_uniform_verify as verify


def test_lcm_and_centered_lcm_bounds() -> None:
    row = verify.lcm_audit(500)
    assert row["all_initial_lcm_bounds"]
    assert row["all_half_binomial_divisibilities"]
    assert row["all_sharp_half_binomial_divisibilities"]
    centered = verify.centered_lcm_audit(60)
    assert centered == {"max_k": 60, "cases": 240, "all_divisibilities": True}
    interval = verify.interval_compression_audit(20, 50)
    assert interval["cases"] == 1000
    assert interval["all_factorial_lcm_divisibilities"]


def test_both_uniform_strips_all_parities() -> None:
    row = verify.strip_audit(1200)
    assert row["rows_checked_all_parities"] == 945
    assert row["boundary"]["d"] == 341
    assert row["boundary"]["rhs_power_of_two_exponent"] == 2044
    assert row["extended_max_endpoint"] >= row["proposed_max_endpoint"]


def test_quadratic_strip_all_parities() -> None:
    row = verify.quadratic_strip_audit(800)
    assert row["first_nonempty_boundary"] == {"k": 18, "d": 18}
    assert row["all_parities"]
    assert row["rows_with_nonempty_strip"] == 783
    assert verify.quadratic_certificate(984, 4_480)
    assert verify.quadratic_certificate(244, 277)


def test_center_gcd_and_under_specified_B_counterexample() -> None:
    row = verify.exact_solution_audit()
    assert [entry["k"] for entry in row["even_d1_telescopes"]] == [6, 12]
    assert row["standalone_B_counterexample"] == {
        "k": 3,
        "n": 0,
        "d": 1,
        "H": 5,
        "equation": True,
        "twenty_three_le_eight_q": True,
    }


def test_mandatory_fixtures_and_strict_boundaries() -> None:
    row = verify.mandatory_fixture_audit()
    assert row["prefix_984"]["H"] == 6_359_517
    assert row["prefix_984"]["dominant_component_conditions"]
    assert row["prefix_984"]["extended_endpoint"] == 1640
    assert row["prefix_984"]["quadratic_strip_applies"]
    assert row["prefix_244"]["H"] == 97_526
    assert row["prefix_244"]["no_prime_base_above_k"]
    assert row["prefix_244"]["quadratic_strip_applies"]
    assert row["pseudo_22"]["gcd_d_H"] == 1
    assert not row["pseudo_22"]["quadratic_strip_applies"]
    assert row["boundary_d_eq_k_i_eq_k"]
