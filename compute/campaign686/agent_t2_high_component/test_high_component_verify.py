from fractions import Fraction

import high_component_verify as verify


def test_exact_exponential_certificate_and_strict_gap() -> None:
    certificate = verify.exact_exponential_certificate()
    assert certificate == {
        "head": (8317, 2197),
        "tail": (21870, 103259),
        "total": (412769, 103259),
        "gap_to_four": (267, 103259),
    }
    assert Fraction(*certificate["total"]) < 4

    assert verify.uniform_inequality_certificate() == {
        "two_base": 0,
        "two_step_boundary": 7,
        "three_base": 43,
        "three_step_boundary": 39,
        "five_base_cleared": 30,
        "five_step_boundary": 11,
        "residual_boundary": 338,
        "component_size_boundary": 72,
    }


def test_top_level_valuation_split_is_exhaustive() -> None:
    for exponent in range(1, 10):
        labels = {
            verify.classify_max_valuation(2, exponent, maximum)
            for maximum in range(exponent + 5)
        }
        assert labels == {
            "unchanged_valuation_cannot_gain_two",
            "q_owner",
            "valuation_drop",
        }

        labels = {
            verify.classify_max_valuation(5, exponent, maximum)
            for maximum in range(exponent + 5)
        }
        assert labels == {
            "all_units_fixed_mod_p",
            "q_owner",
            "valuation_drop",
        }

    for exponent in range(3, 10):
        labels = {
            verify.classify_max_valuation(3, exponent, maximum)
            for maximum in range(exponent + 5)
        }
        assert labels == {
            "all_units_fixed_mod9",
            "half_q_owner_mod9",
            "q_owner_forces_3_divides_m",
            "valuation_drop",
        }


def test_all_modular_branches_are_exhaustively_reproduced() -> None:
    report = verify.modular_classification_report()

    assert report["branch_partition"] == {
        "2": {
            "unchanged_valuation_cannot_gain_two": 28,
            "q_owner": 7,
            "valuation_drop": 21,
        },
        "3": {
            "all_units_fixed_mod9": 20,
            "half_q_owner_mod9": 5,
            "q_owner_forces_3_divides_m": 5,
            "valuation_drop": 15,
        },
        "5": {
            "all_units_fixed_mod_p": 28,
            "q_owner": 7,
            "valuation_drop": 21,
        },
    }
    assert report["p3_low_units"] == 6
    assert report["p3_q_owner_candidates"] == 2
    assert report["p3_half_q_one"] == {"candidates": 36, "solutions": 18}
    assert report["p3_half_q_two"] == {"candidates": 108, "solutions": 0}

    assert all(
        row["solutions"] > 0
        for row in report["p_ge_5_owner_lifts"].values()
    )
    assert all(row["solutions"] > 0 for row in report["p2_owner_lifts"].values())
    assert all(
        row["solutions"] > 0 for row in report["p3_singleton_lifts"].values()
    )


def test_simple_component_conditions_imply_exact_hc() -> None:
    report = verify.sweep_simple_implies_exact()
    assert report["tested_components"] > 90_000
    assert report["simple_antecedent_cases"] > 10_000


def test_uniform_prime_power_family_includes_small_bases() -> None:
    report = verify.sweep_prime_power_family()
    assert report == {"cases": 13_875}

    # Freeze the first admissible exponent in the theorem, including p=2,3.
    for prime in (2, 3, 5, 47):
        d = prime**16
        assert verify.high_component_condition(16, d, prime, 16)


def test_hc_thresholds_and_strict_integer_boundaries() -> None:
    # lambda_2(16)=3, lambda_3(16)=2, lambda_5(16)=1.
    assert verify.lambda_p(16, 2) == 3
    assert verify.lambda_p(16, 3) == 2
    assert verify.lambda_p(16, 5) == 1
    assert verify.mu_3(16, 3) == 1

    assert verify.high_component_threshold(16, 2, 4) == 24 * 2**5
    assert verify.high_component_threshold(16, 3, 3) == 6 * 3**4
    assert verify.high_component_threshold(16, 5, 2) == 6 * 5**3

    # HC is non-strict at its hypothesis, while the derived positive residual
    # is strictly smaller than the same divisor.
    k, p, exponent = 16, 5, 4
    q = p**exponent
    d = q
    assert verify.residual_ceiling(k, d) <= verify.high_component_threshold(
        k, p, exponent
    )
    assert verify.high_component_condition(k, d, p, exponent)


def test_external_strip_is_quarantined_to_arithmetic_only() -> None:
    report = verify.external_strip_arithmetic_report()
    assert report["status"] == "EXTERNAL_PAPER_ONLY"
    assert report["sharp_ratio_boundary_margin"] == 12_079_280
    assert report["ordinary_strip_cases"] > 100_000
    assert report["k82_strip_cases"] > 0
