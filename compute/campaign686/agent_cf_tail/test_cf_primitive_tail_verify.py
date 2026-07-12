from compute.campaign686.agent_cf_tail.cf_primitive_tail_verify import (
    EXPECTED_COUNTS,
    TARGET_K,
    full_report,
)
from compute.campaign686.agent_cf_tail.scale_newton_verify import (
    EXPECTED_DISCREPANCY_BOUNDS,
    full_report as newton_report,
)
from compute.campaign686.agent_cf_tail.scale_hensel_flexibility_verify import (
    GOOD_PRIMES,
    LIFT_PRECISION,
    SCALE_EXPONENT,
    full_report as hensel_report,
)
from compute.campaign686.agent_cf_tail.k5_runge_number_field_verify import (
    full_report as runge_report,
)


REPORT = full_report()
NEWTON_REPORT = newton_report()
HENSEL_REPORT = hensel_report()
RUNGE_REPORT = runge_report()


def test_exact_new_band_constants() -> None:
    band = REPORT["exact_band"]
    assert band["gap_lower_inclusive"] == 10**120
    assert band["gap_upper_exclusive"] == 10**166
    assert band["primitive_denominator_lower"] == 10**77
    assert band["denominator_margin"] > 0
    assert band["ratio_to_v_lt_11_gap_margin"] == 6161


def test_all_six_finite_cf_scale_scans_have_no_root() -> None:
    assert [row["k"] for row in REPORT["per_k"]] == list(TARGET_K)
    for row in REPORT["per_k"]:
        k = row["k"]
        assert row["counts"]["exact_roots"] == 0
        for key, expected in EXPECTED_COUNTS[k].items():
            assert row["counts"][key] == expected
        assert row["artifact"]["q_340"] > 11 * 10**166


def test_named_d1_telescopes_are_preserved() -> None:
    checks = REPORT["telescope_checks"]
    assert [(row["k"], row["u"], row["v"], row["d"]) for row in checks] == [
        (9, 8, 7, 1),
        (15, 13, 12, 1),
    ]
    for row in checks:
        assert row["z"] == 1
        assert row["floor_pin_holds"]
        assert row["scale_residual"] == 0
        assert row["centered_equation"]
        assert row["outside_disjoint_domain"]


def test_reverse_newton_discrepancy_bounds() -> None:
    for k, expected in EXPECTED_DISCREPANCY_BOUNDS.items():
        assert NEWTON_REPORT["bounds"][str(k)]["value"] == expected
    assert NEWTON_REPORT["exhaustive_sanity"]["pairs_checked"] == 79_817
    assert NEWTON_REPORT["exhaustive_sanity"]["largest_gcd"] == 60


def test_newton_coprime_strengthening_is_falsified() -> None:
    fixture = NEWTON_REPORT["stronger_coprime_claim_counterfixture"]
    assert fixture["gcd_z_q"] == 12
    assert fixture["bound"] == 1_200


def test_good_prime_third_and_fourth_orders_remain_hensel_flexible() -> None:
    assert [row["k"] for row in HENSEL_REPORT["rows"]] == list(TARGET_K)
    for row in HENSEL_REPORT["rows"]:
        assert row["prime"] == GOOD_PRIMES[row["k"]]
        assert row["lift_precision"] == LIFT_PRECISION
        assert row["primitive"] and row["correct_real_side"]
        assert row["third_order_full_scale_congruence"]
        assert row["fourth_order_full_scale_congruence"]
        assert row["fifth_order_full_scale_congruence"]
        assert row["valuations"]["gap"] == SCALE_EXPONENT
        assert row["valuations"]["center"] == SCALE_EXPONENT
        assert row["valuations"]["centered_residual"] == 3 * SCALE_EXPONENT
        assert row["valuations"]["constant_quotient"] == 0


def test_k5_runge_and_number_field_obstructions() -> None:
    irreducible = RUNGE_REPORT["infinity_irreducibility"]
    assert irreducible["prime"] == 11
    assert irreducible["monic_linear_divisors_checked"] == 11
    assert irreducible["monic_quadratic_divisors_checked"] == 121
    target = RUNGE_REPORT["target_scale_unit"]
    assert target["first_coarse_power_below_10^-166"] == 146
    assert target["power_145_still_not_below"]
    assert target["power_146_below"]
