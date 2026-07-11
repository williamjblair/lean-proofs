from fractions import Fraction

from compute730.campaign_uniform.repair.far.first_power_routes_hostile_verify import (
    aligned_first_power_hostile_scan,
    endpoint_budget_certificate,
    fixed_slope_fixture_grid,
    full_audit_report,
    r1_short_block_hostile_scan,
    short_qs_non_top_witness,
    top_threshold_certificate,
    verify_producer_hashes,
)


def test_frozen_producer_hashes_match() -> None:
    result = verify_producer_hashes()
    assert result["all_match"] is True
    assert result["files"] == 5


def test_endpoint_and_remaining_budget_rederive_exactly() -> None:
    result = endpoint_budget_certificate()
    assert result["log5_lower_gt_eight_fifths"] is True
    assert result["minimum_block_power"] == 25
    assert result["endpoint_factor"] == Fraction(6, 5)
    assert result["prime_series_with_tail"] < Fraction(29, 500)
    assert result["four_branch_exact_certificate"] < Fraction(174, 625)
    assert result["four_branch_ceiling"] == Fraction(174, 625)
    assert result["remaining_budget"] == Fraction(1779, 2500)


def test_fixed_slope_identity_on_signed_grid() -> None:
    result = fixed_slope_fixture_grid()
    assert result == {"fixtures": 588, "all_exact": True}


def test_aligned_scan_reproduces_first_and_worst_two_mean_failures() -> None:
    result = aligned_first_power_hostile_scan()
    assert result["cases"] == 18
    assert result["counterexample_count"] == 10
    assert result["first_counterexample"] == {
        "branch": "Q",
        "p": 5,
        "r": 2,
        "maximum_aligned_hits": 5,
        "mean": Fraction(54, 25),
        "ratio": Fraction(125, 54),
    }
    assert result["worst_counterexample"] == {
        "branch": "Q",
        "p": 7,
        "r": 3,
        "maximum_aligned_hits": 23,
        "mean": Fraction(3072, 343),
        "ratio": Fraction(7889, 3072),
    }
    assert result["eight_thirds_holds_on_grid"] is True


def test_r1_scan_reproduces_falsifier_and_inflated_boundary() -> None:
    result = r1_short_block_hostile_scan()
    assert result["cases"] == 328
    assert result["uninflated_counterexamples"] == 291
    assert result["inflated_counterexamples"] == 0
    assert result["worst_uninflated"] == {
        "branch": "S",
        "p": 19,
        "critical_length": 165,
        "maximum_start": 109,
        "maximum_hits": 56,
        "ratio": Fraction(5054, 4125),
    }
    assert result["worst_inflated"]["branch"] == "S"
    assert result["worst_inflated"]["p"] == 751
    assert result["worst_inflated"]["critical_length"] == 32927
    assert result["worst_inflated"]["maximum_start"] == 42280
    assert result["worst_inflated"]["maximum_hits"] == 9095
    assert result["worst_inflated"]["score"] < 1
    assert result["log_upper_direction"] is True


def test_qs_top_thresholds_and_predecessor_witnesses() -> None:
    result = top_threshold_certificate()
    assert result == {
        "q_threshold": 66,
        "q_small_split_max": 8,
        "q_large_polynomial_at_split": 36,
        "q_predecessor_witness": {"p": 65, "c": 8},
        "s_threshold": 1856,
        "s_small_split_max": 43,
        "s_large_polynomial_at_split": 38,
        "s_predecessor_witness": {"p": 1855, "c": 43},
        "universal_split_checks": True,
    }


def test_prime_30000001_short_non_top_qs_witnesses() -> None:
    result = short_qs_non_top_witness()
    assert result["X"] == 2**57
    assert result["p"] == 30_000_001
    assert result["prime"] is True
    assert result["critical_length"] == 8_892_451_300
    assert result["root_class_length"] == 4_803_839_443
    assert result["rows"] == [
        {
            "branch": "Q",
            "k": 10,
            "x": 304_699_465,
            "c": 3_867_733,
            "linear_value": 116_031_993_867_733,
            "phi": 261_788_783_513_863_207_673,
            "digits": [714_754, 12_202_043, 290_876],
        },
        {
            "branch": "S",
            "k": 3,
            "x": 101_483_822,
            "c": 1_288_195,
            "linear_value": 38_645_851_288_195,
            "phi": 29_040_312_233_443_259_482,
            "digits": [12_883_968, 343_247, 32_267],
        },
    ]


def test_final_verdict_retains_open_bridge_and_residual() -> None:
    result = full_audit_report()
    assert result["verdict"] == "PASS partial proof; full gate OPEN"
    assert result["coverage_bridge"] == "OPEN"
    assert result["residual_budget"] == Fraction(1779, 2500)
    assert result["finite_diagnostics_are_not_theorems"] is True
