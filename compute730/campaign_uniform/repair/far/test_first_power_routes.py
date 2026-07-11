from fractions import Fraction

from compute730.campaign_uniform.repair.far.first_power_routes import (
    aligned_first_power_scan,
    improved_higher_power_certificate,
    r1_fixed_slope_grid,
    r1_short_block_scan,
    short_qs_non_top_obstruction,
    top_square_threshold_certificate,
)


def test_improved_higher_power_endpoint_payment() -> None:
    result = improved_higher_power_certificate()
    assert result["log5_lower_gt_eight_fifths"] is True
    assert result["minimum_block_power"] == 25
    assert result["endpoint_factor"] == Fraction(6, 5)
    assert result["four_branch_bound"] < Fraction(174, 625)
    assert result["strict_plus_higher_ceiling"] == Fraction(721, 2500)
    assert result["remaining_budget"] == Fraction(1779, 2500)


def test_two_mean_aligned_conjecture_is_false_but_eight_thirds_survives_grid() -> None:
    result = aligned_first_power_scan()
    assert result["cases"] == 18
    assert result["two_mean_bound_holds"] is False
    assert result["counterexample"] == {
        "branch": "Q",
        "p": 7,
        "r": 3,
        "a": 1,
        "maximum_aligned_hits": 23,
        "mean": Fraction(3072, 343),
        "ratio": Fraction(7889, 3072),
    }
    assert result["maximum_ratio"] == Fraction(7889, 3072)
    assert result["eight_thirds_bound_holds_on_grid"] is True


def test_r1_block_slope_is_owner_independent_mod_p() -> None:
    result = r1_fixed_slope_grid()
    assert result["fixtures"] == 588
    assert result["all_exact"] is True


def test_top_square_thresholds_and_predecessor_witnesses() -> None:
    result = top_square_threshold_certificate()
    assert result == {
        "q_threshold": 66,
        "q_predecessor_witness": {"p": 65, "c": 8},
        "s_threshold": 1856,
        "s_predecessor_witness": {"p": 1855, "c": 43},
    }


def test_short_qs_classes_are_not_deleted_by_top_two_digit_lemmas() -> None:
    result = short_qs_non_top_obstruction()
    assert result["X"] == 2**57
    assert result["p"] == 30_000_001
    assert result["prime"] is True
    assert result["rows"] == [
        {
            "branch": "Q",
            "k": 10,
            "x": 304_699_465,
            "c": 3_867_733,
            "linear_value": 116_031_993_867_733,
            "digits": [714_754, 12_202_043, 290_876],
            "root_class_length": 4_803_839_443,
            "critical_length": 8_892_451_300,
            "c_square_exceeds_p": True,
        },
        {
            "branch": "S",
            "k": 3,
            "x": 101_483_822,
            "c": 1_288_195,
            "linear_value": 38_645_851_288_195,
            "digits": [12_883_968, 343_247, 32_267],
            "root_class_length": 4_803_839_443,
            "critical_length": 8_892_451_300,
            "c_square_exceeds_p": True,
        },
    ]


def test_r1_inflated_main_survives_extended_exact_scan() -> None:
    result = r1_short_block_scan()
    assert result["cases"] == 328
    assert result["inflated_counterexamples"] == 0
    assert result["uninflated_counterexamples"] == 291
    assert result["worst_uninflated"]["p"] == 19
    assert result["worst_uninflated"]["branch"] == "S"
    assert result["worst_uninflated"]["maximum_hits"] == 56
    assert result["worst_uninflated"]["critical_length"] == 165
    assert result["worst_uninflated"]["maximum_start"] == 109
    assert result["worst_uninflated"]["ratio"] == Fraction(5054, 4125)
    assert result["worst_inflated"]["p"] == 751
    assert result["worst_inflated"]["branch"] == "S"
    assert result["worst_inflated"]["certified_ratio_to_target"] < 1
