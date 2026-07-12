from pathlib import Path

import pytest

import all_owner_resultant_verify as verify


REPO_ROOT = Path(__file__).resolve().parents[3]


@pytest.fixture(scope="session")
def report():
    value = verify.build_report(REPO_ROOT)
    verify.assert_report(value)
    return value


def test_reconstructed_coefficients_match_all_60_lean_rows(report):
    table = report["lean_table_check"]
    assert table["expected_rows"] == 60
    assert table["parsed_second_rows"] == 60
    assert table["parsed_third_rows"] == 60
    assert table["mismatches"] == []


def test_all_42274_owner_subsets_and_2576_four_circuits(report):
    assert report["totals"] == {
        "target_owner_rows": 60,
        "subsets_size_4_through_k": 42274,
        "four_owner_circuits": 2576,
        "one_sided_sign_circuits": 0,
        "circuits_with_zero_weight": 4,
        "L_one_identity_failures": 0,
    }


def test_only_coefficient_rank_drop_is_k7_owners_2_4_6(report):
    observed = {
        row["k"]: row["zero_coefficient_triples"]
        for row in report["rows"]
        if row["zero_coefficient_triples"]
    }
    assert observed == {7: [(2, 4, 6)]}


def test_every_vandermonde_resultant_retains_common_term(report):
    for row in report["rows"]:
        assert row["L_one_identity_failures"] == []
        assert row["full_grid_D_degree"] == row["k"] - 2
        assert row["full_grid_E_degree"] == row["k"] - 3
        for check in row["nullspace_checks"].values():
            assert set(check["annihilated_moments"]) == {"0"}
            assert check["constant_survives"]
            assert check["constant_moment"] == check["expected_constant_moment"]


def test_polynomial_formula_matches_direct_integer_determinants(report):
    for row in report["rows"]:
        assert all(check["D_matches"] and check["E_matches"]
                   for check in row["direct_determinant_checks"])


def test_full_resultant_is_exact_third_order_block_truncation(report):
    for row in report["rows"]:
        assert row["full_grid_LD_equals_3V_e_k_minus_2"]
        assert row["full_grid_LE_equals_9V_e_k_minus_3"]
        assert row["block_expansion_identity"]
        assert row["block_d_coefficients_zero_through_three"] == {
            "d0_multiplier": -3,
            "d1_multiplier": 0,
            "d2_multiplier": 12,
            "d3_multiplier": 60,
        }
        assert row["high_remainder_minimum_d_degree"] == 4


def test_exact_k5_full_grid_window_fixture(report):
    fixture = report["k5_window_fixture"]
    assert fixture["gap_reconstruction_ok"]
    assert fixture["residual_decomposition_ok"]
    assert fixture["loss_bound_ok"]
    assert fixture["pairwise_coprime"]
    assert fixture["lower_window_ok"] and fixture["upper_window_ok"]
    assert fixture["step_three_ok"]
    assert fixture["all_subset_resultants_divisible"]
    for row in fixture["obstruction_rows"].values():
        assert row["O_nonzero"] and row["F_nonzero"]
        assert row["P_divides_O"]
        assert row["P_squared_divides_F"]
        assert row["third_sign_is_minus_C_sign"]
    assert fixture["block_equation_difference"] == -7091705934067167000000
    assert not fixture["block_equation_holds"]
    assert not fixture["target_cutoff_ok"]


def test_boundary_rows_and_unit_buckets_are_replayed(report):
    fixture = report["k5_window_fixture"]
    assert fixture["buckets"][4] == fixture["buckets"][5] == 1
    assert {row["k"] for row in report["rows"]} == set(verify.TARGET_K)
    assert all(row["exponent_excess_at_10_pow_120"] == 120 * (row["k"] - 4)
               for row in report["rows"])
    boundaries = report["named_boundary_replays"]
    assert all(row["block_equation_holds"] and not row["target_cutoff_ok"]
               for row in boundaries["d_equals_one_telescopes"])
    assert boundaries["three_owner_121_digit"] == {
        "gap_digits": 121,
        "all_local_checks": True,
        "all_composed_checks": True,
        "coarse_upper_residual_window": False,
        "block_equation_holds": False,
    }
    assert boundaries["four_owner_130_digit"] == {
        "gap_digits": 130,
        "all_local_checks": True,
        "all_composed_checks": True,
        "coarse_upper_residual_window": False,
        "block_equation_holds": False,
    }
