from fractions import Fraction

import large_odd_pell_verify as verify


def test_exact_live_threshold_k17():
    row = verify.threshold_certificate()
    assert row == {
        "first_large_odd_k": 17,
        "first_A": 53,
        "first_A_squared": 2809,
        "first_center_gap_bound": 418_195_493,
        "A_lt_k_squared_from": 4,
    }


def test_window_implication_uses_c_equal_k():
    row = verify.window_implication_certificate()
    assert row["boundary_cases"] == 3_720
    assert row["conclusion"] == "n+1 < k*d"


def test_second_obstruction_algebra_fixture():
    ci, di = verify.local_coefficients(17, 3)
    cj, dj = verify.local_coefficients(17, 14)
    assert verify.obstruction_identities(2, 3, 3, 1, 1, ci, di, cj, dj) == (0, 0)


def test_determinant_zeros_are_exactly_reflected_in_scan():
    row = verify.determinant_certificate(101)
    assert row["all_zero_pairs_reflected"]
    assert row["integer_full_component_zero_slopes"] == []
    assert row["determinant_zero_pairs"] > 0


def test_reflected_denominator_obstruction_scan_and_k3_boundary():
    row = verify.denominator_scan(101)
    assert row["integer_slopes"] == 0
    assert row["excluded_k3_slope"] == 12
    assert verify.reflected_zero_slope(3, 1) == Fraction(12)


def test_full_audit_freezes_the_remaining_uniform_lemma():
    report = verify.audit()
    assert report["denominator_scan"]["max_k"] == 1001
    assert report["denominator_scan"]["integer_slopes"] == 0
    assert report["second_obstruction_identity_errors"] == (0, 0)
