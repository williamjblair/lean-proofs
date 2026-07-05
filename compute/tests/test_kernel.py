import json
import subprocess
import sys

import pytest

from compute.kernel import (
    consecutive_kernel_holds,
    kernel_survivors_bruteforce,
    prime_power_factorization,
    scan_case_i_power_two_kernel,
    scan_kernel_crt,
)


def _factorization_product(factors: list[tuple[int, int]]) -> int:
    product = 1
    for _prime, prime_power in factors:
        product *= prime_power
    return product


def test_prime_power_factorization_exact() -> None:
    assert prime_power_factorization(1) == []
    assert prime_power_factorization(72) == [(2, 8), (3, 9)]
    assert prime_power_factorization(325) == [(5, 25), (13, 13)]


def test_prime_power_factorization_handles_large_semiprime() -> None:
    n = 1_000_000_007 * 1_000_000_009
    factors = prime_power_factorization(n)
    assert factors == [
        (1_000_000_007, 1_000_000_007),
        (1_000_000_009, 1_000_000_009),
    ]
    assert _factorization_product(factors) == n


def test_prime_power_factorization_reconstructs_case_i_exponent_sixty_inputs() -> None:
    for n in [3 * (2**60) - 1, 3 * (2**59) - 1]:
        factors = prime_power_factorization(n)
        assert _factorization_product(factors) == n
        assert all(prime_power % prime == 0 for prime, prime_power in factors)


def test_prime_power_factorization_rejects_outside_deterministic_range() -> None:
    with pytest.raises(ValueError, match=r"n < 2\^64"):
        prime_power_factorization(2**64)


def test_kernel_predicate_uses_both_rows_and_bound() -> None:
    assert consecutive_kernel_holds(6, 5, 12, 6)
    assert not consecutive_kernel_holds(6, 5, 12, 5)
    assert not consecutive_kernel_holds(6, 5, 11, 6)


def test_crt_scan_matches_bruteforce_for_small_kernels() -> None:
    for n1, n2, bound in [(6, 5, 40), (10, 9, 80), (15, 14, 120), (21, 10, 150)]:
        crt = scan_kernel_crt(n1, n2, bound)
        brute = kernel_survivors_bruteforce(n1, n2, bound)
        assert crt["survivors"] == brute
        assert crt["survivor_count"] == len(brute)
        assert crt["row_one_class_count"] <= 2 ** len(prime_power_factorization(n1))


def test_crt_scan_reports_row_one_classes_before_filtering() -> None:
    result = scan_kernel_crt(15, 14, 120)
    assert result["mode"] == "kernel_crt"
    assert result["n1"] == 15
    assert result["n2"] == 14
    assert result["bound"] == 120
    assert result["row_one_class_count"] == 4
    assert result["row_one_candidate_count"] >= result["survivor_count"]
    assert result["survivors"] == kernel_survivors_bruteforce(15, 14, 120)


def test_crt_scan_can_apply_problem_lower_bound() -> None:
    result = scan_kernel_crt(15, 14, 120, min_t=4)
    assert result["min_t"] == 4
    assert result["row_one_candidate_count"] == 15
    assert result["survivor_count"] == 6
    assert result["survivors"] == [15, 16, 21, 30, 36, 51]
    assert result["survivors"] == kernel_survivors_bruteforce(15, 14, 120, min_t=4)
    assert not consecutive_kernel_holds(15, 14, 120, 1, min_t=4)


def test_crt_scan_can_include_row_one_candidates_on_request() -> None:
    default_result = scan_kernel_crt(15, 14, 120, min_t=4)
    result = scan_kernel_crt(
        15, 14, 120, min_t=4, include_row_one_candidates=True
    )
    expected_candidates = [
        6,
        10,
        15,
        16,
        21,
        25,
        30,
        31,
        36,
        40,
        45,
        46,
        51,
        55,
        60,
    ]
    assert "row_one_candidates" not in default_result
    assert result["row_one_candidates"] == expected_candidates
    assert result["row_one_candidate_count"] == len(expected_candidates)


def test_crt_scan_can_include_row_one_split_diagnostics_on_request() -> None:
    default_result = scan_kernel_crt(15, 14, 120, min_t=4)
    result = scan_kernel_crt(
        15, 14, 120, min_t=4, include_row_one_splits=True
    )
    assert "row_one_candidate_splits" not in default_result
    assert result["row_one_candidate_splits"][:3] == [
        {
            "t": 6,
            "zero_prime_powers": [3],
            "one_prime_powers": [5],
            "zero_product": 3,
            "one_product": 5,
            "row_one_quotient": 2,
            "row_one_quotient_gcd": 2,
            "gap_gcd": 2,
            "quotient_gap_gcd_product": 4,
            "quotient_gap_gcd_product_lt_n2": True,
            "row_two_remainder": 8,
            "row_two_gcd": 2,
            "survives_row_two": False,
        },
        {
            "t": 10,
            "zero_prime_powers": [5],
            "one_prime_powers": [3],
            "zero_product": 5,
            "one_product": 3,
            "row_one_quotient": 6,
            "row_one_quotient_gcd": 2,
            "gap_gcd": 2,
            "quotient_gap_gcd_product": 4,
            "quotient_gap_gcd_product_lt_n2": True,
            "row_two_remainder": 6,
            "row_two_gcd": 2,
            "survives_row_two": False,
        },
        {
            "t": 15,
            "zero_prime_powers": [3, 5],
            "one_prime_powers": [],
            "zero_product": 15,
            "one_product": 1,
            "row_one_quotient": 14,
            "row_one_quotient_gcd": 14,
            "gap_gcd": 1,
            "quotient_gap_gcd_product": 14,
            "quotient_gap_gcd_product_lt_n2": False,
            "row_two_remainder": 0,
            "row_two_gcd": 14,
            "survives_row_two": True,
        },
    ]
    assert [item["t"] for item in result["row_one_candidate_splits"]] == [
        6,
        10,
        15,
        16,
        21,
        25,
        30,
        31,
        36,
        40,
        45,
        46,
        51,
        55,
        60,
    ]


def test_crt_split_diagnostics_match_quotient_gap_factorization_when_odd() -> None:
    result = scan_kernel_crt(95, 47, 96, min_t=4, include_row_one_splits=True)
    splits = result["row_one_candidate_splits"]
    assert splits == [
        {
            "t": 20,
            "zero_prime_powers": [5],
            "one_prime_powers": [19],
            "zero_product": 5,
            "one_product": 19,
            "row_one_quotient": 4,
            "row_one_quotient_gcd": 1,
            "gap_gcd": 1,
            "quotient_gap_gcd_product": 1,
            "quotient_gap_gcd_product_lt_n2": True,
            "row_two_remainder": 25,
            "row_two_gcd": 1,
            "survives_row_two": False,
        }
    ]
    assert all(
        item["quotient_gap_gcd_product"] == item["row_two_gcd"] for item in splits
    )


def test_crt_scan_can_include_row_one_split_summary_on_request() -> None:
    default_result = scan_kernel_crt(15, 14, 120, min_t=4)
    result = scan_kernel_crt(
        15, 14, 120, min_t=4, include_row_one_split_summary=True
    )
    assert "row_one_split_summary" not in default_result
    assert result["row_one_split_summary"] == {
        "candidate_count": 15,
        "surviving_split_count": 6,
        "failed_split_count": 9,
        "row_two_gcd_histogram": [
            {"row_two_gcd": 2, "count": 9},
            {"row_two_gcd": 14, "count": 6},
        ],
    }


def test_kernel_cli_emits_json() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--n1",
            "15",
            "--n2",
            "14",
            "--bound",
            "120",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "kernel_crt"
    assert payload["survivors"] == kernel_survivors_bruteforce(15, 14, 120)


def test_kernel_cli_can_include_row_one_candidates() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--n1",
            "15",
            "--n2",
            "14",
            "--bound",
            "120",
            "--min-t",
            "4",
            "--include-row-one-candidates",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["row_one_candidates"] == [
        6,
        10,
        15,
        16,
        21,
        25,
        30,
        31,
        36,
        40,
        45,
        46,
        51,
        55,
        60,
    ]


def test_kernel_cli_can_include_row_one_split_diagnostics() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--n1",
            "15",
            "--n2",
            "14",
            "--bound",
            "120",
            "--min-t",
            "4",
            "--include-row-one-splits",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["row_one_candidate_splits"][0] == {
        "t": 6,
        "zero_prime_powers": [3],
        "one_prime_powers": [5],
        "zero_product": 3,
        "one_product": 5,
        "row_one_quotient": 2,
        "row_one_quotient_gcd": 2,
        "gap_gcd": 2,
        "quotient_gap_gcd_product": 4,
        "quotient_gap_gcd_product_lt_n2": True,
        "row_two_remainder": 8,
        "row_two_gcd": 2,
        "survives_row_two": False,
    }


def test_kernel_cli_can_include_row_one_split_summary() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--n1",
            "15",
            "--n2",
            "14",
            "--bound",
            "120",
            "--min-t",
            "4",
            "--include-row-one-split-summary",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["row_one_split_summary"] == {
        "candidate_count": 15,
        "surviving_split_count": 6,
        "failed_split_count": 9,
        "row_two_gcd_histogram": [
            {"row_two_gcd": 2, "count": 9},
            {"row_two_gcd": 14, "count": 6},
        ],
    }


def test_case_i_power_two_family_scan_matches_scalar_scans() -> None:
    result = scan_case_i_power_two_kernel(5)
    assert result["mode"] == "case_i_power_two_kernel"
    assert result["min_exponent"] == 2
    assert result["max_exponent"] == 5
    assert result["min_t"] == 4
    assert result["instance_count"] == 4
    expected = []
    for exponent in range(2, 6):
        n = 3 * (2**exponent)
        scan = scan_kernel_crt(n - 1, n // 2 - 1, n, min_t=4)
        expected.append({"exponent": exponent, "n": n, **scan})
    assert result["instances"] == expected
    assert result["survivor_count"] == sum(item["survivor_count"] for item in expected)


def test_kernel_cli_can_scan_case_i_power_two_family() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--case-i-power-two",
            "--max-exponent",
            "5",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "case_i_power_two_kernel"
    assert payload["max_exponent"] == 5
    assert payload["instances"] == scan_case_i_power_two_kernel(5)["instances"]


def test_case_i_power_two_family_scan_can_include_row_one_candidates() -> None:
    result = scan_case_i_power_two_kernel(
        5, min_exponent=5, include_row_one_candidates=True
    )
    assert result["instances"][0]["row_one_candidates"] == [20]
    assert result["instances"][0]["row_one_candidate_count"] == 1


def test_case_i_power_two_family_scan_can_include_row_one_splits() -> None:
    result = scan_case_i_power_two_kernel(
        5, min_exponent=5, include_row_one_splits=True
    )
    assert result["instances"][0]["row_one_candidate_splits"] == [
        {
            "t": 20,
            "zero_prime_powers": [5],
            "one_prime_powers": [19],
            "zero_product": 5,
            "one_product": 19,
            "row_one_quotient": 4,
            "row_one_quotient_gcd": 1,
            "gap_gcd": 1,
            "quotient_gap_gcd_product": 1,
            "quotient_gap_gcd_product_lt_n2": True,
            "row_two_remainder": 25,
            "row_two_gcd": 1,
            "survives_row_two": False,
        }
    ]


def test_case_i_power_two_family_scan_can_include_split_summary() -> None:
    result = scan_case_i_power_two_kernel(5, include_row_one_split_summary=True)
    assert result["row_one_split_summary"] == {
        "candidate_count": 1,
        "surviving_split_count": 0,
        "failed_split_count": 1,
        "row_two_gcd_histogram": [{"row_two_gcd": 1, "count": 1}],
    }
    assert result["instances"][-1]["row_one_split_summary"] == {
        "candidate_count": 1,
        "surviving_split_count": 0,
        "failed_split_count": 1,
        "row_two_gcd_histogram": [{"row_two_gcd": 1, "count": 1}],
    }


def test_case_i_power_two_family_scan_reaches_exponent_sixty() -> None:
    result = scan_case_i_power_two_kernel(60, min_exponent=60)
    assert result["mode"] == "case_i_power_two_kernel"
    assert result["min_exponent"] == 60
    assert result["max_exponent"] == 60
    assert result["instance_count"] == 1
    assert result["instances"][0]["exponent"] == 60
    assert result["instances"][0]["n"] == 3 * (2**60)
