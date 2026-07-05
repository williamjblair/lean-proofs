import json
import subprocess
import sys

from compute.kernel import (
    consecutive_kernel_holds,
    kernel_survivors_bruteforce,
    prime_power_factorization,
    scan_case_i_power_two_kernel,
    scan_kernel_crt,
)


def test_prime_power_factorization_exact() -> None:
    assert prime_power_factorization(1) == []
    assert prime_power_factorization(72) == [(2, 8), (3, 9)]
    assert prime_power_factorization(325) == [(5, 25), (13, 13)]


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
