import json
import math
import subprocess
import sys

import pytest

from compute.kernel import (
    consecutive_kernel_holds,
    scan_squeezed_normalized_case_i_kernel,
    squeezed_normalized_case_i_kernel_holds,
    squeezed_row_one_candidates_discriminant,
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


def test_gpt_pro_shape_counterexample_is_pure_c2_survivor() -> None:
    n = 54_734_052
    n1 = n - 1
    n2 = n // 2 - 1
    t = 8_748_251

    assert n % 4 == 0
    assert n % 3 == 0
    assert n2 % 2 == 1
    assert n1 == 2 * n2 + 1
    assert math.gcd(n1, n2) == 1
    assert 2 * t <= n
    assert consecutive_kernel_holds(n1, n2, n, t, min_t=4)

    row_one_product = t * (t - 1)
    row_one_quotient, remainder = divmod(row_one_product, n1)
    assert remainder == 0
    assert row_one_quotient == 1_398_250

    row_one_quotient_gcd = math.gcd(row_one_quotient, n2)
    gap_gcd = math.gcd(t - 2, n2)
    assert row_one_quotient_gcd == 2_975
    assert gap_gcd == 9_199
    assert row_one_quotient_gcd * gap_gcd == n2
    assert math.gcd(row_one_product * (t - 2), n2) == n2


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


def test_squeezed_normalized_predicate_checks_all_rows() -> None:
    assert not squeezed_normalized_case_i_kernel_holds(3, 48, 22, 4)
    assert not squeezed_normalized_case_i_kernel_holds(3, 48, 22, 3)
    assert not squeezed_normalized_case_i_kernel_holds(3, 48, 24, 0)
    assert not squeezed_normalized_case_i_kernel_holds(3, 36, 8, 2)
    assert not squeezed_normalized_case_i_kernel_holds(2, 72, 16, 7)


def test_squeezed_discriminant_generator_finds_row_one_candidates() -> None:
    assert squeezed_row_one_candidates_discriminant(3, 48) == [
        {"F": 3, "X": 48, "t": 22, "g": 4}
    ]
    assert squeezed_row_one_candidates_discriminant(5, 112) == [
        {"F": 5, "X": 112, "t": 26, "g": 4}
    ]
    assert squeezed_row_one_candidates_discriminant(3, 52) == []


def test_squeezed_discriminant_generator_matches_bruteforce_row_one_stage() -> None:
    discriminant_candidates = []
    brute_candidates = []
    for f in range(1, 10):
        for x in range(1, 121):
            discriminant_candidates.extend(squeezed_row_one_candidates_discriminant(f, x))
            for t in range(1, x // 2 + 1):
                n = f * x
                n1 = n - 1
                product = t * (x - t)
                if (
                    n1 > 0
                    and f % 2 == 1
                    and f >= 3
                    and x % 4 == 0
                    and 4 * f <= x
                    and 2 * (f * f) <= x
                    and 2 * t < x
                    and product % n1 == 0
                ):
                    brute_candidates.append({"F": f, "X": x, "t": t, "g": product // n1})
    assert discriminant_candidates == brute_candidates


def test_squeezed_normalized_scan_matches_bruteforce() -> None:
    result = scan_squeezed_normalized_case_i_kernel(max_f=9, max_x=120)
    brute = []
    for f in range(1, 10):
        for x in range(1, 121):
            for t in range(1, x // 2 + 1):
                n1 = f * x - 1
                product = t * (x - t)
                if n1 <= 0 or product % n1 != 0:
                    continue
                g = product // n1
                if squeezed_normalized_case_i_kernel_holds(f, x, t, g):
                    brute.append({"F": f, "X": x, "t": t, "g": g})
    assert result["mode"] == "squeezed_normalized_case_i_kernel"
    assert result["algorithm"] == "bounded_discriminant_scan"
    assert result["max_f"] == 9
    assert result["max_x"] == 120
    assert result["survivors"] == brute
    assert result["candidate_count"] == 7
    assert result["survivor_count"] == len(brute) == 0


def test_squeezed_normalized_scan_records_empty_ranges() -> None:
    result = scan_squeezed_normalized_case_i_kernel(max_f=25, max_x=600)
    assert result["candidate_count"] == 80
    assert result["survivor_count"] == 0
    assert result["survivors"] == []


def test_squeezed_normalized_scan_can_include_candidate_diagnostics() -> None:
    default_result = scan_squeezed_normalized_case_i_kernel(max_f=9, max_x=120)
    result = scan_squeezed_normalized_case_i_kernel(
        max_f=9,
        max_x=120,
        include_candidate_diagnostics=True,
    )
    assert "candidate_diagnostics" not in default_result
    assert result["candidate_diagnostics"] == [
        {
            "F": 3,
            "X": 48,
            "t": 22,
            "g": 4,
            "half_row": 71,
            "gap": 4,
            "half_row_value": 16,
            "half_row_remainder": 16,
            "half_row_gcd": 1,
            "survives_half_row": False,
        },
        {
            "F": 3,
            "X": 96,
            "t": 14,
            "g": 4,
            "half_row": 143,
            "gap": 68,
            "half_row_value": 272,
            "half_row_remainder": 129,
            "half_row_gcd": 1,
            "survives_half_row": False,
        },
        {
            "F": 3,
            "X": 108,
            "t": 51,
            "g": 9,
            "half_row": 161,
            "gap": 6,
            "half_row_value": 54,
            "half_row_remainder": 54,
            "half_row_gcd": 1,
            "survives_half_row": False,
        },
        {
            "F": 3,
            "X": 112,
            "t": 45,
            "g": 9,
            "half_row": 167,
            "gap": 22,
            "half_row_value": 198,
            "half_row_remainder": 31,
            "half_row_gcd": 1,
            "survives_half_row": False,
        },
        {
            "F": 5,
            "X": 80,
            "t": 38,
            "g": 4,
            "half_row": 199,
            "gap": 4,
            "half_row_value": 16,
            "half_row_remainder": 16,
            "half_row_gcd": 1,
            "survives_half_row": False,
        },
        {
            "F": 5,
            "X": 112,
            "t": 26,
            "g": 4,
            "half_row": 279,
            "gap": 60,
            "half_row_value": 240,
            "half_row_remainder": 240,
            "half_row_gcd": 3,
            "survives_half_row": False,
        },
        {
            "F": 7,
            "X": 112,
            "t": 54,
            "g": 4,
            "half_row": 391,
            "gap": 4,
            "half_row_value": 16,
            "half_row_remainder": 16,
            "half_row_gcd": 1,
            "survives_half_row": False,
        },
    ]


def test_squeezed_normalized_scan_can_include_half_row_summary() -> None:
    result = scan_squeezed_normalized_case_i_kernel(
        max_f=9,
        max_x=120,
        include_candidate_summary=True,
    )
    assert result["candidate_summary"] == {
        "candidate_count": 7,
        "surviving_half_row_count": 0,
        "failed_half_row_count": 7,
        "half_row_gcd_histogram": [
            {"half_row_gcd": 1, "count": 6},
            {"half_row_gcd": 3, "count": 1},
        ],
    }


def test_kernel_cli_can_scan_squeezed_normalized_case_i_kernel() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--squeezed-normalized-case-i",
            "--max-f",
            "9",
            "--max-x",
            "120",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "squeezed_normalized_case_i_kernel"
    assert payload["candidate_count"] == 7
    assert payload["survivors"] == []


def test_kernel_cli_can_include_squeezed_candidate_summary() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--squeezed-normalized-case-i",
            "--max-f",
            "9",
            "--max-x",
            "120",
            "--include-candidate-summary",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["candidate_summary"]["half_row_gcd_histogram"] == [
        {"half_row_gcd": 1, "count": 6},
        {"half_row_gcd": 3, "count": 1},
    ]
