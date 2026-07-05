import json
import math
import subprocess
import sys

import pytest

from compute.kernel import (
    consecutive_kernel_holds,
    diagnose_squeezed_normalized_candidate,
    power_two_quotient_kernel_holds,
    scan_squeezed_normalized_case_i_kernel,
    scan_power_two_quotient_kernel,
    squeezed_normalized_case_i_kernel_holds,
    squeezed_row_one_candidates_discriminant,
    kernel_survivors_bruteforce,
    prime_power_factorization,
    scan_case_i_power_two_kernel,
    scan_kernel_crt,
    squeezed_candidate_original_row_three_obstructions,
    squeezed_candidate_original_row_three_obstruction_witnesses,
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


def test_crt_scan_can_include_quotient_gap_summary_on_request() -> None:
    default_result = scan_kernel_crt(15, 14, 120, min_t=4)
    result = scan_kernel_crt(
        15, 14, 120, min_t=4, include_quotient_gap_summary=True
    )
    assert "quotient_gap_summary" not in default_result
    assert "row_one_candidate_splits" not in result
    assert result["quotient_gap_summary"] == {
        "candidate_count": 15,
        "strict_lt_n2_count": 9,
        "non_strict_lt_n2_count": 6,
        "all_strict_lt_n2": False,
        "max_quotient_gap_gcd_product": 28,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": 2, "count": 4},
            {"quotient_gap_gcd_product": 4, "count": 5},
            {"quotient_gap_gcd_product": 14, "count": 3},
            {"quotient_gap_gcd_product": 28, "count": 3},
        ],
        "max_relative_product": {
            "t": 16,
            "n2": 14,
            "quotient_gap_gcd_product": 28,
        },
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


def test_kernel_cli_can_include_quotient_gap_summary() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--case-i-power-two",
            "--max-exponent",
            "5",
            "--include-quotient-gap-summary",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["quotient_gap_summary"]["all_strict_lt_n2"] is True
    assert payload["quotient_gap_summary"]["candidate_count"] == 1
    assert payload["quotient_gap_summary"]["max_relative_product"] == {
        "exponent": 5,
        "n": 96,
        "t": 20,
        "n2": 47,
        "quotient_gap_gcd_product": 1,
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


def test_case_i_power_two_family_scan_can_include_quotient_gap_summary() -> None:
    result = scan_case_i_power_two_kernel(62, include_quotient_gap_summary=True)
    assert "row_one_candidate_splits" not in result["instances"][3]
    assert result["quotient_gap_summary"] == {
        "candidate_count": 130,
        "strict_lt_n2_count": 130,
        "non_strict_lt_n2_count": 0,
        "all_strict_lt_n2": True,
        "max_quotient_gap_gcd_product": 115,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": 1, "count": 108},
            {"quotient_gap_gcd_product": 5, "count": 15},
            {"quotient_gap_gcd_product": 11, "count": 2},
            {"quotient_gap_gcd_product": 23, "count": 2},
            {"quotient_gap_gcd_product": 29, "count": 1},
            {"quotient_gap_gcd_product": 101, "count": 1},
            {"quotient_gap_gcd_product": 115, "count": 1},
        ],
        "max_relative_product": {
            "exponent": 5,
            "n": 96,
            "t": 20,
            "n2": 47,
            "quotient_gap_gcd_product": 1,
        },
    }
    assert result["instances"][3]["quotient_gap_summary"] == {
        "candidate_count": 1,
        "strict_lt_n2_count": 1,
        "non_strict_lt_n2_count": 0,
        "all_strict_lt_n2": True,
        "max_quotient_gap_gcd_product": 1,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": 1, "count": 1}
        ],
        "max_relative_product": {
            "exponent": 5,
            "n": 96,
            "t": 20,
            "n2": 47,
            "quotient_gap_gcd_product": 1,
        },
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


def test_squeezed_normalized_predicate_excludes_zero_row_degeneracy() -> None:
    F, X, u, g = 3, 20, 0, 0
    weakened_hypotheses = (
        F % 2 == 1
        and 3 <= F
        and X % 4 == 0
        and 0 < X - 2 * u
        and 4 * F <= X
        and 2 * (F * F) <= X
        and u * (X - u) == g * (F * X - 1)
        and (g * (X - 2 * u)) % (F * (X // 2) - 1) == 0
    )
    assert weakened_hypotheses
    assert not squeezed_normalized_case_i_kernel_holds(F, X, u, g)


def test_squeezed_normalized_predicate_has_positive_row_counterexample() -> None:
    F, X, u, g = 3, 432184014644, 186954166997, 35360510289
    gap = X - 2 * u
    half_row = F * (X // 2) - 1
    assert gap == 58275680650
    assert half_row == 648276021965
    assert u * (X - u) == g * (F * X - 1)
    assert g * gap == half_row * 3178673490
    assert squeezed_normalized_case_i_kernel_holds(F, X, u, g)


def test_diagnose_squeezed_normalized_candidate_classifies_original_digit_failure() -> None:
    diagnostic = diagnose_squeezed_normalized_candidate(
        3,
        432184014644,
        186954166997,
        35360510289,
        original_obstruction_prime_limit=11,
    )
    assert diagnostic == {
        "F": 3,
        "X": 432184014644,
        "t": 186954166997,
        "g": 35360510289,
        "n": 1296552043932,
        "j": 560862500991,
        "row_one_holds": True,
        "squeezed_normalized_case_i_kernel_holds": True,
        "original_row_three_point_in_range": True,
        "original_obstruction_prime_limit": 11,
        "original_row_three_obstruction_primes": [5, 11],
        "original_row_three_has_obstruction": True,
        "original_row_three_digit_compatible_under_cap": False,
    }


def test_squeezed_candidate_original_row_three_obstructions_find_digit_kill() -> None:
    F, X, u = 3, 432184014644, 186954166997
    assert squeezed_candidate_original_row_three_obstructions(F, X, u, 3) == []
    assert squeezed_candidate_original_row_three_obstructions(F, X, u, 5) == [5]
    assert squeezed_candidate_original_row_three_obstructions(F, X, u, 11) == [5, 11]


def test_squeezed_candidate_original_obstruction_witnesses_record_digit_levels() -> None:
    F, X, u = 3, 432184014644, 186954166997
    assert squeezed_candidate_original_row_three_obstruction_witnesses(
        F, X, u, 11
    ) == [
        {
            "prime": 5,
            "i_failure": {"level": 0, "k_digit": 3, "n_digit": 2},
            "j_failure": {"level": 1, "k_digit": 3, "n_digit": 1},
        },
        {
            "prime": 11,
            "i_failure": {"level": 0, "k_digit": 3, "n_digit": 2},
            "j_failure": {"level": 1, "k_digit": 10, "n_digit": 2},
        },
    ]


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


def test_power_two_quotient_predicate_checks_all_rows() -> None:
    assert power_two_quotient_kernel_holds(512, 3, 205, 41) is False
    assert power_two_quotient_kernel_holds(1024, 3, 111, 33) is False
    assert power_two_quotient_kernel_holds(12, 3, 2, 1) is False


def test_power_two_quotient_scan_matches_bruteforce() -> None:
    result = scan_power_two_quotient_kernel(max_exponent=10, max_b=101)
    brute_row_one = []
    brute_survivors = []
    for exponent in range(2, 11):
        A = 2**exponent
        for B in range(3, 102, 2):
            D = B * A - 1
            M = B * (A // 2) - 1
            for v in range(1, A // 2):
                product = v * (A - v)
                if product % D != 0:
                    continue
                h = product // D
                item = {"exponent": exponent, "A": A, "B": B, "v": v, "h": h}
                brute_row_one.append(item)
                if (h * (A - 2 * v)) % M == 0:
                    brute_survivors.append(item)
    assert result["mode"] == "power_two_quotient_kernel"
    assert result["algorithm"] == "power_two_quotient_divisor_split"
    assert result["row_one_candidate_count"] == len(brute_row_one) == 2
    assert result["survivor_count"] == len(brute_survivors) == 0
    assert result["row_one_candidates"] == brute_row_one
    assert result["survivors"] == []
    assert result["reduced_divisor_gap_summary"] == {
        "candidate_count": 2,
        "gap_holds_count": 2,
        "gap_failure_count": 0,
        "min_gap_margin": 726,
        "min_gap_candidate": {
            "exponent": 9,
            "A": 512,
            "B": 3,
            "v": 205,
            "h": 41,
            "r": 5,
            "s": 307,
            "l": 41,
            "m": 1,
            "alpha": 2,
            "beta": 184,
            "c": 2,
            "d": 1,
            "reduced_divisor": 767,
            "l_times_m": 41,
            "gap_margin": 726,
            "gap_holds": True,
        },
    }


def test_power_two_quotient_scan_rejects_inverted_exponent_range() -> None:
    with pytest.raises(ValueError, match="0 <= min_exponent <= max_exponent"):
        scan_power_two_quotient_kernel(max_exponent=4, max_b=101, min_exponent=5)


def test_power_two_quotient_scan_can_report_factorization_skips() -> None:
    result = scan_power_two_quotient_kernel(
        max_exponent=60,
        max_b=17,
        min_exponent=60,
        skip_factorization_failures=True,
    )

    assert result["instance_count"] == 8
    assert result["factorized_instance_count"] == 7
    assert result["skipped_instance_count"] == 1
    assert result["skipped_instances"] == [
        {
            "exponent": 60,
            "A": 2**60,
            "B": 17,
            "row_one_modulus": 17 * 2**60 - 1,
            "reason": "prime_power_factorization currently requires n < 2^64",
        }
    ]
    assert result["row_one_candidate_count"] == 3
    assert result["survivor_count"] == 0
    assert result["reduced_divisor_gap_summary"]["candidate_count"] == 3
    assert result["reduced_divisor_gap_summary"]["gap_failure_count"] == 0


def test_power_two_quotient_scan_is_strict_by_default_on_factorization_limit() -> None:
    with pytest.raises(ValueError, match=r"n < 2\^64"):
        scan_power_two_quotient_kernel(
            max_exponent=60,
            max_b=17,
            min_exponent=60,
        )


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


def test_squeezed_normalized_scan_can_include_original_obstruction_diagnostics() -> None:
    result = scan_squeezed_normalized_case_i_kernel(
        max_f=3,
        max_x=48,
        include_candidate_diagnostics=True,
        original_obstruction_prime_limit=11,
    )
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
            "original_n": 144,
            "original_j": 66,
            "original_obstruction_prime_limit": 11,
            "original_row_three_obstruction_primes": [3, 11],
            "original_row_three_has_obstruction": True,
        }
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


def test_squeezed_normalized_summary_can_include_original_obstruction_counts() -> None:
    result = scan_squeezed_normalized_case_i_kernel(
        max_f=9,
        max_x=120,
        include_candidate_summary=True,
        original_obstruction_prime_limit=11,
    )
    assert result["candidate_summary"]["original_row_three_obstruction_summary"] == {
        "prime_limit": 11,
        "candidate_count": 7,
        "with_obstruction_count": 7,
        "without_obstruction_count": 0,
        "first_obstruction_prime_histogram": [
            {"prime": 3, "count": 5},
            {"prime": 5, "count": 1},
            {"prime": 7, "count": 1},
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


def test_kernel_cli_can_scan_power_two_quotient_kernel() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--power-two-quotient-kernel",
            "--max-exponent",
            "10",
            "--max-b",
            "101",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "power_two_quotient_kernel"
    assert payload["row_one_candidate_count"] == 2
    assert payload["survivor_count"] == 0
    assert payload["reduced_divisor_gap_summary"]["gap_failure_count"] == 0
    assert payload["reduced_divisor_gap_summary"]["min_gap_margin"] == 726


def test_kernel_cli_can_report_power_two_factorization_skips() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--power-two-quotient-kernel",
            "--min-exponent",
            "60",
            "--max-exponent",
            "60",
            "--max-b",
            "17",
            "--skip-factorization-failures",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["instance_count"] == 8
    assert payload["factorized_instance_count"] == 7
    assert payload["skipped_instance_count"] == 1
    assert payload["skipped_instances"] == [
        {
            "exponent": 60,
            "A": 2**60,
            "B": 17,
            "row_one_modulus": 17 * 2**60 - 1,
            "reason": "prime_power_factorization currently requires n < 2^64",
        }
    ]
    assert payload["survivor_count"] == 0


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


def test_kernel_cli_can_include_squeezed_original_obstruction_diagnostics() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--squeezed-normalized-case-i",
            "--max-f",
            "3",
            "--max-x",
            "48",
            "--include-candidate-diagnostics",
            "--original-obstruction-prime-limit",
            "11",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["candidate_diagnostics"][0]["original_n"] == 144
    assert payload["candidate_diagnostics"][0]["original_j"] == 66
    assert payload["candidate_diagnostics"][0][
        "original_row_three_obstruction_primes"
    ] == [3, 11]


def test_kernel_cli_can_diagnose_single_squeezed_candidate() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.kernel",
            "--diagnose-squeezed-candidate",
            "--candidate-f",
            "3",
            "--candidate-x",
            "432184014644",
            "--candidate-t",
            "186954166997",
            "--candidate-g",
            "35360510289",
            "--original-obstruction-prime-limit",
            "11",
            "--include-original-obstruction-witnesses",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["squeezed_normalized_case_i_kernel_holds"] is True
    assert payload["original_row_three_obstruction_primes"] == [5, 11]
    assert payload["original_row_three_digit_compatible_under_cap"] is False
    assert payload["original_row_three_obstruction_witnesses"] == [
        {
            "i_failure": {"k_digit": 3, "level": 0, "n_digit": 2},
            "j_failure": {"k_digit": 3, "level": 1, "n_digit": 1},
            "prime": 5,
        },
        {
            "i_failure": {"k_digit": 3, "level": 0, "n_digit": 2},
            "j_failure": {"k_digit": 10, "level": 1, "n_digit": 2},
            "prime": 11,
        },
    ]
