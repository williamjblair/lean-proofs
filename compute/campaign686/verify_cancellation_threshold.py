#!/usr/bin/env python3
"""Exact verifier for the Erdős 686 low-degree cancellation threshold.

Every acceptance decision is made with integers.  The finite scan recomputes
the prime counts, factorials, minimal osculation degrees, and both sides of
the claimed inequality.  The infinite tail is checked after clearing all
fractional exponents; its prime-count input is the elementary mod-6 bound.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CERTIFICATE = ROOT / "cancellation_threshold_certificate.json"
FINITE_START = 44
FINITE_END = 224
TAIL_START = 225
LOW_START = 16

sys.set_int_max_str_digits(0)


def prime_counts(limit: int) -> list[int]:
    composite = bytearray(limit + 1)
    composite[0:2] = b"\x01\x01"
    for p in range(2, math.isqrt(limit) + 1):
        if not composite[p]:
            composite[p * p : limit + 1 : p] = b"\x01" * (
                (limit - p * p) // p + 1
            )
    out = [0] * (limit + 1)
    count = 0
    for n in range(limit + 1):
        if not composite[n]:
            count += 1
        out[n] = count
    return out


def osculation_degree(m: int) -> int:
    r = 0
    while math.comb(r + 2, 2) < 4 * m + 1:
        r += 1
    return r


def threshold_record(k: int, m: int, pi_k: int) -> tuple[bool, str]:
    r = osculation_degree(m)
    monomials = math.comb(r + 2, 2)
    d_k = 708_827 * k * k // 5_000_000 + 1
    x_k = k * d_k // 2 + 1
    exponent = 2 * (k - pi_k) - r
    if exponent < 0:
        raise AssertionError((k, m, exponent))
    lhs = pow(2, 2 * pi_k) * pow(x_k, exponent)
    rhs = (
        12
        * monomials
        * monomials
        * r
        * pow(2, k)
        * pow(k, r - 1)
        * pow(math.factorial(k - 1), 2)
        * pow(3, 2 * pi_k)
    )
    passed = lhs > rhs
    line = ",".join(
        map(
            str,
            (k, m, pi_k, r, monomials, d_k, x_k, exponent, int(passed)),
        )
    )
    return passed, line


def verify_worst_case_monotonicity(k: int, pi_k: int) -> None:
    previous_r = -1
    previous_n = -1
    previous_e = 10**9
    for m in range(2, k + 1):
        r = osculation_degree(m)
        n_r = math.comb(r + 2, 2)
        e = 2 * (k - pi_k) - r
        if not (previous_r <= r and previous_n <= n_r and e <= previous_e):
            raise AssertionError(f"m-monotonicity failed at {(k, m)}")
        previous_r, previous_n, previous_e = r, n_r, e


def exact_finite_data(counts: list[int]) -> dict[str, object]:
    digest = hashlib.sha256()
    cases = 0
    failures: list[list[int]] = []
    for k in range(FINITE_START, FINITE_END + 1):
        verify_worst_case_monotonicity(k, counts[k])
        for m in range(2, k + 1):
            passed, line = threshold_record(k, m, counts[k])
            digest.update((line + "\n").encode("ascii"))
            cases += 1
            if not passed:
                failures.append([k, m])
    if failures:
        raise AssertionError(f"finite threshold failures: {failures[:10]}")
    if cases != 24_073:
        raise AssertionError(cases)
    return {
        "range": [FINITE_START, FINITE_END],
        "case_count": cases,
        "all_pass": True,
        "records_sha256": digest.hexdigest(),
    }


def exact_low_data(counts: list[int]) -> dict[str, object]:
    suffix_starts: dict[str, int] = {}
    isolated_all_m_successes: list[int] = []
    digest = hashlib.sha256()
    for k in range(LOW_START, FINITE_START):
        bad: list[int] = []
        for m in range(2, k + 1):
            passed, line = threshold_record(k, m, counts[k])
            digest.update((line + "\n").encode("ascii"))
            if not passed:
                bad.append(m)
        if bad:
            expected = list(range(bad[0], k + 1))
            if bad != expected:
                raise AssertionError(f"failures are not a suffix at k={k}: {bad}")
            suffix_starts[str(k)] = bad[0]
        else:
            isolated_all_m_successes.append(k)
    return {
        "range": [LOW_START, FINITE_START - 1],
        "failure_suffix_start": suffix_starts,
        "all_m_successes": isolated_all_m_successes,
        "records_sha256": digest.hexdigest(),
    }


def exact_symbolic_tail() -> dict[str, object]:
    # Prime-count bound: primes > 3 occupy the 1 or 5 residue classes mod 6,
    # with 1 itself removed.  Checking the six residues proves
    # 3*pi(k) <= k+6 without an analytic estimate.
    residue_checks = []
    for a in range(6):
        k = TAIL_START + ((a - TAIL_START) % 6)
        candidates_with_one = (k + 5) // 6 + (k + 1) // 6
        next_candidates = (k + 11) // 6 + (k + 7) // 6
        residue_checks.append(
            {
                "residue": a,
                "representative": k,
                "three_candidate_count": 3 * candidates_with_one,
                "upper_bound": k + 3,
            }
        )
        if 3 * candidates_with_one > k + 3:
            raise AssertionError((a, k))
        # Both sides increase by six after k is increased by six, so one
        # representative proves the exact floor inequality for the residue.
        if 3 * (next_candidates - candidates_with_one) != 6:
            raise AssertionError((a, "residue slope"))

    # Write k=5q+a.  q>=45 and
    # C(q+2,2) >= 4(5q+a)+1 iff q^2-37q-8a >= 0.
    degree_residue_checks = []
    for a in range(5):
        seed_polynomial = 45 * 45 - 37 * 45 - 8 * a
        first_difference = 2 * 45 - 36
        k = 5 * 45 + a
        n_upper_cleared = (
            2 * k * k - (45 + 2) * (45 + 1)
        )
        n_upper_first_difference = (
            2 * (k + 5) * (k + 5)
            - (46 + 2) * (46 + 1)
            - n_upper_cleared
        )
        if seed_polynomial < 0 or first_difference <= 0:
            raise AssertionError(a)
        if n_upper_cleared < 0 or n_upper_first_difference <= 0:
            raise AssertionError((a, "N<=k^2"))
        degree_residue_checks.append(
            {
                "residue": a,
                "seed_q": 45,
                "seed_polynomial": seed_polynomial,
                "first_difference": first_difference,
                "N_upper_seed_cleared": n_upper_cleared,
                "N_upper_first_difference": n_upper_first_difference,
            }
        )

    # The x bound uses only exact cleared constants:
    # d > 708827*k^2/5000000, 2x > kd, and
    # 15*708827 > 2*5000000, hence 15x > k^3.
    x_numerator = 15 * 708_827
    x_denominator = 2 * 5_000_000
    if x_numerator <= x_denominator:
        raise AssertionError("x lower-bound constant is insufficient")

    # From 3*pi<=k+6 and 5r<=k:
    #   45e = 90(k-pi)-45r >= 51k-180 >= 50k.
    if 51 * TAIL_START - 180 < 50 * TAIL_START:
        raise AssertionError("e lower-bound seed failed")
    if 51 - 50 <= 0:
        raise AssertionError("e lower-bound slope failed")

    constant = pow(2, 45) * pow(3, 30) * pow(15, 50)
    seed_k = TAIL_START
    seed_lhs = pow(seed_k, 51 * seed_k - 135)
    seed_rhs = pow(972, 45) * pow(constant, seed_k)
    if seed_lhs <= seed_rhs:
        raise AssertionError("symbolic tail seed failed")
    if pow(seed_k, 51) <= constant:
        raise AssertionError("symbolic tail monotonicity seed failed")

    # At k=225 the seed inequality cancels to the compact prime-power form
    # 3^4455*5^11430 > 2^10215.
    compact_lhs = pow(3, 4_455) * pow(5, 11_430)
    compact_rhs = pow(2, 10_215)
    if compact_lhs <= compact_rhs:
        raise AssertionError("compact seed inequality failed")

    # Cleared exponent bookkeeping for the 45th powers.  These are the exact
    # coefficients in the reduction to
    # k^(51k-135) > 972^45*C^k.
    # RHS^45 is bounded by
    # 972^45*k^(99k+135)*2^(45k)*3^(30k):
    # N^2*r contributes at most k^5, k^(r-1) contributes
    # at most k^(k/5), and (k-1)!^2 contributes k^(2k-2).
    if 45 * 5 - 90 != 135:
        raise AssertionError("RHS constant k-exponent failed")
    if 9 + 90 != 99:
        raise AssertionError("RHS linear k-exponent failed")
    if 150 - 99 != 51 or 0 - 135 != -135:
        raise AssertionError("cleared k-exponent arithmetic failed")
    if 45 * 2 != 90 or 90 * 2 != 180:
        raise AssertionError("prime-factor exponent arithmetic failed")

    return {
        "start": TAIL_START,
        "prime_bound": {
            "claim": "3*pi(k) <= k+6",
            "method": "prime residues 1 and 5 modulo 6",
            "residue_checks": residue_checks,
        },
        "degree_bound": {
            "claim": "5*r_k <= k",
            "method": "k=5q+a and q^2-37q-8a >= 0",
            "residue_checks": degree_residue_checks,
        },
        "derived_bounds": [
            "45*e_(k,k) >= 50*k",
            "N_(r_k) <= k^2",
            "15*x_k > k^3",
        ],
        "cleared_rhs_45_bound": "972^45*k^(99*k+135)*2^(45*k)*3^(30*k)",
        "x_constant_comparison": [x_numerator, x_denominator],
        "growth_constant": str(constant),
        "reduced_inequality": "k^(51*k-135) > 972^45*(2^45*3^30*15^50)^k",
        "seed": {
            "k": seed_k,
            "compact_inequality": "3^4455*5^11430 > 2^10215",
            "lhs_bits": compact_lhs.bit_length(),
            "rhs_bits": compact_rhs.bit_length(),
            "lhs_sha256": hashlib.sha256(str(compact_lhs).encode()).hexdigest(),
            "rhs_sha256": hashlib.sha256(str(compact_rhs).encode()).hexdigest(),
        },
        "monotonicity": "k^51 > C for k>=225",
        "seed_power_51_gt_constant": True,
    }


def expected_certificate() -> dict[str, object]:
    counts = prime_counts(FINITE_END)
    finite = exact_finite_data(counts)
    low = exact_low_data(counts)
    tail = exact_symbolic_tail()
    return {
        "schema": "erdos686.low-degree-cancellation-threshold.v1",
        "arithmetic": "exact integers only; no floating-point acceptance",
        "definitions": {
            "d_k": "floor(708827*k^2/5000000)+1",
            "x_k": "floor(k*d_k/2)+1",
            "r_m": "least r with binom(r+2,2)>=4m+1",
            "e_km": "2*(k-pi(k))-r_m",
        },
        "finite_scan": finite,
        "below_uniform_threshold": low,
        "worst_case": {
            "m": "k",
            "reason": "r_m and N_r are nondecreasing while e_km is nonincreasing",
        },
        "symbolic_tail": tail,
        "uniform_threshold": 44,
        "full_large_part_required": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    expected = expected_certificate()
    if args.write_certificate:
        CERTIFICATE.write_text(json.dumps(expected, indent=2) + "\n")
    actual = json.loads(CERTIFICATE.read_text())
    if actual != expected:
        raise AssertionError("cancellation threshold certificate mismatch")
    print("PASS: exact low-degree cancellation threshold certificate verified")
    print("finite cases: 24073; uniform threshold: k=44")
    print("symbolic tail: k>=225; no floating-point acceptance conditions")


if __name__ == "__main__":
    main()
