#!/usr/bin/env python3
"""Independent hostile verifier for the frozen Erdős 730 first-power routes.

This module deliberately does not import ``first_power_routes.py`` or its
tests.  It rebuilds the branch maps, rational logarithm certificates, finite
scans, threshold arguments, and short/non-top witnesses from exact data.
NumPy is used only for bounded ``int64`` arrays after an explicit overflow
check; every reported comparison is integer or ``Fraction`` arithmetic.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import cache
import hashlib
from math import gcd, isqrt
import json
from pathlib import Path
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[4]

PRODUCER_HASHES = {
    "ErdosProblems/Erdos730FirstPowerRoutes.lean": (
        "ba313bb107c06cec137efced15da5a3c334c77082e981ac351b2d8db659d1825"
    ),
    "compute730/campaign_uniform/repair/far/first_power_routes.py": (
        "a63bb168682ba6aca047f35dd073c3c4d713cd20ee80367637865886cac43dc0"
    ),
    "compute730/campaign_uniform/repair/far/test_first_power_routes.py": (
        "bf2798b0cf28d53587df528aaa1a720f48d517e20c8eebac9c1b2b5b19b07495"
    ),
    "compute730/campaign_uniform/repair/far/first_power_routes_findings.md": (
        "d273db26c9fc15f6783e778e12df25d70cb4500f33b3042ab471c411e0abccc1"
    ),
    "docs/plans/2026-07-10-erdos730-first-power-short-top.md": (
        "9865c076593f273afbecc85828d1805f598784ab48a7ef67601d24432ac6e4a3"
    ),
}

T = 5289
A = 3024 * T * T

BRANCHES: dict[str, dict[str, Any]] = {
    "P": {
        "lam": 42 * T,
        "mu": 11,
        "den": 7,
        "num": lambda pa, c: 12 * pa * c * c - 41 * c,
        "u": lambda c0: 144 * T * c0,
        "b": -246 * T,
    },
    "Q": {
        "lam": 72 * T,
        "mu": 13,
        "den": 12,
        "num": lambda pa, c: 7 * pa * c * c + 41 * c,
        "u": lambda c0: 84 * T * c0,
        "b": 246 * T,
    },
    "R": {
        "lam": 28 * T,
        "mu": 5,
        "den": 14,
        "num": lambda pa, c: 54 * pa * c * c + 129 * c - 7,
        "u": lambda c0: 216 * T * c0,
        "b": 258 * T,
    },
    "S": {
        "lam": 72 * T,
        "mu": 19,
        "den": 12,
        "num": lambda pa, c: 7 * pa * c * c - 43 * c - 6,
        "u": lambda c0: 84 * T * c0,
        "b": -258 * T,
    },
}


def verify_producer_hashes() -> dict[str, Any]:
    rows = []
    for relative_path, expected in PRODUCER_HASHES.items():
        actual = hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()
        rows.append(
            {
                "path": relative_path,
                "expected": expected,
                "actual": actual,
                "matches": actual == expected,
            }
        )
    return {
        "files": len(rows),
        "all_match": all(row["matches"] for row in rows),
        "rows": rows,
    }


def primes_through(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def _atanh_log_bounds(z: Fraction, terms: int = 32) -> tuple[Fraction, Fraction]:
    if not Fraction(0) <= z < 1 or terms < 1:
        raise ValueError("invalid atanh parameters")
    lower = sum(
        (2 * z ** (2 * index + 1) / (2 * index + 1) for index in range(terms)),
        Fraction(0),
    )
    tail = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return lower, lower + tail


def log_bounds(integer: int) -> tuple[Fraction, Fraction]:
    if integer < 1:
        raise ValueError("log input must be positive")
    if integer == 1:
        return Fraction(0), Fraction(0)
    exponent = integer.bit_length() - 1
    power_two = 1 << exponent
    ln2_lower, ln2_upper = _atanh_log_bounds(Fraction(1, 3))
    residual = Fraction(integer - power_two, integer + power_two)
    residual_lower, residual_upper = _atanh_log_bounds(residual)
    return (
        exponent * ln2_lower + residual_lower,
        exponent * ln2_upper + residual_upper,
    )


def _ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def certified_block_length(p: int, r: int) -> int:
    lower_log, upper_log = log_bounds(p)
    scale = p**r * r * r
    lower = scale * lower_log * lower_log
    upper = scale * upper_log * upper_log
    candidate = _ceil_fraction(upper)
    if not Fraction(candidate - 1) < lower <= upper <= candidate:
        raise AssertionError("rational log bounds did not isolate the ceiling")
    return candidate


def root_data(branch: dict[str, Any], p: int, a: int) -> tuple[int, int]:
    pa = p**a
    lam = int(branch["lam"])
    mu = int(branch["mu"])
    if gcd(lam, p) != 1:
        raise ValueError("branch slope is not invertible")
    x0 = (-mu * pow(lam, -1, pa)) % pa
    c0 = (lam * x0 + mu) // pa
    if lam * x0 + mu != pa * c0:
        raise AssertionError("root lift changed")
    return x0, c0


def phi(branch: dict[str, Any], pa: int, c: int) -> int:
    numerator = int(branch["num"](pa, c))
    denominator = int(branch["den"])
    if numerator % denominator:
        raise AssertionError("branch Phi is not integral")
    return numerator // denominator


def forbidden_digit(branch_name: str, p: int) -> int:
    if branch_name in ("P", "Q"):
        return 0
    if branch_name in ("R", "S"):
        return (p - 1) // 2
    raise KeyError(branch_name)


def _restricted_mask(values: np.ndarray, p: int, digits: int) -> np.ndarray:
    H = (p + 1) // 2
    mask = np.ones(len(values), dtype=np.int8)
    work = values.copy()
    for _ in range(digits):
        mask &= work % p < H
        work //= p
    return mask


def _branch_period_mask(branch_name: str, p: int, r: int, a: int = 1) -> np.ndarray:
    branch = BRANCHES[branch_name]
    modulus = p ** (2 * r)
    if 2 * modulus * modulus >= 2**63:
        raise OverflowError("scan exceeds exact int64 envelope")
    pa = p**a
    _, c0 = root_data(branch, p, a)
    quadratic = A * pa % modulus
    linear = (pa * int(branch["u"](c0)) + int(branch["b"])) % modulus
    constant = phi(branch, pa, c0) % modulus
    k = np.arange(modulus, dtype=np.int64)
    values = ((quadratic * k % modulus) * k + linear * k + constant) % modulus
    restricted = _restricted_mask(values, p, 2 * r)
    exact_valuation = (
        (c0 % p) + (int(branch["lam"]) % p) * (k % p)
    ) % p != 0
    output_exact = values % p != forbidden_digit(branch_name, p)
    if not np.array_equal(exact_valuation, output_exact):
        raise AssertionError("exact valuation/output digit bridge failed")
    mask = (restricted & exact_valuation).astype(np.int8)
    H = (p + 1) // 2
    if int(mask.sum()) != (H - 1) * H ** (2 * r - 1):
        raise AssertionError("full-period exact count changed")
    return mask


def _maximum_periodic_window(mask: np.ndarray, width: int) -> tuple[int, int]:
    period = len(mask)
    full_periods, remainder = divmod(width, period)
    base = full_periods * int(mask.sum())
    if remainder == 0:
        return 0, base
    extended = np.concatenate((mask, mask[: remainder - 1])).astype(np.int64)
    prefix = np.concatenate((np.array([0], dtype=np.int64), np.cumsum(extended)))
    windows = prefix[remainder:] - prefix[:-remainder]
    start = int(windows.argmax())
    return start, base + int(windows[start])


@cache
def endpoint_budget_certificate() -> dict[str, Any]:
    log5_lower, _ = log_bounds(5)
    if not log5_lower > Fraction(8, 5):
        raise AssertionError("independent log(5)>8/5 certificate failed")

    minimum_block_power = 25
    # 256P-25(10P+6)=6P-150, nonnegative for every P>=25.
    endpoint_slack_at_minimum = (
        256 * minimum_block_power - 25 * (10 * minimum_block_power + 6)
    )
    if endpoint_slack_at_minimum != 0:
        raise AssertionError("critical endpoint split changed")

    checked_primes = [p for p in primes_through(1000) if p >= 5]
    partial = sum(
        (Fraction(p + 1, p * (p - 1) * (2 * p + 1)) for p in checked_primes),
        Fraction(0),
    )
    if not partial < Fraction(57, 1000):
        raise AssertionError("finite prime sum missed 57/1000")
    with_tail = partial + Fraction(1, 1000)
    if not with_tail < Fraction(29, 500):
        raise AssertionError("series plus tail missed 29/500")
    endpoint_factor = Fraction(6, 5)
    four_branch = 4 * endpoint_factor * with_tail
    ceiling = Fraction(174, 625)
    if not four_branch < ceiling:
        raise AssertionError("higher-power certificate missed 174/625")
    remaining = 1 - Fraction(1, 100) - ceiling
    if remaining != Fraction(1779, 2500):
        raise AssertionError("remaining budget changed")
    return {
        "log5_lower_gt_eight_fifths": True,
        "minimum_block_power": minimum_block_power,
        "endpoint_slack_at_minimum": endpoint_slack_at_minimum,
        "endpoint_factor": endpoint_factor,
        "checked_primes": len(checked_primes),
        "finite_prime_sum": partial,
        "tail_envelope": Fraction(1, 1000),
        "prime_series_with_tail": with_tail,
        "four_branch_exact_certificate": four_branch,
        "four_branch_ceiling": ceiling,
        "remaining_budget": remaining,
    }


def fixed_slope_fixture_grid() -> dict[str, Any]:
    fixtures = 0
    for branch in BRANCHES.values():
        for p in (5, 7, 11):
            # The identity is polynomial and does not require an admissible
            # branch root.  An arbitrary signed-safe coefficient fixture
            # therefore also checks branches whose slope is not a unit at 7.
            linear = p * int(branch["u"](2)) + int(branch["b"])
            constant = int(branch["mu"])
            for u in range(-3, 4):
                for z in range(-3, 4):
                    def polynomial(k: int) -> int:
                        return A * p * k * k + linear * k + constant

                    remainder = polynomial(u + p * z) - polynomial(u) - p * z * linear
                    expected = A * p**2 * (2 * u * z + p * z**2)
                    if remainder != expected or remainder % p**2:
                        raise AssertionError("fixed upper-slope identity failed")
                    fixtures += 1
    return {"fixtures": fixtures, "all_exact": True}


def _aligned_row(branch_name: str, p: int, r: int) -> dict[str, Any]:
    mask = _branch_period_mask(branch_name, p, r)
    block_power = p**r
    counts = mask.reshape((block_power, block_power)).sum(axis=1)
    maximum = int(counts.max())
    mean = Fraction(int(mask.sum()), block_power)
    return {
        "branch": branch_name,
        "p": p,
        "r": r,
        "maximum_aligned_hits": maximum,
        "mean": mean,
        "ratio": Fraction(maximum, 1) / mean,
    }


@cache
def aligned_first_power_hostile_scan() -> dict[str, Any]:
    rows = []
    for p, maximum_r in ((5, 5), (7, 4), (11, 3)):
        for r in range(2, maximum_r + 1):
            for branch_name in ("Q", "S"):
                rows.append(_aligned_row(branch_name, p, r))
    counterexamples = [row for row in rows if row["ratio"] > 2]
    worst = max(rows, key=lambda row: row["ratio"])
    if not counterexamples or worst["ratio"] > Fraction(8, 3):
        raise AssertionError("aligned hostile boundary changed")
    return {
        "cases": len(rows),
        "counterexample_count": len(counterexamples),
        "first_counterexample": counterexamples[0],
        "worst_counterexample": worst,
        "eight_thirds_holds_on_grid": all(
            row["ratio"] <= Fraction(8, 3) for row in rows
        ),
    }


def _r1_row(branch_name: str, p: int) -> dict[str, Any]:
    mask = _branch_period_mask(branch_name, p, 1)
    width = certified_block_length(p, 1)
    start, maximum = _maximum_periodic_window(mask, width)
    H = (p + 1) // 2
    ratio = Fraction(maximum * p**2, width * H**2)
    _, log_upper = log_bounds(p)
    target_factor = 1 + 1 / log_upper
    score = ratio / target_factor
    return {
        "branch": branch_name,
        "p": p,
        "critical_length": width,
        "maximum_start": start,
        "maximum_hits": maximum,
        "ratio": ratio,
        "score": score,
    }


@cache
def r1_short_block_hostile_scan() -> dict[str, Any]:
    rows = []
    for p in primes_through(1000):
        if p < 5 or p in (41, 43):
            continue
        for branch_name in ("Q", "S"):
            rows.append(_r1_row(branch_name, p))
    uninflated = [row for row in rows if row["ratio"] > 1]
    inflated = [row for row in rows if row["score"] > 1]
    worst_uninflated_row = max(rows, key=lambda row: row["ratio"])
    worst_inflated_row = max(rows, key=lambda row: row["score"])
    if inflated:
        raise AssertionError("inflated hostile scan found a counterexample")

    worst_uninflated = {
        key: worst_uninflated_row[key]
        for key in (
            "branch",
            "p",
            "critical_length",
            "maximum_start",
            "maximum_hits",
            "ratio",
        )
    }
    return {
        "cases": len(rows),
        "uninflated_counterexamples": len(uninflated),
        "inflated_counterexamples": len(inflated),
        "worst_uninflated": worst_uninflated,
        "worst_inflated": worst_inflated_row,
        # log(p)<log_upper implies 1+1/log_upper < 1+1/log(p).
        "log_upper_direction": True,
    }


def top_threshold_certificate() -> dict[str, Any]:
    q_threshold = 66
    q_split = 8
    q_polynomial = 5 * 9**2 - 41 * 9
    q_predecessor = {"p": 65, "c": 8}
    if not (
        41 * q_split < 5 * q_threshold
        and q_polynomial == 36
        and 10 * 9 - 36 > 0
        and q_predecessor["c"] ** 2 < q_predecessor["p"]
        and not 41 * q_predecessor["c"] < 5 * q_predecessor["p"]
    ):
        raise AssertionError("Q threshold split failed")

    s_threshold = 1856
    s_split = 43
    s_polynomial = 44**2 - 43 * 44 - 6
    s_predecessor = {"p": 1855, "c": 43}
    if not (
        43 * s_split + 6 < s_threshold
        and s_polynomial == 38
        and 2 * 44 - 42 > 0
        and s_predecessor["c"] ** 2 < s_predecessor["p"]
        and not 43 * s_predecessor["c"] + 6 < s_predecessor["p"]
    ):
        raise AssertionError("S threshold split failed")

    return {
        "q_threshold": q_threshold,
        "q_small_split_max": q_split,
        "q_large_polynomial_at_split": q_polynomial,
        "q_predecessor_witness": q_predecessor,
        "s_threshold": s_threshold,
        "s_small_split_max": s_split,
        "s_large_polynomial_at_split": s_polynomial,
        "s_predecessor_witness": s_predecessor,
        "universal_split_checks": True,
    }


def _base_p_digits(value: int, p: int) -> list[int]:
    if value < 0:
        raise ValueError("digits require a nonnegative integer")
    digits = []
    work = value
    while work:
        digits.append(work % p)
        work //= p
    return digits or [0]


@cache
def short_qs_non_top_witness() -> dict[str, Any]:
    X = 2**57
    p = 30_000_001
    if any(p % divisor == 0 for divisor in primes_through(isqrt(p))):
        raise AssertionError("p=30000001 is not prime")
    critical = certified_block_length(p, 1)
    H = (p + 1) // 2
    rows = []
    root_class_length = None
    for branch_name, k, expected_digits in (
        ("Q", 10, [714_754, 12_202_043, 290_876]),
        ("S", 3, [12_883_968, 343_247, 32_267]),
    ):
        branch = BRANCHES[branch_name]
        x0, c0 = root_data(branch, p, 1)
        first = x0 if x0 >= 1 else p
        length = 0 if first > X else 1 + (X - first) // p
        if root_class_length is None:
            root_class_length = length
        elif length != root_class_length:
            raise AssertionError("Q/S root-class lengths diverged")
        x = x0 + p * k
        c = c0 + int(branch["lam"]) * k
        linear_value = int(branch["lam"]) * x + int(branch["mu"])
        value = phi(branch, p, c)
        digits = _base_p_digits(value, p)
        if not (
            1 <= x <= X
            and length < critical
            and linear_value == p * c
            and c % p != 0
            and c**2 > p
            and digits == expected_digits
            and all(digit < H for digit in digits)
            and digits[0] != forbidden_digit(branch_name, p)
        ):
            raise AssertionError("short/non-top obstruction witness changed")
        rows.append(
            {
                "branch": branch_name,
                "k": k,
                "x": x,
                "c": c,
                "linear_value": linear_value,
                "phi": value,
                "digits": digits,
            }
        )
    return {
        "X": X,
        "p": p,
        "prime": True,
        "critical_length": critical,
        "root_class_length": root_class_length,
        "rows": rows,
    }


def _json_value(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, dict):
        return {key: _json_value(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_json_value(item) for item in value]
    return value


def full_audit_report() -> dict[str, Any]:
    hashes = verify_producer_hashes()
    if not hashes["all_match"]:
        raise AssertionError("frozen producer hash mismatch")
    endpoint = endpoint_budget_certificate()
    return {
        "producer_hashes": hashes,
        "endpoint_budget": endpoint,
        "fixed_slope": fixed_slope_fixture_grid(),
        "aligned_first_power": aligned_first_power_hostile_scan(),
        "r1_short_block": r1_short_block_hostile_scan(),
        "top_thresholds": top_threshold_certificate(),
        "short_qs_non_top": short_qs_non_top_witness(),
        "coverage_bridge": "OPEN",
        "residual_budget": endpoint["remaining_budget"],
        "finite_diagnostics_are_not_theorems": True,
        "verdict": "PASS partial proof; full gate OPEN",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(
        json.dumps(
            _json_value(full_audit_report()),
            indent=2 if args.pretty else None,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
