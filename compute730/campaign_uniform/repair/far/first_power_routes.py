#!/usr/bin/env python3
"""Two exact attack families for the remaining first-power #730 range.

Route A studies the maximum count in one aligned ``p^r`` block relative to
its exact mean.  It preserves an exact counterexample to the tempting
``2*mean`` bound and records the weaker finite boundary that survives.

Route B specializes to ``a=r=1``.  There the upper output digit changes by
the same fixed branch slope on every aligned block.  The script scans all
admissible Q/S cases through prime 1000 against the logarithmically inflated
main term, using a rational *upper* bound for ``log p`` so that the tested
right-hand side is no larger than the true one.

The module also sharpens the already-proved ``a>=2`` endpoint factor from
``2`` to ``6/5``.  Every verdict is integer or ``Fraction`` arithmetic.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import cache
from math import isqrt
from pathlib import Path
import sys
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compute730.campaign_uniform.repair.far.far_fourier import (
    _scan_case,
    certified_block_length,
    log_bounds,
)
from compute730.campaign_uniform.repair.far.unit_range_block import (
    corrected_case_scan,
    higher_power_first_moment_certificate,
    primes_through,
)
from compute730.campaign_uniform.test_uniformity import A, BRANCHES, phi, root_data


@cache
def improved_higher_power_certificate() -> dict[str, Any]:
    log5_lower, _ = log_bounds(5)
    if not log5_lower > Fraction(8, 5):
        raise AssertionError("log(5)>8/5 certificate failed")

    # For r>=a>=2, P=p^r>=25 and
    # N>=P(r log p)^2>P*(16/5)^2.  Hence N>=10P+6, which gives
    # (N+2P)/(N-1)<=6/5 in the root-class endpoint calculation.
    minimum_block_power = 25
    if 256 * minimum_block_power < 25 * (10 * minimum_block_power + 6):
        raise AssertionError("minimum critical block misses N>=10P+6")

    previous = higher_power_first_moment_certificate()
    single_branch_series = previous["single_branch_series_bound"]
    endpoint_factor = Fraction(6, 5)
    four_branch = 4 * endpoint_factor * single_branch_series
    ceiling = Fraction(174, 625)
    if not four_branch < ceiling:
        raise AssertionError("improved higher-power payment missed 174/625")
    strict_plus_higher = Fraction(1, 100) + ceiling
    remaining = 1 - strict_plus_higher
    if strict_plus_higher != Fraction(721, 2500) or remaining != Fraction(1779, 2500):
        raise AssertionError("budget arithmetic changed")
    return {
        "log5_lower_gt_eight_fifths": True,
        "minimum_block_power": minimum_block_power,
        "endpoint_factor": endpoint_factor,
        "single_branch_series_bound": single_branch_series,
        "four_branch_bound": four_branch,
        "four_branch_ceiling": ceiling,
        "strict_plus_higher_ceiling": strict_plus_higher,
        "remaining_budget": remaining,
    }


@cache
def aligned_first_power_scan() -> dict[str, Any]:
    fixtures = []
    for p, maximum_r in ((5, 5), (7, 4), (11, 3)):
        for r in range(2, maximum_r + 1):
            for branch in ("Q", "S"):
                fixtures.append((branch, p, r, 1))

    rows = []
    for branch, p, r, a in fixtures:
        scan = corrected_case_scan(branch, p, r, a)
        block_period = p**r
        mean = Fraction(scan["full_period_hits"], block_period)
        ratio = Fraction(scan["maximum_aligned_block_hits"], 1) / mean
        rows.append(
            {
                "branch": branch,
                "p": p,
                "r": r,
                "a": a,
                "maximum_aligned_hits": scan["maximum_aligned_block_hits"],
                "mean": mean,
                "ratio": ratio,
            }
        )
    worst = max(rows, key=lambda row: row["ratio"])
    counterexamples = [row for row in rows if row["ratio"] > 2]
    if not counterexamples:
        raise AssertionError("expected exact counterexample to 2*mean disappeared")
    if worst["ratio"] > Fraction(8, 3):
        raise AssertionError("8/3 finite diagnostic failed")
    return {
        "cases": len(rows),
        "two_mean_bound_holds": not counterexamples,
        "counterexample": worst,
        "counterexample_count": len(counterexamples),
        "maximum_ratio": worst["ratio"],
        "eight_thirds_bound_holds_on_grid": all(
            row["ratio"] <= Fraction(8, 3) for row in rows
        ),
    }


def r1_fixed_slope_grid() -> dict[str, object]:
    checks = 0
    for branch in BRANCHES.values():
        for p in (5, 7, 11):
            linear = p * int(branch["u"](2)) + int(branch["b"])
            constant = int(branch["mu"])
            for u in range(-3, 4):
                for z in range(-3, 4):
                    def polynomial(k: int) -> int:
                        return A * p * k * k + linear * k + constant

                    remainder = polynomial(u + p * z) - polynomial(u) - p * z * linear
                    expected = A * p**2 * (2 * u * z + p * z**2)
                    if remainder != expected or remainder % p**2:
                        raise AssertionError("r=1 fixed-slope identity failed")
                    checks += 1
    return {"fixtures": checks, "all_exact": True}


def top_square_threshold_certificate() -> dict[str, object]:
    """Exact threshold witnesses for the two conditional Q/S exclusions.

    The universal implications themselves are kernel-proved.  These integer
    checks record that lowering either natural-number threshold by one would
    fail without using primality.
    """

    q_threshold = 66
    q_witness = {"p": 65, "c": 8}
    if not q_witness["c"] ** 2 < q_witness["p"]:
        raise AssertionError("Q threshold witness left the two-digit regime")
    if 41 * q_witness["c"] < 5 * q_witness["p"]:
        raise AssertionError("Q threshold witness no longer falsifies the bound")

    s_threshold = 1856
    s_witness = {"p": 1855, "c": 43}
    if not s_witness["c"] ** 2 < s_witness["p"]:
        raise AssertionError("S threshold witness left the two-digit regime")
    if 43 * s_witness["c"] + 6 < s_witness["p"]:
        raise AssertionError("S threshold witness no longer falsifies the bound")

    return {
        "q_threshold": q_threshold,
        "q_predecessor_witness": q_witness,
        "s_threshold": s_threshold,
        "s_predecessor_witness": s_witness,
    }


def short_qs_non_top_obstruction() -> dict[str, object]:
    """Exact witness that Q/S short classes are not all top-two-digit classes."""

    X = 2**57
    p = 30_000_001
    if any(p % divisor == 0 for divisor in primes_through(isqrt(p))):
        raise AssertionError("short Q/S witness modulus is no longer prime")
    critical = int(certified_block_length(p, 1)["length"])
    H = (p + 1) // 2
    rows = []
    for branch_name, k, expected_digits in (
        ("Q", 10, [714_754, 12_202_043, 290_876]),
        ("S", 3, [12_883_968, 343_247, 32_267]),
    ):
        branch = BRANCHES[branch_name]
        x0, c0 = root_data(branch, p, 1)
        first = x0 if x0 >= 1 else p
        root_class_length = 0 if first > X else 1 + (X - first) // p
        x = x0 + p * k
        c = c0 + int(branch["lam"]) * k
        linear_value = int(branch["lam"]) * x + int(branch["mu"])
        value = phi(branch, p, c)
        digits = []
        work = value
        while work:
            digits.append(work % p)
            work //= p
        forbidden = 0 if branch_name == "Q" else H - 1
        if not (
            1 <= x <= X
            and linear_value == p * c
            and root_class_length < critical
            and c**2 > p
            and c % p != 0
            and digits == expected_digits
            and all(digit < H for digit in digits)
            and digits[0] != forbidden
        ):
            raise AssertionError("short non-top Q/S obstruction changed")
        rows.append(
            {
                "branch": branch_name,
                "k": k,
                "x": x,
                "c": c,
                "linear_value": linear_value,
                "digits": digits,
                "root_class_length": root_class_length,
                "critical_length": critical,
                "c_square_exceeds_p": True,
            }
        )
    return {"X": X, "p": p, "prime": True, "rows": rows}


def _short_row_summary(
    *, score: Fraction, ratio: Fraction, p: int, branch: str, row: dict[str, Any]
) -> dict[str, Any]:
    return {
        "p": p,
        "branch": branch,
        "maximum_hits": int(row["max_hits"]),
        "critical_length": int(row["width"]),
        "maximum_start": int(row["max_start"]),
        "ratio": ratio,
        "certified_ratio_to_target": score,
    }


@cache
def r1_short_block_scan() -> dict[str, Any]:
    rows = []
    for p in (
        prime for prime in primes_through(1000)
        if prime >= 5 and prime not in (41, 43)
    ):
        for branch in ("Q", "S"):
            row = _scan_case(branch, p, 1, 1)
            ratio = Fraction(
                int(row["max_hits"]) * int(row["main_denominator"]),
                int(row["main_numerator"]),
            )
            _, log_upper = log_bounds(p)
            # Since log(p)<log_upper, this denominator produces a smaller
            # allowance than the true 1+1/log(p).
            certified_target_factor = 1 + Fraction(1, 1) / log_upper
            score = ratio / certified_target_factor
            rows.append((score, ratio, p, branch, row))

    inflated_counterexamples = [entry for entry in rows if entry[0] > 1]
    uninflated_counterexamples = [entry for entry in rows if entry[1] > 1]
    worst_inflated = max(rows, key=lambda entry: entry[0])
    worst_uninflated = max(rows, key=lambda entry: entry[1])
    if inflated_counterexamples:
        raise AssertionError("finite r=1 inflated counterexample found")
    return {
        "cases": len(rows),
        "inflated_counterexamples": len(inflated_counterexamples),
        "uninflated_counterexamples": len(uninflated_counterexamples),
        "worst_inflated": _short_row_summary(
            score=worst_inflated[0],
            ratio=worst_inflated[1],
            p=worst_inflated[2],
            branch=worst_inflated[3],
            row=worst_inflated[4],
        ),
        "worst_uninflated": _short_row_summary(
            score=worst_uninflated[0],
            ratio=worst_uninflated[1],
            p=worst_uninflated[2],
            branch=worst_uninflated[3],
            row=worst_uninflated[4],
        ),
    }


def _json_value(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, dict):
        return {key: _json_value(item) for key, item in value.items()}
    return value


def report() -> dict[str, Any]:
    return {
        "improved_higher_power": improved_higher_power_certificate(),
        "aligned_first_power": aligned_first_power_scan(),
        "r1_fixed_slope": r1_fixed_slope_grid(),
        "top_square_thresholds": top_square_threshold_certificate(),
        "short_qs_non_top_obstruction": short_qs_non_top_obstruction(),
        "r1_short_block": r1_short_block_scan(),
        "verdict": (
            "higher-power budget sharpened; 2*mean aligned lemma falsified; "
            "a=1 uniform discrepancy and short/top budget remain open"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(_json_value(report()), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
