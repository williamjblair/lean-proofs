#!/usr/bin/env python3
"""Exact block restriction for the corrected Erdős 730 range ``a<=r``.

The quadratic map is written

``G(k)=A*p^a*k^2+(p^a*u+b)k+v`` modulo ``p^(2r)``.

On an aligned block ``k=u0+p^r*v0``, its low ``r`` output digits depend
only on ``u0``.  The p-adic isometry makes those digits a permutation, so
the exact-valuation restricted set has at most ``(H-1)H^(r-1)`` elements
in every aligned block.  This yields a deliberately coarse, but summable,
first-moment payment for the proper subrange ``2<=a<=r``.

All verdicts use integers or ``Fraction``.  NumPy arrays remain within
checked signed-64-bit bounds in the three finite hostile scans.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import cache
from math import gcd, isqrt
from pathlib import Path
import sys
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compute730.campaign_uniform.repair.far.far_fourier import (
    branch_forbidden_digit,
    certified_block_length,
    log_bounds,
)
from compute730.campaign_uniform.test_uniformity import (
    A,
    BRANCHES,
    phi,
    root_data,
)


def low_word_block_bound(p: int, r: int) -> int:
    if p < 5 or p % 2 == 0 or r < 1:
        raise ValueError("require odd p>=5 and r>=1")
    H = (p + 1) // 2
    return (H - 1) * H ** (r - 1)


def quadratic_value(
    quadratic_unit: int,
    pa: int,
    linear: int,
    constant: int,
    k: int,
) -> int:
    return quadratic_unit * pa * k * k + linear * k + constant


def quadratic_derivative(
    quadratic_unit: int, pa: int, linear: int, k: int
) -> int:
    return 2 * quadratic_unit * pa * k + linear


def block_identity_fixture_grid() -> dict[str, object]:
    checks = 0
    for branch in BRANCHES.values():
        for p in (5, 7, 11):
            for a in (1, 2, 3):
                pa = p**a
                linear = pa * int(branch["u"](2)) + int(branch["b"])
                constant = int(branch["mu"])
                block = p**3
                for u in range(-3, 4):
                    for v in range(-3, 4):
                        left = quadratic_value(A, pa, linear, constant, u + block * v)
                        base = quadratic_value(A, pa, linear, constant, u)
                        derivative = quadratic_derivative(A, pa, linear, u)
                        remainder = left - base - block * v * derivative
                        expected = A * pa * block**2 * v**2
                        if remainder != expected or remainder % block**2:
                            raise AssertionError("quadratic block identity failed")
                        checks += 1
    return {"fixtures": checks, "all_exact": True}


def _restricted_mask(values: np.ndarray, p: int, digits: int) -> np.ndarray:
    H = (p + 1) // 2
    result = np.ones(len(values), dtype=np.int8)
    work = values.copy()
    for _ in range(digits):
        result &= work % p < H
        work //= p
    return result


def _maximum_periodic_window(mask: np.ndarray, width: int) -> tuple[int, int]:
    period = len(mask)
    if not 1 <= width < period:
        raise ValueError("finite scan expects 1<=width<period")
    extended = np.concatenate((mask, mask[: width - 1])).astype(np.int64)
    cumulative = np.concatenate(
        (np.array([0], dtype=np.int64), np.cumsum(extended))
    )
    windows = cumulative[width:] - cumulative[:-width]
    start = int(windows.argmax())
    return start, int(windows[start])


@cache
def corrected_case_scan(branch_name: str, p: int, r: int, a: int) -> dict[str, Any]:
    if branch_name not in BRANCHES:
        raise KeyError(branch_name)
    if p < 5 or p % 2 == 0 or r < 1 or not 1 <= a <= r:
        raise ValueError("require odd p>=5 and 1<=a<=r")
    branch = BRANCHES[branch_name]
    if gcd(int(branch["lam"]), p) != 1:
        raise ValueError("branch has no admissible p-adic root")

    half_period = p**r
    modulus = half_period**2
    if 2 * modulus * modulus >= 2**63:
        raise OverflowError("scan would exceed exact int64 multiplication")
    pa = p**a
    _, c0 = root_data(branch, p, a)
    quadratic = (A * pa) % modulus
    linear = (pa * int(branch["u"](c0)) + int(branch["b"])) % modulus
    constant = phi(branch, pa, c0) % modulus

    k = np.arange(modulus, dtype=np.int64)
    values = ((quadratic * k % modulus) * k + linear * k + constant) % modulus
    restricted = _restricted_mask(values, p, 2 * r)
    exact_valuation = (
        (c0 % p) + (int(branch["lam"]) % p) * (k % p)
    ) % p != 0
    output_exact = values % p != branch_forbidden_digit(branch_name, p)
    if not np.array_equal(exact_valuation, output_exact):
        raise AssertionError("exact valuation/output digit bridge failed")
    mask = (restricted & exact_valuation).astype(np.int8)

    H = (p + 1) // 2
    expected_period_count = (H - 1) * H ** (2 * r - 1)
    actual_period_count = int(mask.sum())
    if actual_period_count != expected_period_count:
        raise AssertionError("full-period exact count changed")

    block_counts = mask.reshape((half_period, half_period)).sum(axis=1)
    maximum_aligned = int(block_counts.max())
    aligned_bound = low_word_block_bound(p, r)
    if maximum_aligned > aligned_bound:
        raise AssertionError("low-word block bound failed")

    width = int(certified_block_length(p, r)["length"])
    start, maximum = _maximum_periodic_window(mask, width)
    main_numerator = width * H ** (2 * r)
    main_denominator = modulus
    ratio = Fraction(maximum * main_denominator, main_numerator)
    cover_bound = aligned_bound * (width // half_period + 2)
    return {
        "branch": branch_name,
        "p": p,
        "r": r,
        "a": a,
        "a_le_r": a <= r,
        "modulus": modulus,
        "critical_length": width,
        "maximum_start": start,
        "maximum_hits": maximum,
        "ratio": ratio,
        "maximum_hits_below_uninflated_main": ratio <= 1,
        "full_period_hits": actual_period_count,
        "full_period_count_exact": actual_period_count == expected_period_count,
        "maximum_aligned_block_hits": maximum_aligned,
        "aligned_block_bound": aligned_bound,
        "critical_block_cover_bound": cover_bound,
    }


def primes_through(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def higher_power_series_at_prime(p: int) -> Fraction:
    """Exact sum over every ``a>=2`` and every overcounted ``r>=a``.

    With ``H=(p+1)/2`` and
    ``rho_r=(H-1)H^(r-1)/p^r``, geometric summation gives

    ``sum_{a>=2} p^(-a) sum_{r>=a} rho_r
       = (p+1)/(p(p-1)(2p+1)).``
    """

    if p < 5 or p % 2 == 0:
        raise ValueError("require odd p>=5")
    return Fraction(p + 1, p * (p - 1) * (2 * p + 1))


@cache
def higher_power_first_moment_certificate() -> dict[str, Any]:
    log5_lower, _ = log_bounds(5)
    if not log5_lower > 1:
        raise AssertionError("exact logarithm lower bound no longer exceeds one")
    checked_primes = [prime for prime in primes_through(1000) if prime >= 5]
    partial = sum(
        (higher_power_series_at_prime(prime) for prime in checked_primes),
        Fraction(0, 1),
    )
    if not partial < Fraction(57, 1000):
        raise AssertionError("finite higher-power prime sum exceeded certificate")

    # For p>1000, S_p < 1/(p(p-1)).  Dropping primality and telescoping
    # over every integer n>=1001 costs exactly 1/1000.
    tail = Fraction(1, 1000)
    single_branch = partial + tail
    if not single_branch < Fraction(29, 500):
        raise AssertionError("single-branch series missed 29/500")

    # The factor two is the exact class-endpoint/block-cover payment, and
    # the factor four is for P,Q,R,S.  No branch independence is assumed.
    four_branch = 8 * single_branch
    if not four_branch < Fraction(58, 125):
        raise AssertionError("four-branch higher-power payment missed 58/125")
    return {
        "primes_through_1000": len(checked_primes),
        "largest_checked_prime": checked_primes[-1],
        "log5_lower_gt_one": True,
        "partial_prime_sum": partial,
        "partial_prime_sum_below": Fraction(57, 1000),
        "tail_bound": tail,
        "single_branch_series_bound": single_branch,
        "single_branch_rational_ceiling": Fraction(29, 500),
        "four_branch_normalized_bound": four_branch,
        "four_branch_rational_ceiling": Fraction(58, 125),
    }


def _json_value(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, dict):
        return {key: _json_value(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_json_value(item) for item in value]
    return value


def report() -> dict[str, Any]:
    scans = [
        corrected_case_scan("Q", 5, 5, 4),
        corrected_case_scan("Q", 7, 4, 1),
        corrected_case_scan("S", 11, 3, 1),
    ]
    return {
        "block_identity": block_identity_fixture_grid(),
        "new_exact_scans": scans,
        "higher_prime_power_first_moment": higher_power_first_moment_certificate(),
        "proved_subrange": "2<=a<=r",
        "remaining_range": "a=1 plus the independently open short/top budget",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(
        json.dumps(
            _json_value(report()),
            indent=2 if args.pretty else None,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
