#!/usr/bin/env python3
"""Exact algebra and finite hostile checks for the #730 far range.

Finite claims use integers or ``Fraction``.  NumPy is used only for arrays
of exact machine integers whose largest intermediate is checked to remain
well below ``int64`` in the hostile grid.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from math import gcd
import json
from pathlib import Path
import sys

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compute730.campaign_uniform.test_uniformity import (
    A,
    BRANCHES,
    phi,
    root_data,
)


def valuation(value: int, p: int) -> int:
    if value == 0 or p < 2:
        raise ValueError("require a nonzero value and p>=2")
    exponent = 0
    work = abs(value)
    while work % p == 0:
        exponent += 1
        work //= p
    return exponent


def branch_forbidden_digit(branch: str, p: int) -> int:
    if p < 5 or p % 2 == 0:
        raise ValueError("far campaign uses odd p>=5")
    if branch in ("P", "Q"):
        return 0
    if branch in ("R", "S"):
        return (p - 1) // 2
    raise KeyError(branch)


def restricted_exact_size(p: int, m: int) -> int:
    if p < 5 or m < 1:
        raise ValueError("require p>=5 and m>=1")
    H = (p + 1) // 2
    return (H - 1) * H ** (m - 1)


def restricted_exact_values(p: int, m: int, branch: str) -> list[int]:
    H = (p + 1) // 2
    forbidden = branch_forbidden_digit(branch, p)
    values = []
    for value in range(p**m):
        work = value
        accepted = True
        for digit_index in range(m):
            digit = work % p
            work //= p
            if digit >= H or (digit_index == 0 and digit == forbidden):
                accepted = False
                break
        if accepted:
            values.append(value)
    return values


def cumulative_fourier_energy(p: int, m: int, v: int) -> int:
    """Energy over frequencies divisible by ``p^v``, for ``0<=v<m``."""

    if not 0 <= v < m:
        raise ValueError("require 0<=v<m")
    H = (p + 1) // 2
    # p^(m-v) times the number of pairs agreeing modulo p^(m-v).
    return p ** (m - v) * (H - 1) * H ** (m + v - 1)


def brute_cumulative_fourier_energy(p: int, m: int, branch: str, v: int) -> int:
    if not 0 <= v < m:
        raise ValueError("require 0<=v<m")
    modulus = p ** (m - v)
    buckets = Counter(value % modulus for value in restricted_exact_values(p, m, branch))
    return modulus * sum(count * count for count in buckets.values())


def _atanh_log_bounds(z: Fraction, terms: int) -> tuple[Fraction, Fraction]:
    """Bounds for ``log((1+z)/(1-z))`` with ``0<=z<1``."""

    if not Fraction(0, 1) <= z < Fraction(1, 1) or terms < 1:
        raise ValueError("invalid atanh series parameters")
    lower = Fraction(0, 1)
    for index in range(terms):
        lower += 2 * z ** (2 * index + 1) / (2 * index + 1)
    tail = (
        2
        * z ** (2 * terms + 1)
        / ((2 * terms + 1) * (1 - z * z))
    )
    return lower, lower + tail


def log_bounds(integer: int, terms: int = 32) -> tuple[Fraction, Fraction]:
    """Rigorous rational lower and upper bounds for the natural logarithm."""

    if integer < 1:
        raise ValueError("integer must be positive")
    if integer == 1:
        return Fraction(0, 1), Fraction(0, 1)
    exponent = integer.bit_length() - 1
    power_two = 1 << exponent
    ln2_lower, ln2_upper = _atanh_log_bounds(Fraction(1, 3), terms)
    residual_z = Fraction(integer - power_two, integer + power_two)
    residual_lower, residual_upper = _atanh_log_bounds(residual_z, terms)
    return (
        exponent * ln2_lower + residual_lower,
        exponent * ln2_upper + residual_upper,
    )


def _ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def certified_block_length(p: int, r: int) -> dict[str, object]:
    """Certify ``ceil(p^r (log p^r)^2)`` without floating point."""

    if p < 2 or r < 1:
        raise ValueError("require p>=2 and r>=1")
    lower_log, upper_log = log_bounds(p)
    scale = p**r * r * r
    lower = scale * lower_log * lower_log
    upper = scale * upper_log * upper_log
    length = _ceil_fraction(upper)
    lower_strict = Fraction(length - 1, 1) < lower
    upper_weak = upper <= length
    if not lower_strict or not upper_weak:
        raise AssertionError("log interval does not certify a unique ceiling")
    return {
        "p": p,
        "r": r,
        "length": length,
        "lower": lower,
        "upper": upper,
        "lower_strict": lower_strict,
        "upper_weak": upper_weak,
    }


def is_separated_far(p: int, r: int, a: int) -> bool:
    """Exact test of ``s >= (kappa_p+1/12)r``."""

    if p < 5 or r < 1 or a < 1:
        raise ValueError("require p>=5 and r,a>=1")
    H = (p + 1) // 2
    s = max(2 * r - a, 0)
    return Fraction(p, 1) ** (12 * s - r) >= Fraction(p, H) ** (12 * r)


def completion_conductor(p: int, r: int, a: int, frequency_valuation: int) -> dict[str, int]:
    """Return the exact conductor data after removing ``p^v`` from h."""

    m = 2 * r
    if not 0 <= frequency_valuation < m:
        raise ValueError("require 0<=v<2r")
    n = m - frequency_valuation
    tau = min(n, a + valuation(A, p))
    return {
        "n": n,
        "tau": tau,
        "d": n - tau,
    }


def absolute_triangle_exponent_obstruction(p: int) -> bool:
    """Exact test of ``2*kappa_p > 1/2``.

    This is equivalent to ``p^3>H^4`` and identifies fixed primes for
    which the valuation-stratified triangle majorant is exponentially too
    large at critical length.
    """

    if p < 5:
        raise ValueError("require p>=5")
    H = (p + 1) // 2
    return p**3 > H**4


def long_interval_trivial_threshold(p: int, m: int) -> int:
    """Length at which full-period decomposition alone proves the target."""

    if p < 5 or m < 1:
        raise ValueError("require p>=5 and m>=1")
    H = (p + 1) // 2
    return (H - 1) * p**m


def _root_sum_equals_integer(
    coefficients: list[int], p: int, n: int, target: int
) -> bool:
    """Exact equality at a primitive ``p^n``-th root of unity."""

    modulus = p**n
    if len(coefficients) != modulus:
        raise ValueError("coefficient vector has the wrong length")
    adjusted = coefficients.copy()
    adjusted[0] -= target
    base = p ** (n - 1)
    for residue in range(base):
        value = adjusted[residue]
        if any(adjusted[residue + digit * base] != value for digit in range(1, p)):
            return False
    return True


def _phase_histogram(p: int, n: int, quadratic: int, linear: int) -> list[int]:
    modulus = p**n
    histogram = [0] * modulus
    for k in range(modulus):
        histogram[(quadratic * k * k + linear * k) % modulus] += 1
    return histogram


def _norm_squared_histogram(coefficients: list[int]) -> list[int]:
    modulus = len(coefficients)
    result = [0] * modulus
    support = [(index, value) for index, value in enumerate(coefficients) if value]
    for left_index, left_value in support:
        for right_index, right_value in support:
            result[(left_index - right_index) % modulus] += left_value * right_value
    return result


def gauss_sum_prediction(
    *, p: int, n: int, quadratic: int, linear: int
) -> dict[str, object]:
    modulus = p**n
    quadratic %= modulus
    linear %= modulus
    tau = n if quadratic == 0 else min(valuation(quadratic, p), n)
    if tau < n:
        supported = linear % (p**tau) == 0
        magnitude_squared = p ** (n + tau) if supported else 0
    else:
        supported = linear == 0
        magnitude_squared = modulus * modulus if supported else 0
    return {
        "tau": tau,
        "supported": supported,
        "magnitude_squared": magnitude_squared,
    }


def gauss_sum_prediction_holds_exactly(
    *,
    p: int,
    n: int,
    quadratic: int,
    linear: int,
    prediction: dict[str, object],
) -> bool:
    coefficients = _phase_histogram(p, n, quadratic, linear)
    if not prediction["supported"]:
        return _root_sum_equals_integer(coefficients, p, n, 0)
    norm_squared = _norm_squared_histogram(coefficients)
    return _root_sum_equals_integer(
        norm_squared,
        p,
        n,
        int(prediction["magnitude_squared"]),
    )


def _restricted_mask(values: np.ndarray, p: int, m: int) -> np.ndarray:
    H = (p + 1) // 2
    result = np.ones(len(values), dtype=np.int8)
    work = values.copy()
    for _ in range(m):
        result &= work % p < H
        work //= p
    return result


def _maximum_periodic_window(mask: np.ndarray, width: int) -> tuple[int, int]:
    period = len(mask)
    full_periods, remainder = divmod(width, period)
    base_count = full_periods * int(mask.sum())
    if remainder == 0:
        return 0, base_count
    extended = np.concatenate((mask, mask[: remainder - 1])).astype(np.int64)
    cumulative = np.concatenate(
        (np.array([0], dtype=np.int64), np.cumsum(extended))
    )
    windows = cumulative[remainder:] - cumulative[:-remainder]
    start = int(windows.argmax())
    return start, base_count + int(windows[start])


def _scan_case(branch_name: str, p: int, r: int, a: int) -> dict[str, object]:
    branch = BRANCHES[branch_name]
    m = 2 * r
    modulus = p**m
    if 2 * modulus * modulus >= 2**63:
        raise OverflowError("hostile grid would exceed exact int64 intermediates")
    pa = p**a
    _, c0 = root_data(branch, p, a)
    quadratic = (A * pa) % modulus
    linear = (pa * branch["u"](c0) + branch["b"]) % modulus
    constant = phi(branch, pa, c0) % modulus

    k = np.arange(modulus, dtype=np.int64)
    values = ((quadratic * k % modulus) * k + linear * k + constant) % modulus
    restricted = _restricted_mask(values, p, m)
    exact_valuation = (
        (c0 % p) + (branch["lam"] % p) * (k % p)
    ) % p != 0
    forbidden = branch_forbidden_digit(branch_name, p)
    output_exact = values % p != forbidden
    if not np.array_equal(exact_valuation, output_exact):
        raise AssertionError("exact valuation is not the claimed output digit deletion")
    mask = (restricted & exact_valuation).astype(np.int64)
    expected_period_count = restricted_exact_size(p, m)
    if int(mask.sum()) != expected_period_count:
        raise AssertionError("full-period exact count is wrong")

    width = int(certified_block_length(p, r)["length"])
    start, maximum = _maximum_periodic_window(mask, width)
    H = (p + 1) // 2
    return {
        "p": p,
        "r": r,
        "branch": branch_name,
        "a": a,
        "s": max(m - a, 0),
        "separated": is_separated_far(p, r, a),
        "modulus": modulus,
        "width": width,
        "max_start": start,
        "max_hits": maximum,
        "full_period_hits": expected_period_count,
        "main_numerator": width * H**m,
        "main_denominator": modulus,
        "quadratic_valuation": a + valuation(A, p),
    }


def scan_hostile_grid() -> list[dict[str, object]]:
    rows = []
    for p, maximum_r in ((5, 4), (7, 3), (11, 3)):
        for r in range(1, maximum_r + 1):
            for branch_name, branch in BRANCHES.items():
                if gcd(branch["lam"], p) != 1:
                    continue
                for a in range(1, 2 * r + 1):
                    if is_separated_far(p, r, a):
                        rows.append(_scan_case(branch_name, p, r, a))
    return rows


def main() -> None:
    rows = scan_hostile_grid()
    worst = max(
        rows,
        key=lambda row: Fraction(
            int(row["max_hits"]) * int(row["main_denominator"]),
            int(row["main_numerator"]),
        ),
    )
    ratio = Fraction(
        int(worst["max_hits"]) * int(worst["main_denominator"]),
        int(worst["main_numerator"]),
    )
    print(
        json.dumps(
            {
                "rows": len(rows),
                "all_at_most_uninflated_main": all(
                    int(row["max_hits"]) * int(row["main_denominator"])
                    <= int(row["main_numerator"])
                    for row in rows
                ),
                "worst": worst,
                "worst_ratio": f"{ratio.numerator}/{ratio.denominator}",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
