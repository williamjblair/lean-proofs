#!/usr/bin/env python3
"""Exact audit for the uniform large-odd two-prime Pell wrapper."""

from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction


def pell_coefficient(k: int) -> int:
    assert k >= 1
    return 3 * k + 2


def local_coefficients(k: int, i: int) -> tuple[int, int]:
    """Constant and linear coefficients of product_{j!=i}(z+j-i)."""
    assert 1 <= i <= k
    constant = 1
    linear = 0
    for j in range(1, k + 1):
        if j == i:
            continue
        offset = j - i
        linear = linear * offset + constant
        constant *= offset
    return constant, linear


def obstruction_identities(
    p_component: int,
    q_component: int,
    a: int,
    b: int,
    delta: int,
    ci: int,
    di: int,
    cj: int,
    dj: int,
) -> tuple[int, int]:
    """Return the exact errors in the two second-obstruction identities."""
    assert a * p_component**2 - b * q_component**2 == 3 * delta
    local_left = 3 * ci * a - 4 * di * q_component**2
    local_right = 3 * cj * b - 4 * dj * p_component**2
    obstruction_left = 3 * (ci * a * b + 4 * di * delta)
    obstruction_right = 3 * (cj * a * b - 4 * dj * delta)
    left_error = (
        b * local_left + 4 * di * a * p_component**2 - obstruction_left
    )
    right_error = (
        a * local_right + 4 * dj * b * q_component**2 - obstruction_right
    )
    return left_error, right_error


def reflected_zero_slope(k: int, i: int) -> Fraction:
    """The forced t=ab at a reflected simultaneous second-order zero."""
    assert k % 2 == 1
    assert 1 <= i < (k + 1) // 2
    return 4 * (k + 1 - 2 * i) * sum(
        (Fraction(1, r) for r in range(i, k - i + 1)),
        Fraction(0),
    )


def threshold_certificate() -> dict:
    first_live_k = 17
    assert pell_coefficient(first_live_k) == 53
    assert pell_coefficient(first_live_k) < first_live_k**2
    for k in range(4, 10_001):
        assert pell_coefficient(k) < k * k
    # Exact boundary showing k=3 is the last failure of A<k^2.
    assert pell_coefficient(3) == 11 > 3**2
    return {
        "first_large_odd_k": first_live_k,
        "first_A": pell_coefficient(first_live_k),
        "first_A_squared": pell_coefficient(first_live_k) ** 2,
        "first_center_gap_bound": pell_coefficient(first_live_k) ** 5,
        "A_lt_k_squared_from": 4,
    }


def window_implication_certificate() -> dict:
    checked = 0
    for k in range(17, 202, 2):
        for d in range(k, k + 40):
            # Check the exact upper endpoint admitted by 18*x < 13*k*d.
            x = (13 * k * d - 1) // 18
            assert 18 * x < 13 * k * d
            assert x < k * d
            checked += 1
    return {"boundary_cases": checked, "conclusion": "n+1 < k*d"}


def determinant_certificate(max_k: int = 201) -> dict:
    checked = 0
    zeros = 0
    nonreflected_zeros = []
    integer_full_component_slopes = []
    for k in range(17, max_k + 1, 2):
        coeffs = {i: local_coefficients(k, i) for i in range(1, k + 1)}
        for i in range(1, k + 1):
            ci, di = coeffs[i]
            for j in range(1, k + 1):
                if i == j:
                    continue
                cj, dj = coeffs[j]
                determinant = cj * di + ci * dj
                checked += 1
                if determinant != 0:
                    continue
                zeros += 1
                if j != k + 1 - i:
                    nonreflected_zeros.append((k, i, j))
                if i < j:
                    slope = Fraction(-4 * di * (i - j), ci)
                    assert slope == reflected_zero_slope(k, i)
                    if slope.denominator == 1:
                        integer_full_component_slopes.append(
                            (k, i, j, slope.numerator)
                        )
    assert not nonreflected_zeros
    assert not integer_full_component_slopes
    return {
        "max_k": max_k,
        "ordered_pairs_checked": checked,
        "determinant_zero_pairs": zeros,
        "all_zero_pairs_reflected": True,
        "integer_full_component_zero_slopes": integer_full_component_slopes,
    }


def denominator_scan(max_k: int = 1001) -> dict:
    checked = 0
    minimum_denominator: tuple[int, int, int, int] | None = None
    for k in range(5, max_k + 1, 2):
        harmonic = [Fraction(0)] * (k + 1)
        for r in range(1, k + 1):
            harmonic[r] = harmonic[r - 1] + Fraction(1, r)
        midpoint = (k + 1) // 2
        for i in range(1, midpoint):
            slope = 4 * (k + 1 - 2 * i) * (
                harmonic[k - i] - harmonic[i - 1]
            )
            assert slope.denominator > 1
            candidate = (slope.denominator, k, i, slope.numerator)
            if minimum_denominator is None or candidate < minimum_denominator:
                minimum_denominator = candidate
            checked += 1
    assert minimum_denominator is not None
    # The excluded k=3 boundary really has an integral zero slope.
    assert reflected_zero_slope(3, 1) == 12
    return {
        "max_k": max_k,
        "reflected_pairs_checked": checked,
        "integer_slopes": 0,
        "minimum_denominator_fixture": minimum_denominator,
        "excluded_k3_slope": 12,
    }


def audit() -> dict:
    ci, di = local_coefficients(17, 3)
    cj, dj = local_coefficients(17, 14)
    identity_errors = obstruction_identities(2, 3, 3, 1, 1, ci, di, cj, dj)
    assert identity_errors == (0, 0)
    report = {
        "threshold": threshold_certificate(),
        "window": window_implication_certificate(),
        "second_obstruction_identity_errors": identity_errors,
        "determinants": determinant_certificate(),
        "denominator_scan": denominator_scan(),
        "surviving_uniform_lemma": (
            "for odd k>=5 and 1<=i<(k+1)/2, "
            "4*(k+1-2*i)*sum_{r=i}^{k-i}(1/r) is not an integer"
        ),
    }
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    report["payload_sha256"] = hashlib.sha256(encoded).hexdigest()
    return report


def main() -> None:
    print(json.dumps(audit(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
