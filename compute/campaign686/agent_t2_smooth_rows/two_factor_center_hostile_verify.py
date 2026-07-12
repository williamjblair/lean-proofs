#!/usr/bin/env python3
"""Independent hostile verifier for the two-factor center slice.

No implementation is imported from ``two_factor_center.py``.  This script
recomputes the closed forms, product windows, factor search, residue tables,
and mandatory fixtures using exact integers.
"""

from __future__ import annotations

import json
from math import isqrt, prod


def run_audit() -> dict[str, int]:
    bounds = 0
    centers = 0
    oriented_large_pairs = 0
    large_supported_pairs = 0
    simultaneous_lifts = 0
    one_component_centers = 0

    for k in range(16, 39):
        for d in range(k, k + 7):
            for n in (9 * d + 1, 9 * d + 3, 11 * d + 5):
                s = 2 * n + d + k + 1
                owners = sorted({1, 2, k // 2, (k + 1) // 2, k - 1, k})
                lines = [
                    (5 * n + d + k + 1 + 3 * i)
                    if k % 2 == 0
                    else (3 * n - d - k - 1 + 5 * i)
                    for i in owners
                ]
                for a in lines:
                    for b in lines:
                        if k % 2 == 0:
                            assert 5 * s * s < a * b < 8 * s * s
                        else:
                            assert s * s < a * b < 4 * s * s
                        bounds += 1

    for k in range(16, 40):
        for d in range(k, k + 7):
            for n in range(9 * d + 1, 9 * d + 93):
                centers += 1
                s = 2 * n + d + k + 1
                modulus = 3 if k % 2 == 0 else 5
                line = (
                    (lambda i: 5 * n + d + k + 1 + 3 * i)
                    if k % 2 == 0
                    else (lambda i: 3 * n - d - k - 1 + 5 * i)
                )
                distinct_factors = []
                remaining = s
                trial = 2
                while trial * trial <= remaining:
                    if remaining % trial:
                        trial += 1
                        continue
                    distinct_factors.append(trial)
                    while remaining % trial == 0:
                        remaining //= trial
                    trial += 1
                if remaining > 1:
                    distinct_factors.append(remaining)
                if len(distinct_factors) == 1 and distinct_factors[0] > k:
                    one_component_centers += 1
                    assert all(0 < line(i) < s * s for i in range(1, k + 1))

                def supported(value: int) -> bool:
                    trial_value = value
                    trial_prime = 2
                    while trial_prime * trial_prime <= trial_value:
                        if trial_value % trial_prime:
                            trial_prime += 1
                            continue
                        if trial_prime <= k:
                            return False
                        while trial_value % trial_prime == 0:
                            trial_value //= trial_prime
                        trial_prime += 1
                    return trial_value == 1 or trial_value > k

                for q in range(1, isqrt(s) + 1):
                    if s % q:
                        continue
                    r = s // q
                    orientations = ((q, r),) if q == r else ((q, r), (r, q))
                    for x, y in orientations:
                        if x <= k or y <= k or x % modulus == 0 or y % modulus == 0:
                            continue
                        oriented_large_pairs += 1
                        if supported(x) and supported(y):
                            large_supported_pairs += 1
                        xs = [i for i in range(1, k + 1) if line(i) % (x * x) == 0]
                        ys = [j for j in range(1, k + 1) if line(j) % (y * y) == 0]
                        simultaneous_lifts += len(xs) * len(ys)

    # Reproduce the finite residue obstructions without using the producer.
    assert all((u - v) % 3 != 0 for u, v in ((1, 6), (2, 3), (3, 2), (6, 1)))
    residue_checks = 0
    for q in range(1, 5):
        for r in range(1, 5):
            q2, r2 = q * q % 5, r * r % 5
            for multiplier in (2, 3):
                assert q2 != multiplier * r2 % 5
                assert multiplier * q2 % 5 != r2
                residue_checks += 2

    # Mandatory boundary fixtures: exact products, no logarithms.
    def block(k: int, start: int) -> int:
        return prod(start + i for i in range(1, k + 1))

    for k, n, d in ((984, 3_177_026, 4_480), (244, 48_502, 277)):
        assert block(k, n + d) != 4 * block(k, n)
    assert 2 * 3_177_026 + 4_480 + 984 + 1 == 3**2 * 706_613
    assert 2 * 48_502 + 277 + 244 + 1 == 2 * 11**2 * 13 * 31

    assert simultaneous_lifts == 0
    return {
        "product_window_rows": bounds,
        "centers": centers,
        "oriented_large_factor_pairs": oriented_large_pairs,
        "large_supported_factor_pairs": large_supported_pairs,
        "simultaneous_square_lifts": simultaneous_lifts,
        "one_component_centers": one_component_centers,
        "mod_five_checks": residue_checks,
        "mandatory_fixtures": 2,
    }


if __name__ == "__main__":
    print(json.dumps(run_audit(), sort_keys=True))
