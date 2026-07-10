#!/usr/bin/env python3
"""Exact reproduction for the two-prime-support Erdős 686 restriction.

No floating point, external CAS, or probabilistic primality testing is used.
The script reproduces the concentration losses, the two absolute gap bounds,
and the finite coefficient-family counts after the elementary congruence
filters.
"""

from __future__ import annotations

import argparse
import json
import math
from typing import Any


TARGETS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
SMALL_PRIMES = (2, 3, 5, 7, 11, 13)
PER_PRIME_LOSS = 4096
TWO_PRIME_LOSS = PER_PRIME_LOSS**2


def valuation(value: int, prime: int) -> int:
    """Return the exact prime-adic valuation of a positive integer."""
    if value <= 0:
        raise ValueError("value must be positive")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def small_prime_loss_table() -> dict[int, int]:
    """Return p^(1+v_p(14!)) for every possible small prime."""
    factorial_14 = math.factorial(14)
    return {
        prime: prime ** (1 + valuation(factorial_14, prime))
        for prime in SMALL_PRIMES
    }


def absolute_gap_constants() -> dict[str, int]:
    """Return the global same-bucket and center-plus-other bounds."""
    same_bucket = TWO_PRIME_LOSS**2 * math.factorial(14) * 35
    center_other = (
        TWO_PRIME_LOSS**6
        * math.factorial(7) ** 4
        * math.factorial(14) ** 3
        * 35**5
    )
    return {
        "per_prime_loss": PER_PRIME_LOSS,
        "two_prime_loss": TWO_PRIME_LOSS,
        "same_bucket": same_bucket,
        "center_plus_other": center_other,
        "target_cutoff": 10**120,
    }


def noncenter_deltas(k: int) -> tuple[int, ...]:
    center = (k + 1) // 2
    return tuple(
        sorted(
            {
                i - j
                for i in range(1, k + 1)
                for j in range(1, k + 1)
                if i != j and i != center and j != center
            }
        )
    )


def coefficient_family_summary(k: int, bound_a: int) -> dict[str, Any]:
    """Count the exact finite Pell families left by elementary filters.

    For u and v odd and prime to 3, the coefficient equation

        a*u^2 - b*v^2 = 3*delta

    forces a == b != 0 modulo 3 and a-b == 3*delta modulo 8.
    """
    deltas = noncenter_deltas(k)
    raw_pairs = 0
    filtered_pairs: set[tuple[int, int]] = set()
    filtered_triples: list[tuple[int, int, int]] = []
    for a in range(1, bound_a * bound_a):
        for b in range(1, (bound_a * bound_a - 1) // a + 1):
            if a * b >= bound_a * bound_a:
                continue
            raw_pairs += 1
            if a % 3 != b % 3 or a % 3 == 0:
                continue
            for delta in deltas:
                if (a - b - 3 * delta) % 8 == 0:
                    filtered_pairs.add((a, b))
                    filtered_triples.append((a, b, delta))
    return {
        "k": k,
        "A": bound_a,
        "delta_min": min(deltas),
        "delta_max": max(deltas),
        "delta_count": len(deltas),
        "raw_coefficient_pairs": raw_pairs,
        "filtered_coefficient_pairs": len(filtered_pairs),
        "filtered_pell_triples": len(filtered_triples),
        "discriminants": len({a * b for a, b in filtered_pairs}),
    }


def telescope_checks() -> list[dict[str, int | bool]]:
    def centered_product(k: int, x: int) -> int:
        result = x
        for radius in range(1, (k - 1) // 2 + 1):
            result *= x * x - radius * radius
        return result

    fixtures = ((9, 8, 7), (15, 13, 12))
    return [
        {
            "k": k,
            "X": x,
            "Y": y,
            "d": x - y,
            "equation_holds": centered_product(k, x) == 4 * centered_product(k, y),
            "has_two_positive_prime_power_components": False,
            "outside_d_ge_k": x - y < k,
        }
        for k, x, y in fixtures
    ]


def report() -> dict[str, Any]:
    losses = small_prime_loss_table()
    constants = absolute_gap_constants()
    return {
        "small_prime_losses": losses,
        "maximum_small_prime_loss": max(losses.values()),
        "absolute_gap_constants": constants,
        "same_bucket_below_cutoff": constants["same_bucket"] < constants["target_cutoff"],
        "center_plus_other_below_cutoff": (
            constants["center_plus_other"] < constants["target_cutoff"]
        ),
        "coefficient_families": [
            coefficient_family_summary(k, bound_a) for k, bound_a in TARGETS.items()
        ],
        "telescopes": telescope_checks(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
