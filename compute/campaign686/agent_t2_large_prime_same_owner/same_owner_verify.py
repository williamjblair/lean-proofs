#!/usr/bin/env python3
"""Exact arithmetic audit for the large-prime same-owner dominance lane."""

from __future__ import annotations

import hashlib
import json
import math


def dominance_ceiling(k: int, d: int) -> int:
    """The exact non-strict side opposed by the strict residual bound."""
    assert k >= 1 and d >= 1
    return (13 * k - 6) * d + 18 * (k - 1)


def least_dominant_component(k: int, d: int) -> int:
    """Least h with dominance_ceiling(k,d) <= 6*h^2."""
    target = dominance_ceiling(k, d)
    h = math.isqrt((target + 5) // 6)
    while 6 * h * h < target:
        h += 1
    while h > 0 and 6 * (h - 1) * (h - 1) >= target:
        h -= 1
    assert 6 * h * h >= target
    assert h == 0 or 6 * (h - 1) * (h - 1) < target
    return h


def whole_two_component_certificate(
    k: int, p: int, e: int, q: int, f: int
) -> dict[str, int]:
    """Certify the automatic dominance chain for d=p^e*q^f."""
    assert k >= 16
    assert p >= k and q >= k
    assert e >= 1 and f >= 1
    d = p**e * q**f
    lhs = dominance_ceiling(k, d)
    tail_relaxed = (13 * k - 6) * d + 18 * d
    coefficient_form = (13 * k + 12) * d
    rhs = 6 * d * d
    assert d >= k * k
    assert k <= d
    assert 18 * (k - 1) <= 18 * d
    assert tail_relaxed == coefficient_form
    assert 13 * k + 12 <= 6 * k * k <= 6 * d
    assert lhs <= tail_relaxed <= rhs
    return {
        "k": k,
        "p": p,
        "e": e,
        "q": q,
        "f": f,
        "d": d,
        "dominance_ceiling": lhs,
        "six_d_squared": rhs,
        "margin": rhs - lhs,
        "least_dominant_component": least_dominant_component(k, d),
    }


def audit() -> dict:
    boundary = whole_two_component_certificate(16, 17, 1, 19, 1)
    checked = 0
    minimum_margin: tuple[int, int, int, int, int, int] | None = None
    for k in range(16, 201):
        for p in range(k, k + 5):
            for q in range(k, k + 5):
                for e in range(1, 4):
                    for f in range(1, 4):
                        row = whole_two_component_certificate(k, p, e, q, f)
                        candidate = (row["margin"], k, p, e, q, f)
                        if minimum_margin is None or candidate < minimum_margin:
                            minimum_margin = candidate
                        checked += 1
    assert minimum_margin is not None
    report = {
        "exact_inequality":
            "6*h^2 < (13*k-6)*d+18*(k-1) for every localized square divisor",
        "dominance_obstruction":
            "(13*k-6)*d+18*(k-1) <= 6*h^2",
        "reused_aggregation":
            "globalResidualGroupedLeft_square_dvd_residual",
        "new_aggregate":
            "grouped-owner dominance and all-parity two-large-prime owner separation",
        "boundary": boundary,
        "sweep_cases": checked,
        "sweep_minimum_margin": minimum_margin,
    }
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    report["payload_sha256"] = hashlib.sha256(encoded).hexdigest()
    return report


def main() -> None:
    print(json.dumps(audit(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
