#!/usr/bin/env python3
"""Exact audit of the first reverse p-adic Newton step for Erdos 686."""

from __future__ import annotations

import json
import math
from typing import Any

from compute.campaign686.agent_cf_tail.cf_primitive_tail_verify import (
    TARGET_K,
    a_value,
    elementary_square_coefficients,
    scale_residual,
)
from compute.campaign686.scale_filter_counterfamily import counterfamily_point


EXPECTED_DISCREPANCY_BOUNDS = {
    5: 1_200,
    7: 105_840,
    9: 28_339_200,
    11: 18_209_664_000,
    13: 24_047_622_144_000,
    15: 58_528_432_134_144_000,
}


def prime_factorization(value: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    candidate = 2
    while candidate * candidate <= value:
        while value % candidate == 0:
            factors[candidate] = factors.get(candidate, 0) + 1
            value //= candidate
        candidate = 3 if candidate == 2 else candidate + 2
    if value > 1:
        factors[value] = factors.get(value, 0) + 1
    return factors


def discrepancy_bound(k: int) -> int:
    coefficients = elementary_square_coefficients(k)
    return 60 * coefficients[-1] * coefficients[-2]


def exhaustive_linear_cubic_gcd_check(limit: int = 500) -> dict[str, int]:
    checked = 0
    largest_gcd = 0
    for k in TARGET_K:
        for v in range(1, limit + 1):
            for u in range(v + 1, 2 * v):
                if math.gcd(u, v) != 1 or not u**k < 4 * v**k:
                    continue
                a1 = a_value(u, v, 1)
                a3 = a_value(u, v, 3)
                common = math.gcd(a1, a3)
                if 60 % common:
                    raise AssertionError((k, u, v, common))
                checked += 1
                largest_gcd = max(largest_gcd, common)
    return {"limit": limit, "pairs_checked": checked, "largest_gcd": largest_gcd}


def telescope_newton_checks() -> list[dict[str, Any]]:
    rows = []
    for k, u, v in ((9, 8, 7), (15, 13, 12)):
        coefficients = elementary_square_coefficients(k)
        z = 1
        e = coefficients[-1]
        f = coefficients[-2]
        a1 = a_value(u, v, 1)
        a3 = a_value(u, v, 3)
        if (e * a1) % z:
            raise AssertionError("constant scale divisibility failed")
        q = e * a1 // z
        if scale_residual(k, u, v, 1):
            raise AssertionError("telescope is not a full scale root")
        if (q - f * a3) % z:
            raise AssertionError("low Horner congruence failed")
        overlap = math.gcd(z, q)
        bound = discrepancy_bound(k)
        if bound % overlap:
            raise AssertionError("Newton discrepancy bound failed")
        rows.append(
            {
                "k": k,
                "u": u,
                "v": v,
                "z": z,
                "q": q,
                "gcd_z_q": overlap,
                "bound": bound,
            }
        )
    return rows


def counterfamily_non_coprime_fixture() -> dict[str, int]:
    """The k=5 low-filter counterfamily refutes the stronger gcd=1 claim."""
    point = counterfamily_point(1)
    z, u, v = point.z, point.u, point.v
    a1 = a_value(u, v, 1)
    a3 = a_value(u, v, 3)
    q = 4 * a1 // z
    if 4 * a1 != z * q or (q - 5 * a3) % z:
        raise AssertionError("counterfamily does not pass the first Newton step")
    overlap = math.gcd(z, q)
    if overlap != 12 or 1_200 % overlap:
        raise AssertionError("non-coprime Newton fixture changed")
    return {"z": z, "q": q, "gcd_z_q": overlap, "bound": 1_200}


def full_report() -> dict[str, Any]:
    bounds: dict[str, Any] = {}
    for k in TARGET_K:
        value = discrepancy_bound(k)
        if value != EXPECTED_DISCREPANCY_BOUNDS[k]:
            raise AssertionError(f"k={k}: discrepancy bound changed")
        factors = prime_factorization(value)
        product = math.prod(prime**exponent for prime, exponent in factors.items())
        if product != value:
            raise AssertionError("factorization reproduction failed")
        bounds[str(k)] = {"value": value, "prime_factorization": factors}
    return {
        "status": "bounded valuation discrepancy proved; no infinite-tail closure",
        "bounds": bounds,
        "exhaustive_sanity": exhaustive_linear_cubic_gcd_check(),
        "telescope_checks": telescope_newton_checks(),
        "stronger_coprime_claim_counterfixture": counterfamily_non_coprime_fixture(),
    }


def main() -> None:
    print(json.dumps(full_report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
