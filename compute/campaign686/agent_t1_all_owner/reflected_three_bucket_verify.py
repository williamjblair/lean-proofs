#!/usr/bin/env python3
"""Exact verifier for the 54 center/reflected Erdős 686 views.

This is independent of Lean's coefficient reduction.  It rebuilds the local
cofactor coefficients from products, specializes the reduced fifth
coefficient, verifies the endpoint-third determinant, checks all 27 rational
lower-bound sign certificates, and reproduces the packing cutoff exactly.
"""

from __future__ import annotations

import argparse
import json
from itertools import product
from math import factorial
from typing import Any

from compute.campaign686.agent_t1_all_owner.fifth_local_lift_verify import (
    ROWS,
    local_coefficients,
    reduced_fifth_coefficient,
)


LEGACY_TARGET = 10**120
TAIL1000_INTERMEDIATE_CUTOFF = 10**200
TAIL1000_TARGET = 10**1000
# Keep the historical name for the sign-certificate and legacy packing
# checks.  Those checks were originally proved at the 10^120 handoff.
TARGET = LEGACY_TARGET
RATIO = {
    5: (268048, 31951),
    7: (278097, 21902),
    9: (283346, 16653),
    11: (286567, 13432),
    13: (288745, 11254),
    15: (290316, 9683),
}
LOSS = {
    5: 108,
    7: 1620,
    9: 136080,
    11: 1224720,
    13: 242494560,
    15: 18914575680,
}


def reflected_left_third(
    C: int, D: int, E: int, t: int, g: int, r: int, d: int
) -> int:
    return -9 * C * t + 216 * D * g**2 * r**2 + 360 * E * g**2 * r**2 * d


def reflected_right_third(
    C: int, D: int, E: int, t: int, g: int, r: int, d: int
) -> int:
    return -9 * C * t - 216 * D * g**2 * r**2 + 360 * E * g**2 * r**2 * d


def determinant_grid() -> dict[str, int]:
    checks = signed = 0
    for k, r, t, g, d, X in product(
        ROWS, range(1, 8), range(-5, 6), range(-3, 4), range(-3, 4), range(-5, 6)
    ):
        center = (k + 1) // 2
        if r >= center:
            continue
        C, D, E, _, _ = local_coefficients(k, center - r)
        left = reflected_left_third(C, D, E, t, g, r, d)
        right = reflected_right_third(C, D, E, t, g, r, d)
        determinant = (X - 3 * r) * right - (X + 3 * r) * left
        expected = 54 * r * (C * t - 8 * D * X * g**2 * r - 40 * E * g**2 * r**2 * d)
        if determinant != expected:
            raise AssertionError((k, r, t, g, d, X))
        checks += 1
        signed += min(t, g, d, X) < 0
    return {"exact_identities": checks, "signed_fixtures": signed}


def center_fifth_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for k in ROWS:
        center = (k + 1) // 2
        C, D, E, F, G = local_coefficients(k, center)
        if D != 0 or F != 0:
            raise AssertionError("center cofactor was not even")
        base = 8748 * C * (255 * C * G + 180 * E**2)
        if base == 0:
            raise AssertionError("linear fifth slope unexpectedly vanished")
        for r in range(1, center):
            slope = base * r**4
            values = [
                reduced_fifth_coefficient(C, D, E, F, G, gap, r, -r)
                for gap in (0, 1, 2)
            ]
            if values != [0, slope, 2 * slope]:
                raise AssertionError((k, r, values, slope))
            rows.append(
                {
                    "k": k,
                    "r": r,
                    "C": C,
                    "E": E,
                    "G": G,
                    "constant": 0,
                    "linear": slope,
                    "quadratic": 0,
                }
            )
    return rows


def certificate_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for k, U in ROWS.items():
        center = (k + 1) // 2
        R, H = RATIO[k]
        center_bound = factorial(center - 1) ** 2 * U
        for r in range(1, center):
            C, D, E, _, _ = local_coefficients(k, center - r)
            beta = 8 * abs(D) * r
            epsilon = 40 * abs(E) * r**2
            monotone_margin = abs(C) * R**2 - beta * H**2
            cubic_margin = R * monotone_margin - epsilon * H**3
            offset = 9 * abs(C) * r**2 * U * H**3
            if monotone_margin <= 0 or cubic_margin <= 0:
                raise AssertionError((k, r, monotone_margin, cubic_margin))
            if not offset < TARGET**2 * cubic_margin:
                raise AssertionError((k, r, "offset"))
            determinant_bound = 54 * r * (
                abs(C) * U**3 + 8 * abs(D) * U * r + 40 * abs(E) * r**2
            )
            cutoff = center_bound**2 * determinant_bound**3 * LOSS[k] ** 12
            if not cutoff < TAIL1000_INTERMEDIATE_CUTOFF < TAIL1000_TARGET:
                raise AssertionError((k, r, "tail1000 packing cutoff", cutoff))
            rows.append(
                {
                    "k": k,
                    "r": r,
                    "ratio_numerator": R,
                    "ratio_denominator": H,
                    "monotone_margin": monotone_margin,
                    "cubic_margin": cubic_margin,
                    "offset": offset,
                    "center_cube_bound": center_bound,
                    "determinant_bound": determinant_bound,
                    "loss_bound": LOSS[k],
                    "packing_cutoff": cutoff,
                    "packing_cutoff_digits": len(str(cutoff)),
                    "closed_below_legacy_target": cutoff < LEGACY_TARGET,
                    "closed_below_10_200": cutoff < TAIL1000_INTERMEDIATE_CUTOFF,
                    "closed_below_tail1000": cutoff < TAIL1000_TARGET,
                }
            )
    return rows


def tail1000_upgrade_report(
    certificates: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Reproduce the exact 12-to-27 reflected-pair cutoff upgrade.

    Every quantity is a Python integer reconstructed by ``certificate_rows``.
    The intermediate ``10^200`` inequality is deliberately stronger than the
    tail handoff at ``10^1000`` and makes the new margin auditable without
    decimal approximations or logarithms.
    """

    rows = certificate_rows() if certificates is None else certificates
    legacy_closed = [row for row in rows if row["packing_cutoff"] < LEGACY_TARGET]
    newly_closed = [
        row
        for row in rows
        if LEGACY_TARGET <= row["packing_cutoff"] < TAIL1000_INTERMEDIATE_CUTOFF
    ]
    if len(rows) != 27 or len(legacy_closed) != 12 or len(newly_closed) != 15:
        raise AssertionError((len(rows), len(legacy_closed), len(newly_closed)))
    if not all(
        isinstance(row["packing_cutoff"], int)
        and row["packing_cutoff"] < TAIL1000_INTERMEDIATE_CUTOFF
        < TAIL1000_TARGET
        for row in rows
    ):
        raise AssertionError("tail1000 cutoff verification was not exact")

    per_row_maxima: list[dict[str, int | bool]] = []
    for k in ROWS:
        row_certificates = [row for row in rows if row["k"] == k]
        maximum = max(row_certificates, key=lambda row: row["packing_cutoff"])
        per_row_maxima.append(
            {
                "k": k,
                "pair_count": len(row_certificates),
                "maximum_r": maximum["r"],
                "maximum_cutoff": maximum["packing_cutoff"],
                "maximum_cutoff_digits": maximum["packing_cutoff_digits"],
                "maximum_below_10_200": (
                    maximum["packing_cutoff"] < TAIL1000_INTERMEDIATE_CUTOFF
                ),
                "maximum_below_tail1000": (
                    maximum["packing_cutoff"] < TAIL1000_TARGET
                ),
            }
        )

    return {
        "legacy_target": LEGACY_TARGET,
        "intermediate_cutoff": TAIL1000_INTERMEDIATE_CUTOFF,
        "tail1000_target": TAIL1000_TARGET,
        "total_pairs": len(rows),
        "legacy_closed_pairs": len(legacy_closed),
        "newly_closed_pairs": len(newly_closed),
        "all_pairs_below_10_200": True,
        "all_pairs_below_tail1000": True,
        "per_row_maxima": per_row_maxima,
        "newly_closed": [
            {"k": row["k"], "r": row["r"], "cutoff": row["packing_cutoff"]}
            for row in newly_closed
        ],
    }


def report() -> dict[str, Any]:
    fifth = center_fifth_rows()
    certificates = certificate_rows()
    legacy_closed = [
        row for row in certificates if row["closed_below_legacy_target"]
    ]
    legacy_surviving = [
        row for row in certificates if not row["closed_below_legacy_target"]
    ]
    return {
        "view_count": {
            "unoriented_pairs": len(certificates),
            "oriented_views": 2 * len(certificates),
            "legacy_10_120_closed_pairs": len(legacy_closed),
            "legacy_10_120_closed_oriented_views": 2 * len(legacy_closed),
            "legacy_10_120_surviving_pairs": len(legacy_surviving),
            "legacy_10_120_surviving_oriented_views": 2 * len(legacy_surviving),
        },
        "fifth_specialization": {
            "formula": "8748*r^4*C*(255*C*G+180*E^2)*d",
            "all_constants_zero": all(row["constant"] == 0 for row in fifth),
            "all_quadratics_zero": all(row["quadratic"] == 0 for row in fifth),
            "all_linear_slopes_nonzero": all(row["linear"] != 0 for row in fifth),
            "rows": fifth,
        },
        "determinant_grid": determinant_grid(),
        "all_27_cubic_sign_certificates": len(certificates) == 27,
        "tail1000_upgrade": tail1000_upgrade_report(certificates),
        "legacy_10_120_closed": [
            {"k": row["k"], "r": row["r"], "cutoff": row["packing_cutoff"]}
            for row in legacy_closed
        ],
        "legacy_10_120_surviving": [
            {
                "k": row["k"],
                "r": row["r"],
                "cutoff": row["packing_cutoff"],
                "legacy_target_multiple_floor": (
                    row["packing_cutoff"] // LEGACY_TARGET
                ),
            }
            for row in legacy_surviving
        ],
        "certificates": certificates,
        "quantified_remaining_gap": (
            "all 27 center/reflected pairs close below 10^1000; arbitrary "
            "owner configurations and exactly-three configurations not "
            "consisting of the center plus a reflected pair remain outside "
            "this packing slice"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=None if args.compact else 2, sort_keys=True))


if __name__ == "__main__":
    main()
