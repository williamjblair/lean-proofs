#!/usr/bin/env python3
"""Exact arithmetic verifier for the corrected osculation-kernel bounds.

The associated mathematical lemma concerns a q-by-N integer matrix whose
rows have l1 norm at most L.  Counting a cube of radius D by image fibers and
using the affine cube-intersection bound gives N-2q+1 independent kernel
vectors when (D+1)^2 > D*L+1.  This verifier checks the corrected dimensions,
the advertised radius, and every finite cardinality inequality with integers.
It is not a replacement for the Lean proof of the affine-intersection lemma.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CERTIFICATE = ROOT / "osculation_kernel_certificate.json"
SCAN_K_START = 16
SCAN_K_END = 224

sys.set_int_max_str_digits(0)


def osculation_degree(m: int) -> int:
    r = 0
    while math.comb(r + 2, 2) < 4 * m + 1:
        r += 1
    return r


def finite_scan() -> dict[str, object]:
    digest = hashlib.sha256()
    cases = 0
    minimum_slack: int | None = None
    for k in range(SCAN_K_START, SCAN_K_END + 1):
        for m in range(2, k + 1):
            r = osculation_degree(m)
            n_columns = math.comb(r + 2, 2)
            q_rows = 2 * m
            family_size = n_columns - 2 * q_rows + 1
            entry_bound = 3 * r * pow(2, k) * pow(k, r - 1)
            row_l1_bound = n_columns * entry_bound
            radius = 4 * row_l1_bound
            advertised_radius = (
                12 * n_columns * r * pow(2, k) * pow(k, r - 1)
            )
            fiber_gap = pow(radius + 1, 2) - (
                radius * row_l1_bound + 1
            )
            expected_gap = (
                12 * row_l1_bound * row_l1_bound + 8 * row_l1_bound
            )
            if n_columns < 4 * m + 1:
                raise AssertionError((k, m, "minimal degree"))
            if r and math.comb(r + 1, 2) >= 4 * m + 1:
                raise AssertionError((k, m, "degree is not minimal"))
            if family_size < 2:
                raise AssertionError((k, m, family_size))
            if radius != advertised_radius:
                raise AssertionError((k, m, "radius mismatch"))
            if fiber_gap != expected_gap or fiber_gap <= 0:
                raise AssertionError((k, m, "fiber inequality"))
            minimum_slack = (
                family_size
                if minimum_slack is None
                else min(minimum_slack, family_size)
            )
            line = ",".join(
                map(
                    str,
                    (
                        k,
                        m,
                        r,
                        n_columns,
                        q_rows,
                        family_size,
                        entry_bound.bit_length(),
                        row_l1_bound.bit_length(),
                        radius.bit_length(),
                        fiber_gap.bit_length(),
                    ),
                )
            )
            digest.update((line + "\n").encode("ascii"))
            cases += 1
    return {
        "range": {"k": [SCAN_K_START, SCAN_K_END], "m": "2..k"},
        "case_count": cases,
        "minimum_family_size": minimum_slack,
        "records_sha256": digest.hexdigest(),
    }


def symbolic_checks() -> dict[str, object]:
    # Put D=4L.  The fiber inequality has the following exact positive gap.
    for l_bound in (1, 2, 17, 10**6):
        radius = 4 * l_bound
        gap = pow(radius + 1, 2) - (radius * l_bound + 1)
        if gap != 12 * l_bound * l_bound + 8 * l_bound or gap <= 0:
            raise AssertionError(l_bound)

    # With q=2m and N>=4m+1, s=N-2q+1=N-4m+1>=2.
    for m in range(1, 100):
        n_columns = 4 * m + 1
        q_rows = 2 * m
        if n_columns - 2 * q_rows + 1 != 2:
            raise AssertionError(m)

    # The source's 4m-row formulation is impossible at the advertised
    # family size: [I_(4m) 0] has nullity N-4m, one less than requested.
    counterexample_m = 2
    counterexample_n = 4 * counterexample_m + 2
    actual_nullity = counterexample_n - 4 * counterexample_m
    rejected_family_size = counterexample_n - 4 * counterexample_m + 1
    if actual_nullity >= rejected_family_size:
        raise AssertionError("the rejected 4m-row claim unexpectedly survived")

    return {
        "corrected_rows": "q=2m",
        "family_size": "s=N-2q+1=N-4m+1",
        "cube": "{0,...,D}^N",
        "image_bound": "(D*L+1)^q",
        "fiber_condition": "(D+1)^2>D*L+1",
        "affine_intersection_bound": "at most (D+1)^(s-1) cube points in affine dimension s-1",
        "row_l1_bound": "L=N*H",
        "entry_bound": "H=3*r*2^k*k^(r-1)",
        "radius": "D=4*L=12*N*r*2^k*k^(r-1)",
        "positive_gap": "(D+1)^2-(D*L+1)=12*L^2+8*L",
        "rejected_source_claim": {
            "rows": "4m",
            "example_m": counterexample_m,
            "example_columns": counterexample_n,
            "actual_nullity": actual_nullity,
            "claimed_family_size": rejected_family_size,
        },
    }


def expected_certificate() -> dict[str, object]:
    return {
        "schema": "erdos686.osculation-kernel-bound.v1",
        "arithmetic": "exact integers only; no floating-point acceptance",
        "status": "corrected cube/fiber dimensions and radius certified and kernel-checked",
        "symbolic": symbolic_checks(),
        "finite_scan": finite_scan(),
        "lean_theorems": [
            "Erdos686.Erdos686Variant.affine_cube_subset_card_le_finrank",
            "Erdos686.Erdos686Variant.exists_bounded_independent_integer_kernel_family",
            "Erdos686.Erdos686Variant.exists_bounded_independent_osculation_kernel_family_advertised",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    expected = expected_certificate()
    if args.write_certificate:
        CERTIFICATE.write_text(json.dumps(expected, indent=2) + "\n")
    actual = json.loads(CERTIFICATE.read_text())
    if actual != expected:
        raise AssertionError("osculation kernel certificate mismatch")
    print("PASS: exact corrected osculation-kernel certificate verified")
    print("matrix rows: 2m; family size: N-4m+1; radius: 4*N*H")
    print("no floating-point acceptance conditions")


if __name__ == "__main__":
    main()
