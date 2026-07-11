#!/usr/bin/env python3
"""Fresh hostile verifier for the repaired three-bucket zero exclusion.

The historical FAIL audit remains frozen and is treated only as evidence
about source SHA ``5b802d...``.  This verifier imports neither the producer
verifier nor the historical hostile verifier.  It reconstructs coefficients
as elementary-symmetric subset sums and audits the repaired public surface.
"""

from __future__ import annotations

import argparse
from functools import cache
import hashlib
from itertools import combinations, permutations
import json
from math import gcd, prod
from pathlib import Path
import re
from typing import Any, Iterable, Sequence


ROWS = (5, 7, 9, 11, 13, 15)
CROSS_BOUND = 10**30
THIRD_BOUND = 10**18
LOSS_BOUND = 18_914_575_680
CUTOFF = 10**120

HISTORICAL_FAILED_SOURCE_SHA = (
    "5b802dd3db2d63254b251465f96093358389c0eca4d72cdd7608d2238e549ff2"
)

REPAIRED_HASHES = {
    "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean": (
        "de9ddc72881c67f4ce7c7b0987eeccd71040f2ac4064deb8f0d6b70f075bd4bd"
    ),
    "compute/campaign686/three_bucket_zero_exclusion_verify.py": (
        "106f7686c30eed5150d922fa1e0acbd1b7439f1bc000a356df541af724fb4c78"
    ),
    "compute/campaign686/test_three_bucket_zero_exclusion_verify.py": (
        "6d7f2aa138e344fed21700b86a58e98a50ebbbbb3976c2d42fd95c9a66ae4810"
    ),
    "compute/campaign686/three_bucket_zero_exclusion_findings.md": (
        "459f43e1d11c02186635bfe617a8bfe372acdcc5c3cc407fc7bfb7f1d78a3f20"
    ),
    "docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion.md": (
        "0ba5ac8c350406eeccc5e4f134f392487dd3045c4de5dd685964d49c6d22c330"
    ),
}

HISTORICAL_AUDIT_HASHES = {
    "ErdosProblems/Erdos686ThreeBucketZeroExclusionAudit.lean": (
        "bf2c2b7148c387f406becb931eb0f845ca4d09b7017f49d400a21846b9a4f993"
    ),
    "compute/campaign686/three_bucket_zero_exclusion_hostile_verify.py": (
        "9a56d5fab54e4423f11837967887602bd42db33802f898675d9de67e631781d7"
    ),
    "compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py": (
        "8269c61e968907998629a6a7078e5d5d2c8f1e1a4633dfbacf7939719a17a946"
    ),
    "compute/campaign686/three_bucket_zero_exclusion_hostile_audit.md": (
        "44575160cd98bdb92ea9525b4df67b8d1cfcb027fd61ddb648fdd3c5b0dffc56"
    ),
    "docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion-hostile-audit.md": (
        "53aeb83b73a2e5e107002ed7329d8bdffe53229249069cacf91ded9cde9eb24a"
    ),
}

EXPECTED_PUBLIC_DECLARATIONS = [
    "threeBucketOwnerDelta",
    "threeBucketZeroCrossNumerator",
    "threeBucketZeroThirdCoefficient",
    "threeBucketZeroCrossNumeratorTable",
    "threeBucketZeroThirdCoefficientTable",
    "threeBucketZeroRowCertificateBool",
    "target_three_bucket_zero_table_certificate",
    "target_three_bucket_zero_coefficient_certificate",
    "three_bucket_zero_target_numeric_cutoff",
    "three_bucket_zero_gap_lt_cutoff_of_target_coefficients",
    "targetThreeBucketSecondObstruction",
    "targetThreeBucketThirdObstruction",
    "targetThreeBucketSecondObstruction_swap",
    "targetThreeBucketThirdObstruction_swap",
    "target_three_bucket_designated_zero_gap_lt",
    "target_three_bucket_all_second_obstructions_nonzero",
]

EXPECTED_PUBLIC_THEOREMS = [
    "target_three_bucket_zero_table_certificate",
    "target_three_bucket_zero_coefficient_certificate",
    "three_bucket_zero_target_numeric_cutoff",
    "three_bucket_zero_gap_lt_cutoff_of_target_coefficients",
    "targetThreeBucketSecondObstruction_swap",
    "targetThreeBucketThirdObstruction_swap",
    "target_three_bucket_designated_zero_gap_lt",
    "target_three_bucket_all_second_obstructions_nonzero",
]


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def _hashes(paths: dict[str, str]) -> dict[str, str]:
    root = repository_root()
    return {
        relative: hashlib.sha256((root / relative).read_bytes()).hexdigest()
        for relative in paths
    }


@cache
def freeze_report() -> dict[str, Any]:
    repaired_actual = _hashes(REPAIRED_HASHES)
    historical_actual = _hashes(HISTORICAL_AUDIT_HASHES)
    report_text = (
        repository_root()
        / "compute/campaign686/three_bucket_zero_exclusion_hostile_audit.md"
    ).read_text()
    current_source = repaired_actual[
        "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean"
    ]
    return {
        "repaired_expected": REPAIRED_HASHES,
        "repaired_actual": repaired_actual,
        "repaired_all_match": repaired_actual == REPAIRED_HASHES,
        "historical_audit_expected": HISTORICAL_AUDIT_HASHES,
        "historical_audit_actual": historical_actual,
        "historical_audit_all_match": historical_actual == HISTORICAL_AUDIT_HASHES,
        "historical_failed_source_sha": HISTORICAL_FAILED_SOURCE_SHA,
        "current_source_sha": current_source,
        "historical_fail_report_preserved": (
            HISTORICAL_FAILED_SOURCE_SHA in report_text
            and "Verdict: **FAIL for kernel intake" in report_text
        ),
    }


@cache
def public_surface_report() -> dict[str, Any]:
    source = (
        repository_root()
        / "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean"
    ).read_text()
    matches = re.findall(
        r"^(?:(?:noncomputable)\s+)?(def|theorem|lemma)\s+([A-Za-z0-9_]+)",
        source,
        flags=re.MULTILINE,
    )
    declarations = [name for _, name in matches]
    theorems = [name for kind, name in matches if kind in ("theorem", "lemma")]
    if declarations != EXPECTED_PUBLIC_DECLARATIONS:
        raise AssertionError(("public surface drift", declarations))
    if theorems != EXPECTED_PUBLIC_THEOREMS:
        raise AssertionError(("theorem surface drift", theorems))
    return {
        "declaration_names": declarations,
        "theorem_names": theorems,
        "public_declarations": len(declarations),
        "public_theorems_and_lemmas": len(theorems),
    }


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
    if k < 1 or not 1 <= owner <= k:
        raise ValueError((k, owner))
    offsets = tuple(column - owner for column in range(1, k + 1) if column != owner)
    count = len(offsets)

    def coefficient(degree: int) -> int:
        constant_choices = count - degree
        if not 0 <= constant_choices <= count:
            return 0
        return sum(
            (prod(choice) for choice in combinations(offsets, constant_choices)),
            0,
        )

    return coefficient(0), coefficient(1), coefficient(2)


def owner_delta(owner: int, left: int, right: int) -> int:
    return (owner - left) * (owner - right)


def cross_numerator(k: int, owner: int, zero: int, other: int) -> int:
    owner_constant, owner_linear, _ = local_coefficients(k, owner)
    zero_constant, zero_linear, _ = local_coefficients(k, zero)
    return 36 * (
        owner_constant * zero_linear * owner_delta(zero, owner, other)
        - owner_linear * owner_delta(owner, zero, other) * zero_constant
    )


def zero_third_coefficient(k: int, zero: int, owner: int, other: int) -> int:
    _, _, quadratic = local_coefficients(k, zero)
    return 180 * quadratic * owner_delta(zero, owner, other)


def second_obstruction(
    k: int,
    owner: int,
    left: int,
    right: int,
    t: int,
    g: int,
) -> int:
    constant, linear, _ = local_coefficients(k, owner)
    return 3 * (
        constant * t - 12 * linear * g**2 * owner_delta(owner, left, right)
    )


def third_obstruction(
    k: int,
    owner: int,
    left: int,
    right: int,
    t: int,
    g: int,
    d: int,
) -> int:
    _, _, quadratic = local_coefficients(k, owner)
    return (
        -3 * second_obstruction(k, owner, left, right, t, g)
        + 180 * quadratic * g**2 * owner_delta(owner, left, right) * d
    )


def _designated_view(
    k: int,
    first: int,
    second: int,
    zero: int,
    t: int,
    g: int,
    d: int,
) -> tuple[int, int, int, int]:
    return (
        second_obstruction(k, first, zero, second, t, g),
        second_obstruction(k, second, zero, first, t, g),
        second_obstruction(k, zero, first, second, t, g),
        third_obstruction(k, zero, first, second, t, g, d),
    )


def _cyclic_views(
    k: int,
    i: int,
    j: int,
    l: int,
    t: int,
    g: int,
    d: int,
) -> Iterable[tuple[tuple[int, int, int, int], tuple[int, int, int, int]]]:
    oi = second_obstruction(k, i, j, l, t, g)
    oj = second_obstruction(k, j, i, l, t, g)
    ol = second_obstruction(k, l, i, j, t, g)
    fi = third_obstruction(k, i, j, l, t, g, d)
    fj = third_obstruction(k, j, i, l, t, g, d)
    fl = third_obstruction(k, l, i, j, t, g, d)
    yield _designated_view(k, j, l, i, t, g, d), (oj, ol, oi, fi)
    yield _designated_view(k, i, l, j, t, g, d), (oi, ol, oj, fj)
    yield _designated_view(k, i, j, l, t, g, d), (oi, oj, ol, fl)


@cache
def finite_row_report() -> dict[str, Any]:
    rows = []
    cross_checks = 0
    third_checks = 0
    second_swap_checks = 0
    third_swap_checks = 0
    cyclic_checks = 0
    total_zero_cross = 0
    total_zero_third = 0
    for k in ROWS:
        maximum_cross = -1
        maximum_cross_case: tuple[int, int, int] | None = None
        maximum_third = -1
        maximum_third_case: tuple[int, int, int] | None = None
        row_zero_cross = 0
        row_zero_third = 0
        count = 0
        for owner, zero, other in permutations(range(1, k + 1), 3):
            count += 1
            cross = cross_numerator(k, owner, zero, other)
            third_coefficient = zero_third_coefficient(k, zero, owner, other)
            row_zero_cross += cross == 0
            row_zero_third += third_coefficient == 0
            if not 0 < abs(cross) < CROSS_BOUND:
                raise AssertionError(("cross bound", k, owner, zero, other, cross))
            if not 0 < abs(third_coefficient) < THIRD_BOUND:
                raise AssertionError(
                    ("third bound", k, owner, zero, other, third_coefficient)
                )
            if abs(cross) > maximum_cross:
                maximum_cross = abs(cross)
                maximum_cross_case = (owner, zero, other)
            if abs(third_coefficient) > maximum_third:
                maximum_third = abs(third_coefficient)
                maximum_third_case = (owner, zero, other)

            t = (k + 2 * owner + zero) * (other + 3)
            g = 1 + (owner + 3 * zero + other) % 23
            d = 1 + k * owner * zero * other
            owner_second = second_obstruction(k, owner, zero, other, t, g)
            zero_second = second_obstruction(k, zero, owner, other, t, g)
            owner_constant, _, _ = local_coefficients(k, owner)
            zero_constant, _, _ = local_coefficients(k, zero)
            if (
                zero_constant * owner_second - owner_constant * zero_second
                != cross * g**2
            ):
                raise AssertionError(("cross identity", k, owner, zero, other))
            cross_checks += 1
            zero_third = third_obstruction(k, zero, owner, other, t, g, d)
            if zero_third + 3 * zero_second != third_coefficient * g**2 * d:
                raise AssertionError(("third identity", k, owner, zero, other))
            third_checks += 1
            if second_obstruction(k, owner, zero, other, t, g) != second_obstruction(
                k, owner, other, zero, t, g
            ):
                raise AssertionError(("second swap", k, owner, zero, other))
            second_swap_checks += 1
            if third_obstruction(k, owner, zero, other, t, g, d) != third_obstruction(
                k, owner, other, zero, t, g, d
            ):
                raise AssertionError(("third swap", k, owner, zero, other))
            third_swap_checks += 1
            for actual, expected in _cyclic_views(k, owner, zero, other, t, g, d):
                if actual != expected:
                    raise AssertionError(("cyclic view", k, owner, zero, other))
                cyclic_checks += 1

        total_zero_cross += row_zero_cross
        total_zero_third += row_zero_third
        rows.append(
            {
                "k": k,
                "ordered_distinct_owner_triples": count,
                "maximum_cross_numerator": maximum_cross,
                "maximum_cross_case": list(maximum_cross_case or ()),
                "maximum_third_coefficient": maximum_third,
                "maximum_third_case": list(maximum_third_case or ()),
                "zero_cross_cases": row_zero_cross,
                "zero_third_cases": row_zero_third,
            }
        )
    return {
        "rows": rows,
        "ordered_distinct_owner_triples": sum(
            row["ordered_distinct_owner_triples"] for row in rows
        ),
        "zero_cross_cases": total_zero_cross,
        "zero_third_cases": total_zero_third,
        "cross_identity_checks": cross_checks,
        "third_identity_checks": third_checks,
        "second_swap_checks": second_swap_checks,
        "third_swap_checks": third_swap_checks,
        "cyclic_designated_zero_checks": cyclic_checks,
    }


def numeric_cutoff_report() -> dict[str, Any]:
    majorant = CROSS_BOUND**2 * THIRD_BOUND * LOSS_BOUND**4
    return {
        "cross_bound": CROSS_BOUND,
        "third_bound": THIRD_BOUND,
        "loss_bound": LOSS_BOUND,
        "majorant": majorant,
        "cutoff": CUTOFF,
        "strict": majorant < CUTOFF,
        "cutoff_margin_floor": CUTOFF // majorant,
    }


def _row_maxima(k: int) -> tuple[int, int]:
    cross_maximum = 0
    third_maximum = 0
    for owner, zero, other in permutations(range(1, k + 1), 3):
        cross_maximum = max(
            cross_maximum, abs(cross_numerator(k, owner, zero, other))
        )
        third_maximum = max(
            third_maximum, abs(zero_third_coefficient(k, zero, owner, other))
        )
    return cross_maximum, third_maximum


def _block_product(k: int, n: int) -> int:
    return prod(n + offset for offset in range(1, k + 1))


@cache
def hostile_boundary_report() -> dict[str, Any]:
    collision_cross = cross_numerator(5, 1, 1, 2)
    collision_third = zero_third_coefficient(5, 1, 1, 2)

    outside_cross, outside_third = _row_maxima(17)

    P = Q = 4
    R = 1
    g = 2
    A = B = K = 1
    d = g * P * Q * R
    divisibilities = (
        (A * g**2) % P == 0
        and (B * g**2) % Q == 0
        and (K * g**2 * d) % R**2 == 0
    )
    packing_conclusion = (A * B * K * g**4) % d == 0

    sharp_P, sharp_Q, sharp_R = 2, 5, 27
    sharp_g, sharp_A, sharp_B, sharp_K = 3, 2, 5, 1
    sharp_d = sharp_g * sharp_P * sharp_Q * sharp_R
    sharp_product = sharp_A * sharp_B * sharp_K

    shared_g_fixture = {
        "components": [2, 3, 5],
        "g": 30,
        "gcds": [gcd(30, component) for component in (2, 3, 5)],
    }
    unit_components = [[1, 2, 3], [1, 1, 1]]
    d_eq_one = []
    for k, n in ((9, 2), (15, 4)):
        d_one = 1
        d_eq_one.append(
            {
                "k": k,
                "n": n,
                "d": d_one,
                "equation": _block_product(k, n + d_one)
                == 4 * _block_product(k, n),
                "large_gap_hypothesis": CUTOFF <= d_one,
            }
        )
    return {
        "owner_collision": {
            "k": 5,
            "owner": 1,
            "zero": 1,
            "other": 2,
            "cross": collision_cross,
            "third": collision_third,
        },
        "outside_target_row": {
            "k": 17,
            "maximum_cross": outside_cross,
            "maximum_third": outside_third,
            "cross_exceeds_bound": outside_cross >= CROSS_BOUND,
            "third_exceeds_bound": outside_third >= THIRD_BOUND,
        },
        "drop_pairwise_coprime": {
            "P": P,
            "Q": Q,
            "R": R,
            "g": g,
            "d": d,
            "all_divisibility_premises": divisibilities,
            "pairwise_coprime": gcd(P, Q) == gcd(P, R) == gcd(Q, R) == 1,
            "packing_conclusion": packing_conclusion,
        },
        "replace_g4_by_g3": {
            "P": sharp_P,
            "Q": sharp_Q,
            "R": sharp_R,
            "g": sharp_g,
            "d": sharp_d,
            "g4_conclusion": (sharp_product * sharp_g**4) % sharp_d == 0,
            "g3_conclusion": (sharp_product * sharp_g**3) % sharp_d == 0,
        },
        "shared_g_is_allowed": shared_g_fixture,
        "unit_components_are_allowed": unit_components,
        "d_eq_one": d_eq_one,
    }


def forbidden_source_report() -> dict[str, Any]:
    root = repository_root()
    paths = (
        "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean",
        "compute/campaign686/three_bucket_zero_exclusion_verify.py",
        "compute/campaign686/test_three_bucket_zero_exclusion_verify.py",
    )
    forbidden = re.compile(
        r"\b(?:sorry|admit|native_decide|of_decide|unsafe|implemented_by|extern)\b"
        r"|^\s*(?:private\s+)?axiom\b",
        flags=re.MULTILINE,
    )
    hits = {
        relative: [match.group(0) for match in forbidden.finditer((root / relative).read_text())]
        for relative in paths
    }
    hits = {relative: matches for relative, matches in hits.items() if matches}
    return {"paths": list(paths), "hits": hits, "clean": not hits}


@cache
def report() -> dict[str, Any]:
    frozen = freeze_report()
    finite = finite_row_report()
    numeric = numeric_cutoff_report()
    forbidden = forbidden_source_report()
    safe = (
        frozen["repaired_all_match"]
        and frozen["historical_audit_all_match"]
        and frozen["historical_fail_report_preserved"]
        and finite["zero_cross_cases"] == 0
        and finite["zero_third_cases"] == 0
        and numeric["strict"]
        and forbidden["clean"]
    )
    return {
        "freeze": frozen,
        "public_surface": public_surface_report(),
        "finite_rows": finite,
        "numeric_cutoff": numeric,
        "hostile_boundaries": hostile_boundary_report(),
        "forbidden": forbidden,
        "verdict": "PASS repaired candidate" if safe else "FAIL repaired candidate",
        "safe_to_integrate": safe,
        "closes_zero_branch_only": True,
        "closes_nonzero_branch": False,
        "closes_exactly_three_owner_slice": False,
        "closes_erdos_686": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
