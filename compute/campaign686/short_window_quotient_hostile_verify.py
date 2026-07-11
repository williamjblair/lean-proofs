#!/usr/bin/env python3
"""Independent hostile verifier for the frozen ShortWindowQuotient package.

No producer Python module is imported.  Local coefficients are reconstructed
as elementary-symmetric subset sums, after which the reduced fourth identity,
lattice geometry, 2,603 two-zero placements, and named short fixture are
checked using exact integers.
"""

from __future__ import annotations

import argparse
from functools import cache, reduce
import hashlib
from itertools import combinations, permutations, product
import json
from math import gcd, prod
from pathlib import Path
import re
from typing import Any


ROWS: dict[int, tuple[int, int]] = {
    5: (14, 108),
    7: (17, 1_620),
    9: (23, 136_080),
    11: (26, 1_224_720),
    13: (29, 242_494_560),
    15: (35, 18_914_575_680),
}
TARGET = 10**120

FROZEN_HASHES = {
    "ErdosProblems/Erdos686ShortWindowQuotient.lean": (
        "bf18db4af88be78e7f4400a6cdc67b5bfb66ddef8dc12fe1072e7ad1b3903ccc"
    ),
    "ErdosProblems/Erdos686ShortWindowQuotientAudit.lean": (
        "6ff2c48c62b4c77e560378888553485ede2502126ba468abbe1e45cbd373d54a"
    ),
    "compute/campaign686/short_window_quotient_attack.py": (
        "af60785ae52a199a13a72759d133b6c1d6919a22dcb0d4b4172a892a2faafe0d"
    ),
    "compute/campaign686/test_short_window_quotient_attack.py": (
        "37e2f43d6169ae6fe0cf7cecbb4c23213087504d87e4d873f1a27f33ec1d78f3"
    ),
    "compute/campaign686/short_window_quotient_findings.md": (
        "b1365cdaba351c96f453c08737bf48babbe94a906a094512babd145f047f010a"
    ),
    "docs/plans/2026-07-10-erdos686-short-window-quotient-attack.md": (
        "4c228bff302f2e5fcd45ff4b9347eec1101299412807953b202415cfd0eced29"
    ),
}

THEOREM_NAMES = [
    "three_bucket_reduced_fourth_identity",
    "square_factor_cancel_from_cube_dvd",
    "three_bucket_fourth_to_third_quotient",
    "three_bucket_fourth_obstruction_to_quotient",
    "three_bucket_reduced_fourth_quotient_dvd",
    "three_bucket_fourth_obstruction_reduced_dvd",
    "three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients",
    "common_component_third_quotient_dvd_fixed",
    "common_component_opposite_cofactor_dvd_offset",
    "three_third_quotient_lattice_identity",
    "two_zero_third_quotient_gap_square_bound",
    "two_zero_third_quotient_gap_lt_cutoff",
    "third_quotient_bound_of_short_window",
]


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


@cache
def freeze_report() -> dict[str, Any]:
    root = repository_root()
    actual = {
        relative: hashlib.sha256((root / relative).read_bytes()).hexdigest()
        for relative in FROZEN_HASHES
    }
    findings_lines = (
        root / "compute/campaign686/short_window_quotient_findings.md"
    ).read_text().splitlines()
    duplicated = "P_s^3 | 3a_u a_v T_s + P_s^2 J_s,"
    if findings_lines[82] != duplicated or findings_lines[352] != duplicated:
        raise AssertionError("section-8 prose restatement moved")
    return {
        "expected": FROZEN_HASHES,
        "actual": actual,
        "files": len(actual),
        "all_match": actual == FROZEN_HASHES,
        "findings_prose_duplicate": {
            "earlier_line": 83,
            "section_8_line": 353,
            "text": duplicated,
            "semantic_effect": False,
        },
    }


@cache
def public_surface_report() -> dict[str, Any]:
    root = repository_root()
    source = (root / "ErdosProblems/Erdos686ShortWindowQuotient.lean").read_text()
    definitions = re.findall(r"^def\s+([A-Za-z0-9_]+)", source, re.MULTILINE)
    theorems = re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE)
    if theorems != THEOREM_NAMES:
        raise AssertionError(("theorem surface drift", theorems))
    importer = (
        root / "ErdosProblems/Erdos686ShortWindowQuotientAudit.lean"
    ).read_text()
    importer_theorems = re.findall(
        r"^(?:theorem|lemma)\s+([A-Za-z0-9_]+)", importer, re.MULTILINE
    )
    return {
        "definition_names": definitions,
        "theorem_names": theorems,
        "public_definitions": len(definitions),
        "public_theorems": len(theorems),
        "producer_audit_declares_new_theorems": importer_theorems,
        "producer_audit_is_importer_only": not importer_theorems,
    }


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    if not 1 <= owner <= k:
        raise ValueError((k, owner))
    offsets = tuple(column - owner for column in range(1, k + 1) if column != owner)
    count = len(offsets)
    return tuple(
        sum(
            (prod(choice) for choice in combinations(offsets, count - degree)),
            0,
        )
        for degree in range(count + 1)
    )


def geometry(owner: int, left: int, right: int) -> tuple[int, int]:
    return (owner - left) * (owner - right), 2 * owner - left - right


def second_obstruction(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> int:
    constant, linear = local_coefficients(k, owner)[:2]
    delta, _ = geometry(owner, left, right)
    return 3 * (constant * t - 12 * linear * g**2 * delta)


def third_obstruction(
    k: int, owner: int, left: int, right: int, t: int, g: int, d: int
) -> int:
    quadratic = local_coefficients(k, owner)[2]
    delta, _ = geometry(owner, left, right)
    return (
        -3 * second_obstruction(k, owner, left, right, t, g)
        + 180 * quadratic * g**2 * delta * d
    )


def fourth_correction(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> int:
    _, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta, sigma = geometry(owner, left, right)
    return (
        -9 * linear * t**2
        - 108 * linear * t * g**2 * sigma
        + 324 * quadratic * t * g**2 * delta
        + 6804 * cubic * g**4 * delta**2
    )


def reduced_coefficient(k: int, owner: int, left: int, right: int) -> int:
    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta, sigma = geometry(owner, left, right)
    middle = -108 * linear * sigma + 324 * quadratic * delta
    return 108 * delta * (
        -108 * linear**3 * delta
        + constant * linear * middle
        + 567 * constant**2 * cubic * delta
    )


def reduced_multiplier(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> int:
    constant, linear, quadratic = local_coefficients(k, owner)[:3]
    delta, sigma = geometry(owner, left, right)
    middle = -108 * linear * sigma + 324 * quadratic * delta
    return (
        -9 * linear * (3 * constant * t + 36 * linear * g**2 * delta)
        + 3 * constant * g**2 * middle
    )


def reduced_identity_holds(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> bool:
    constant = local_coefficients(k, owner)[0]
    lhs = 9 * constant**2 * fourth_correction(k, owner, left, right, t, g)
    rhs = (
        reduced_multiplier(k, owner, left, right, t, g)
        * second_obstruction(k, owner, left, right, t, g)
        + reduced_coefficient(k, owner, left, right) * g**4
    )
    return lhs == rhs


def lattice_weights(
    k: int, indices: tuple[int, int, int]
) -> tuple[tuple[int, int, int], int]:
    rows = []
    for owner in indices:
        left, right = (index for index in indices if index != owner)
        constant, linear, quadratic = local_coefficients(k, owner)[:3]
        delta, _ = geometry(owner, left, right)
        rows.append((-9 * constant, 180 * quadratic * delta, 108 * linear * delta))
    (a1, b1, _), (a2, b2, _), (a3, b3, _) = rows
    raw = (
        a2 * b3 - a3 * b2,
        a3 * b1 - a1 * b3,
        a1 * b2 - a2 * b1,
    )
    common = reduce(gcd, (abs(value) for value in raw))
    if common == 0:
        raise AssertionError(("rank below two", k, indices))
    weights = tuple(value // common for value in raw)
    gamma = sum(weight * row[2] for weight, row in zip(weights, rows, strict=True))
    return weights, gamma


def quotient_bound_coefficient(
    k: int, owner: int, left: int, right: int, window: int
) -> int:
    constant, linear, quadratic = local_coefficients(k, owner)[:3]
    delta, _ = geometry(owner, left, right)
    return (
        9 * abs(constant) * window**3
        + 108 * abs(linear) * abs(delta)
        + 180 * abs(quadratic) * abs(delta)
    )


def signed_identity_report() -> dict[str, Any]:
    checks = 0
    for k in (5, 7, 9):
        for owner, left, right in (
            (1, 2, k),
            ((k + 1) // 2, 1, k),
            (k, 1, 2),
        ):
            for t, g in product(range(-8, 9), range(-4, 5)):
                if not reduced_identity_holds(k, owner, left, right, t, g):
                    raise AssertionError((k, owner, left, right, t, g))
                checks += 1
    return {"checks": checks, "all_hold": True}


@cache
def coefficient_geometry_report() -> dict[str, Any]:
    rows = []
    total_ordered = 0
    total_centers = 0
    total_zero = 0
    total_lattice = 0
    total_zero_weights = 0
    minimum_gamma: int | None = None
    maximum_gamma = 0
    minimum_nonzero: int | None = None
    maximum_reduced = 0
    maximum_case: list[int] | None = None
    for k, (window, _) in ROWS.items():
        center = (k + 1) // 2
        ordered = 0
        centers = 0
        zeros = 0
        row_bound = 0
        for owner, left, right in permutations(range(1, k + 1), 3):
            ordered += 1
            centers += owner == center
            value = reduced_coefficient(k, owner, left, right)
            if value == 0:
                zeros += 1
                if owner != center:
                    raise AssertionError(("noncentral zero", k, owner, left, right))
            else:
                absolute = abs(value)
                minimum_nonzero = (
                    absolute if minimum_nonzero is None else min(minimum_nonzero, absolute)
                )
                if absolute > maximum_reduced:
                    maximum_reduced = absolute
                    maximum_case = [k, owner, left, right]
            row_bound = max(
                row_bound,
                quotient_bound_coefficient(k, owner, left, right, window),
            )
        lattice_count = 0
        zero_weights = 0
        for indices in combinations(range(1, k + 1), 3):
            weights, gamma = lattice_weights(k, indices)
            lattice_count += 1
            zero_weights += sum(weight == 0 for weight in weights)
            if gamma == 0:
                raise AssertionError(("zero gamma", k, indices))
            absolute = abs(gamma)
            minimum_gamma = absolute if minimum_gamma is None else min(minimum_gamma, absolute)
            maximum_gamma = max(maximum_gamma, absolute)
        rows.append(
            {
                "k": k,
                "ordered_distinct_owner_triples": ordered,
                "center_owner_occurrences": centers,
                "zero_reduced_coefficients": zeros,
                "rank_two_lattice_triples": lattice_count,
                "zero_lattice_weight_components": zero_weights,
                "maximum_quotient_bound_coefficient": row_bound,
            }
        )
        total_ordered += ordered
        total_centers += centers
        total_zero += zeros
        total_lattice += lattice_count
        total_zero_weights += zero_weights
    return {
        "rows": rows,
        "ordered_distinct_owner_triples": total_ordered,
        "center_owner_occurrences": total_centers,
        "zero_reduced_coefficients": total_zero,
        "all_zeros_are_centers": total_zero == total_centers,
        "rank_two_lattice_triples": total_lattice,
        "all_lattice_gammas_nonzero": True,
        "zero_lattice_weight_components": total_zero_weights,
        "minimum_lattice_gamma": minimum_gamma,
        "maximum_lattice_gamma": maximum_gamma,
        "minimum_nonzero_reduced_coefficient": minimum_nonzero,
        "maximum_reduced_coefficient": maximum_reduced,
        "maximum_reduced_case": maximum_case,
    }


@cache
def two_zero_report() -> dict[str, Any]:
    rows = []
    total = 0
    closed = 0
    first_open_global = None
    for k, (_, loss_bound) in ROWS.items():
        center = (k + 1) // 2
        row_total = 0
        row_closed = 0
        zero_weight = 0
        numeric = 0
        first_open = None
        for indices in combinations(range(1, k + 1), 3):
            weights, gamma = lattice_weights(k, indices)
            coefficients = []
            for owner in indices:
                left, right = (index for index in indices if index != owner)
                coefficients.append(abs(reduced_coefficient(k, owner, left, right)))
            for zeros in combinations(range(3), 2):
                if any(indices[position] == center for position in zeros):
                    continue
                row_total += 1
                remaining = ({0, 1, 2} - set(zeros)).pop()
                weight = abs(weights[remaining])
                if weight == 0:
                    row_closed += 1
                    zero_weight += 1
                    continue
                first = coefficients[zeros[0]]
                second = coefficients[zeros[1]]
                if first == 0 or second == 0:
                    raise AssertionError("noncentral coefficient vanished")
                coefficient_lcm = first // gcd(first, second) * second
                majorant = coefficient_lcm**2 * abs(gamma) * loss_bound**12
                cutoff_side = weight * TARGET**2
                if majorant < cutoff_side:
                    row_closed += 1
                    numeric += 1
                elif first_open is None:
                    first_open = {
                        "indices": list(indices),
                        "zero_positions": list(zeros),
                        "remaining_weight": weight,
                        "coefficient_lcm": coefficient_lcm,
                        "gamma": abs(gamma),
                        "majorant_digits": len(str(majorant)),
                        "cutoff_side_digits": len(str(cutoff_side)),
                    }
        if first_open_global is None and first_open is not None:
            first_open_global = first_open
        rows.append(
            {
                "k": k,
                "noncentral_two_zero_cases": row_total,
                "closed_cases": row_closed,
                "zero_weight_contradictions": zero_weight,
                "numeric_closures": numeric,
                "first_open_case": first_open,
            }
        )
        total += row_total
        closed += row_closed
    k15 = next(row for row in rows if row["k"] == 15)
    return {
        "rows": rows,
        "noncentral_two_zero_cases": total,
        "closed_cases": closed,
        "all_closed_through_k13": all(
            row["closed_cases"] == row["noncentral_two_zero_cases"]
            for row in rows
            if row["k"] <= 13
        ),
        "k15_closed": k15["closed_cases"],
        "k15_total": k15["noncentral_two_zero_cases"],
        "k15_open": k15["noncentral_two_zero_cases"] - k15["closed_cases"],
        "first_open_case": first_open_global,
    }


def _local_lifts(
    k: int, owner: int, component: int, cofactor: int, opposite: int
) -> tuple[int, int, int]:
    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    second = 3 * constant * cofactor - 4 * linear * opposite**2
    third = -3 * second + 20 * quadratic * component * opposite**3
    fourth = 3 * third + component**2 * (
        -9 * linear * cofactor**2
        + 36 * quadratic * cofactor * opposite**2
        + 84 * cubic * opposite**4
    )
    return second, third, fourth


@cache
def small_fixture_report() -> dict[str, Any]:
    k = 5
    indices = (1, 2, 3)
    components = (3, 5, 2)
    g = 24
    residuals = (4_122, 4_125, 4_128)
    cofactors = tuple(
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    )
    t = prod(cofactors)
    d = g * prod(components)
    n = (residuals[0] + d) // 3 - indices[0]
    q = residuals[0] // d
    remainder_quotients = tuple(
        (residual - q * d) // component
        for residual, component in zip(residuals, components, strict=True)
    )
    normalization = len({residual // d for residual in residuals}) == 1
    normalization &= all(
        cofactor * component == q * (d // component) + remainder
        for cofactor, component, remainder in zip(
            cofactors, components, remainder_quotients, strict=True
        )
    )
    local_ok = True
    composed_ok = True
    restrictions_ok = True
    quotients = []
    for position, (owner, component, cofactor) in enumerate(
        zip(indices, components, cofactors, strict=True)
    ):
        others = tuple(pos for pos in range(3) if pos != position)
        left_position, right_position = others
        left = indices[left_position]
        right = indices[right_position]
        opposite = d // component
        second, third, fourth = _local_lifts(
            k, owner, component, cofactor, opposite
        )
        local_ok &= (
            second % component == 0
            and third % component**2 == 0
            and fourth % component**3 == 0
            and (n + owner) % component == 0
        )
        composed_second = second_obstruction(k, owner, left, right, t, g)
        composed_third = third_obstruction(k, owner, left, right, t, g, d)
        correction = fourth_correction(k, owner, left, right, t, g)
        composed_fourth = (
            3 * cofactors[left_position] * cofactors[right_position] * composed_third
            + component**2 * correction
        )
        quotient = composed_third // component**2
        quotients.append(quotient)
        constant = local_coefficients(k, owner)[0]
        reduced = (
            27
            * constant**2
            * cofactors[left_position]
            * cofactors[right_position]
            * quotient
            + reduced_coefficient(k, owner, left, right) * g**4
        )
        composed_ok &= (
            composed_second % component == 0
            and composed_third % component**2 == 0
            and composed_fourth % component**3 == 0
        )
        quotient_overlap = gcd(component, abs(quotient))
        left_overlap = gcd(component, cofactors[left_position])
        right_overlap = gcd(component, cofactors[right_position])
        bound = quotient_bound_coefficient(k, owner, left, right, ROWS[k][0])
        restrictions_ok &= (
            reduced % component == 0
            and (reduced_coefficient(k, owner, left, right) * g**4)
            % quotient_overlap
            == 0
            and abs(3 * (owner - left)) % left_overlap == 0
            and abs(3 * (owner - right)) % right_overlap == 0
            and 5 * abs(quotient) < bound * g**2 * cofactor
        )
    weights, gamma = lattice_weights(k, indices)
    lattice_lhs = sum(
        weight * component**2 * quotient
        for weight, component, quotient in zip(
            weights, components, quotients, strict=True
        )
    )
    block_equation = prod(n + d + j for j in range(1, k + 1)) == 4 * prod(
        n + j for j in range(1, k + 1)
    )
    return {
        "components": list(components),
        "g": g,
        "d": d,
        "residuals": list(residuals),
        "cofactors": list(cofactors),
        "all_local_lifts": local_ok,
        "all_composed_lifts": composed_ok,
        "quotient_normalization": normalization,
        "lattice_identity": lattice_lhs == g**2 * gamma,
        "all_quotient_restrictions": restrictions_ok,
        "block_equation": block_equation,
    }


def hostile_scope_report() -> dict[str, Any]:
    center = reduced_coefficient(5, 3, 1, 5)
    noncentral = reduced_coefficient(5, 1, 2, 3)
    P = Q = 8
    R = 1
    g = 2
    L = Gamma = W = 1
    d = g * P * Q * R
    premises_without_coprime = (
        (L * g**4) % P == 0
        and (L * g**4) % Q == 0
        and R**2 * W <= Gamma * g**2
    )
    conclusion = d**2 * W <= L**2 * Gamma * g**12
    return {
        "center_reduced_coefficient": center,
        "noncentral_reduced_coefficient": noncentral,
        "zero_weight_contradiction_requires_positive_g": True,
        "pairwise_coprimality_is_load_bearing": (
            premises_without_coprime and not conclusion and gcd(P, Q) != 1
        ),
        "center_containing_two_zero_cases_remain": True,
        "k15_noncentral_open_cases": two_zero_report()["k15_open"],
        "finite_two_zero_application_is_lean_wrapped": False,
    }


@cache
def report() -> dict[str, Any]:
    frozen = freeze_report()
    geometry_report = coefficient_geometry_report()
    two_zero = two_zero_report()
    safe = (
        frozen["all_match"]
        and geometry_report["all_zeros_are_centers"]
        and geometry_report["all_lattice_gammas_nonzero"]
        and two_zero["noncentral_two_zero_cases"] == 2_603
        and small_fixture_report()["all_quotient_restrictions"]
    )
    return {
        "freeze": frozen,
        "public_surface": public_surface_report(),
        "signed_identity": signed_identity_report(),
        "coefficient_geometry": geometry_report,
        "two_zero": two_zero,
        "small_fixture": small_fixture_report(),
        "scope": hostile_scope_report(),
        "verdict": "PASS partial package" if safe else "FAIL package",
        "safe_to_integrate_generic_lean": safe,
        "finite_two_zero_scan_attestation_ready": False,
        "closes_three_owner_branch": False,
        "closes_erdos_686": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
