#!/usr/bin/env python3
"""Independent hostile verification of the frozen lattice-sign package.

This module intentionally does not import either producer Python module.  It
reconstructs the local polynomial coefficients from elementary symmetric
sums, rebuilds the primitive lattice, enumerates every exact rational sign
cell, and rechecks the two claimed fourth-lift fixtures from first principles.

The outcome is deliberately partial: the generic Lean bridges and the exact
finite arithmetic are sound, but the 2,381 mixed open cells and ten live
positive zero boundaries are not closed by the producer package.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from fractions import Fraction
from functools import cache, reduce
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path
from typing import Any, Iterable


TARGET = 10**120
ROWS: dict[int, tuple[int, int]] = {
    5: (14, 108),
    7: (17, 1_620),
    9: (23, 136_080),
    11: (26, 1_224_720),
    13: (29, 242_494_560),
    15: (35, 18_914_575_680),
}
REPO_ROOT = Path(__file__).resolve().parents[2]
FROZEN_SHA256 = {
    "ErdosProblems/Erdos686ShortWindowLatticeSign.lean":
        "1085863ae92e0d98841da3d667fa12de774ec843fe2a97988173f414dd8c905c",
    "ErdosProblems/Erdos686ShortWindowLatticeSignAudit.lean":
        "f89374d984a160b8fded04c9062a073ef8b2594cde75715c021ec7a2da6a0142",
    "compute/campaign686/short_window_lattice_sign_attack.py":
        "d66bbe0222141513156c5b277eaa971444e80436865dd69c30bc931f8d6587fc",
    "compute/campaign686/test_short_window_lattice_sign_attack.py":
        "a9c06f32dbc081b6491b33906c914cc94b2a78937be91257150ab253e02104dc",
    "compute/campaign686/short_window_lattice_sign_findings.md":
        "25730c340d97e95855b37d266394b71ce826c945c15ecfaccab1355ce9082560",
    "docs/plans/2026-07-10-erdos686-lattice-sign-attack.md":
        "04cdd6d53bbb5ef75318bb1480c2c49047aecc401726002eb7a9b3e015f9d448",
}
EXPECTED_PUBLIC_THEOREMS = (
    "square_le_of_nonzero_weighted_term",
    "two_component_short_window_gap_bound",
    "two_component_short_window_gap_lt_cutoff",
    "two_weighted_terms_short_window_gap_lt_cutoff",
    "reflected_one_sided_short_window_gap_lt_cutoff",
    "coprime_square_product_dvd_lcm",
    "reflected_boundary_lcm_bound",
    "reflected_one_zero_short_window_gap_bound",
    "reflected_one_zero_short_window_gap_lt_cutoff",
)


def _sha256(relative_path: str) -> str:
    return hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()


def freeze_report() -> dict[str, Any]:
    actual = {path: _sha256(path) for path in FROZEN_SHA256}
    return {
        "files": len(FROZEN_SHA256),
        "expected": FROZEN_SHA256,
        "actual": actual,
        "all_match": actual == FROZEN_SHA256,
    }


def _strip_lean_comments(source: str) -> str:
    """Remove enough comments to audit top-level declarations reliably."""

    source = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", source)


def public_surface_report() -> dict[str, Any]:
    source = _strip_lean_comments(
        (REPO_ROOT / "ErdosProblems/Erdos686ShortWindowLatticeSign.lean")
        .read_text()
    )
    importer = _strip_lean_comments(
        (REPO_ROOT / "ErdosProblems/Erdos686ShortWindowLatticeSignAudit.lean")
        .read_text()
    )
    theorem_names = tuple(
        re.findall(r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']+)", source)
    )
    importer_declarations = tuple(
        re.findall(r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']+)", importer)
    )
    if theorem_names != EXPECTED_PUBLIC_THEOREMS:
        raise AssertionError((theorem_names, EXPECTED_PUBLIC_THEOREMS))
    return {
        "public_theorems": len(theorem_names),
        "theorem_names": list(theorem_names),
        "producer_importer_declarations": list(importer_declarations),
        "producer_importer_is_independent": bool(importer_declarations),
    }


def _sign(value: int | Fraction) -> int:
    return (value > 0) - (value < 0)


def _fraction_string(value: Fraction) -> str:
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    """Build ``prod_{j != owner} (z + j-owner)`` by symmetric sums.

    This deliberately uses a different construction from the producer's
    iterative polynomial multiplication.
    """

    if owner not in range(1, k + 1):
        raise ValueError("owner outside row")
    offsets = tuple(column - owner for column in range(1, k + 1) if column != owner)
    degree = len(offsets)
    return tuple(
        sum(prod(choice) for choice in combinations(offsets, degree - power))
        for power in range(degree + 1)
    )


def owner_geometry(owner: int, left: int, right: int) -> tuple[int, int]:
    return (owner - left) * (owner - right), 2 * owner - left - right


def reduced_fourth_coefficient(k: int, owner: int, left: int, right: int) -> int:
    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta, sigma = owner_geometry(owner, left, right)
    return 108 * delta * (
        -108 * linear**3 * delta
        + constant * linear * (-108 * linear * sigma + 324 * quadratic * delta)
        + 567 * constant**2 * cubic * delta
    )


@dataclass(frozen=True)
class OwnerRow:
    owner: int
    constant: int
    linear: int
    quadratic: int
    delta: int

    @property
    def root(self) -> Fraction:
        return Fraction(20 * self.quadratic * self.delta, self.constant)

    @property
    def correction(self) -> Fraction:
        return Fraction(12 * self.linear * self.delta, self.constant)

    def threshold(self, d: int) -> Fraction:
        return self.root + self.correction / d

    def scaled_third(self, lam: Fraction, d: int) -> Fraction:
        return (
            -9 * self.constant * lam
            + 180 * self.quadratic * self.delta
            + Fraction(108 * self.linear * self.delta, d)
        )


def owner_rows(k: int, indices: tuple[int, int, int]) -> tuple[OwnerRow, ...]:
    result: list[OwnerRow] = []
    for owner in indices:
        left, right = (index for index in indices if index != owner)
        constant, linear, quadratic = local_coefficients(k, owner)[:3]
        delta, _ = owner_geometry(owner, left, right)
        result.append(OwnerRow(owner, constant, linear, quadratic, delta))
    return tuple(result)


def raw_lattice(k: int, indices: tuple[int, int, int]) -> tuple[tuple[int, int, int], int]:
    coefficient_rows: list[tuple[int, int, int]] = []
    for row in owner_rows(k, indices):
        coefficient_rows.append(
            (
                -9 * row.constant,
                180 * row.quadratic * row.delta,
                108 * row.linear * row.delta,
            )
        )
    (a1, b1, _), (a2, b2, _), (a3, b3, _) = coefficient_rows
    cross = (
        a2 * b3 - a3 * b2,
        a3 * b1 - a1 * b3,
        a1 * b2 - a2 * b1,
    )
    divisor = reduce(gcd, map(abs, cross))
    if divisor == 0:
        raise AssertionError((k, indices, "rank below two"))
    weights = tuple(value // divisor for value in cross)
    gamma = sum(
        weight * row[2]
        for weight, row in zip(weights, coefficient_rows, strict=True)
    )
    return weights, gamma


def oriented_lattice(
    k: int, indices: tuple[int, int, int]
) -> tuple[tuple[int, int, int], int]:
    weights, gamma = raw_lattice(k, indices)
    return (
        (tuple(-weight for weight in weights), -gamma)
        if gamma < 0
        else (weights, gamma)
    )


def _kind(signs: Iterable[int]) -> str:
    nonzero = set(signs) - {0}
    if nonzero == {-1, 1}:
        return "mixed"
    if nonzero == {1}:
        return "positive"
    if nonzero == {-1}:
        return "negative"
    return "zero"


def sign_states(
    k: int, indices: tuple[int, int, int], d: int = TARGET
) -> list[dict[str, Any]]:
    window, _ = ROWS[k]
    rows = owner_rows(k, indices)
    lower, upper = Fraction(125), Fraction(window**3)
    cuts = sorted(
        {
            row.threshold(d)
            for row in rows
            if lower < row.threshold(d) < upper
        }
    )
    points = (lower, *cuts, upper)
    weights, _ = oriented_lattice(k, indices)

    def values(at: Fraction) -> tuple[tuple[int, ...], tuple[int, ...]]:
        quotient_signs = tuple(_sign(row.scaled_third(at, d)) for row in rows)
        term_signs = tuple(
            _sign(weight) * quotient_sign if weight else 0
            for weight, quotient_sign in zip(weights, quotient_signs, strict=True)
        )
        return quotient_signs, term_signs

    states: list[dict[str, Any]] = []
    for position, point in enumerate(points):
        if 0 < position < len(points) - 1:
            quotient_signs, term_signs = values(point)
            states.append(
                {
                    "kind": "boundary",
                    "at": point,
                    "quotient_signs": quotient_signs,
                    "term_signs": term_signs,
                    "orientation": _kind(term_signs),
                }
            )
        if position + 1 < len(points):
            sample = (point + points[position + 1]) / 2
            quotient_signs, term_signs = values(sample)
            states.append(
                {
                    "kind": "open",
                    "left": point,
                    "right": points[position + 1],
                    "quotient_signs": quotient_signs,
                    "term_signs": term_signs,
                    "orientation": _kind(term_signs),
                }
            )
    return states


@cache
def _ordering_stability_data() -> tuple[Fraction, Fraction, tuple[Any, ...], int]:
    minimum: Fraction | None = None
    maximum_correction = Fraction(0)
    equal_pairs: list[tuple[int, tuple[int, int, int], int, int]] = []
    for k, (window, _) in ROWS.items():
        for indices in combinations(range(1, k + 1), 3):
            rows = owner_rows(k, indices)
            for row in rows:
                maximum_correction = max(maximum_correction, abs(row.correction))
                for endpoint in (Fraction(125), Fraction(window**3)):
                    separation = abs(row.root - endpoint)
                    if not separation:
                        raise AssertionError((k, indices, "root at endpoint"))
                    minimum = separation if minimum is None else min(minimum, separation)
            for left, right in combinations(range(3), 2):
                separation = abs(rows[left].root - rows[right].root)
                if separation:
                    minimum = separation if minimum is None else min(minimum, separation)
                else:
                    equal_pairs.append(
                        (k, indices, rows[left].owner, rows[right].owner)
                    )
    if minimum is None:
        raise AssertionError("empty scan")
    for k, indices, left_owner, right_owner in equal_pairs:
        weights, _ = oriented_lattice(k, indices)
        if not (
            indices[1] == (k + 1) // 2
            and indices[0] + indices[2] == k + 1
            and weights[1] == 0
            and {left_owner, right_owner} == {indices[0], indices[2]}
        ):
            raise AssertionError((k, indices, weights, left_owner, right_owner))
    return minimum, maximum_correction, tuple(equal_pairs), len(equal_pairs)


def ordering_stability_report() -> dict[str, Any]:
    minimum, maximum, equal_pairs, count = _ordering_stability_data()
    return {
        "minimum_separation": _fraction_string(minimum),
        "maximum_correction": _fraction_string(maximum),
        "target_correction_cannot_reorder": 2 * maximum / TARGET < minimum,
        "equal_root_pairs": count,
        "all_equal_pairs_are_reflected": all(
            indices[1] == (k + 1) // 2 and indices[0] + indices[2] == k + 1
            for k, indices, _, _ in equal_pairs
        ),
    }


@cache
def _weight_data() -> tuple[dict[str, int], dict[str, int], int, int, int]:
    raw_signs = {"positive": 0, "negative": 0, "zero": 0}
    components = {"positive": 0, "negative": 0, "zero": 0}
    triples = 0
    minimum: int | None = None
    maximum = 0
    for k in ROWS:
        for indices in combinations(range(1, k + 1), 3):
            triples += 1
            _, raw_gamma = raw_lattice(k, indices)
            raw_signs["positive" if raw_gamma > 0 else "negative" if raw_gamma < 0 else "zero"] += 1
            weights, gamma = oriented_lattice(k, indices)
            for weight in weights:
                components["positive" if weight > 0 else "negative" if weight < 0 else "zero"] += 1
            minimum = gamma if minimum is None else min(minimum, gamma)
            maximum = max(maximum, gamma)
    if minimum is None:
        raise AssertionError("empty scan")
    return raw_signs, components, triples, minimum, maximum


def weight_report() -> dict[str, Any]:
    raw_signs, components, triples, minimum, maximum = _weight_data()
    return {
        "triples": triples,
        "raw_gamma_signs": raw_signs,
        "oriented_weight_components": components,
        "minimum_gamma": minimum,
        "maximum_gamma": maximum,
    }


@cache
def _sign_cell_data() -> tuple[dict[str, int], dict[str, int], tuple[dict[str, int], ...]]:
    totals = {
        "triples": 0,
        "zero_weight_components": 0,
        "open_mixed": 0,
        "open_positive": 0,
        "open_negative": 0,
        "open_zero": 0,
        "boundary_mixed": 0,
        "boundary_positive": 0,
        "boundary_negative": 0,
        "boundary_zero": 0,
    }
    quotient_totals = {
        f"{cell}_{kind}": 0
        for cell in ("open", "boundary")
        for kind in ("mixed", "positive", "negative", "zero")
    }
    row_reports: list[dict[str, int]] = []
    for k in ROWS:
        row = {key: 0 for key in totals}
        row["k"] = k
        for indices in combinations(range(1, k + 1), 3):
            row["triples"] += 1
            weights, gamma = oriented_lattice(k, indices)
            if gamma <= 0:
                raise AssertionError((k, indices, gamma))
            row["zero_weight_components"] += sum(weight == 0 for weight in weights)
            for state in sign_states(k, indices):
                row[f"{state['kind']}_{state['orientation']}"] += 1
                quotient_totals[
                    f"{state['kind']}_{_kind(state['quotient_signs'])}"
                ] += 1
        for key in totals:
            totals[key] += row[key]
        row_reports.append(row)
    return totals, quotient_totals, tuple(row_reports)


def sign_cell_report() -> dict[str, Any]:
    totals, quotient_totals, rows = _sign_cell_data()
    return {"totals": totals, "quotient_sign_totals": quotient_totals, "rows": list(rows)}


@cache
def _one_sided_rows() -> tuple[dict[str, Any], ...]:
    result: list[dict[str, Any]] = []
    for k, (window, loss_bound) in ROWS.items():
        for indices in combinations(range(1, k + 1), 3):
            positive = [
                state
                for state in sign_states(k, indices)
                if state["kind"] == "open" and state["orientation"] == "positive"
            ]
            if not positive:
                continue
            if len(positive) != 1:
                raise AssertionError((k, indices, len(positive)))
            weights, gamma = oriented_lattice(k, indices)
            rows = owner_rows(k, indices)
            nonzero = [position for position, weight in enumerate(weights) if weight]
            if not (
                indices[1] == (k + 1) // 2
                and indices[0] + indices[2] == k + 1
                and weights[1] == 0
                and [abs(weights[position]) for position in nonzero] == [1, 1]
                and rows[0].root == rows[2].root
                and rows[0].correction == -rows[2].correction
            ):
                raise AssertionError((k, indices, weights))
            fixed_values = []
            for position in nonzero:
                owner = indices[position]
                left, right = (index for index in indices if index != owner)
                fixed_values.append(abs(reduced_fourth_coefficient(k, owner, left, right)))
            if len(set(fixed_values)) != 1:
                raise AssertionError((k, indices, fixed_values))
            fixed = fixed_values[0]
            shared = gcd(fixed**2, gamma)
            strict_bound = window * gamma**2 * loss_bound**6
            boundary_bound = window * fixed**2 * gamma * loss_bound**10 // shared
            result.append(
                {
                    "k": k,
                    "indices": list(indices),
                    "weights": list(weights),
                    "gamma": gamma,
                    "root": _fraction_string(rows[0].root),
                    "correction": _fraction_string(abs(rows[0].correction)),
                    "term_signs": list(positive[0]["term_signs"]),
                    "strict_gap_bound": strict_bound,
                    "strict_excluded": strict_bound < TARGET,
                    "boundary_fixed_coefficient": fixed,
                    "boundary_shared_factor": shared,
                    "boundary_gap_bound": boundary_bound,
                    "both_boundaries_excluded": boundary_bound < TARGET,
                }
            )
    return tuple(result)


def one_sided_report() -> dict[str, Any]:
    rows = list(_one_sided_rows())
    closed_boundary_pairs = sum(row["both_boundaries_excluded"] for row in rows)
    return {
        "rows": rows,
        "strict_slivers": len(rows),
        "strict_slivers_excluded": sum(row["strict_excluded"] for row in rows),
        "positive_zero_boundaries": 2 * len(rows),
        "zero_boundaries_excluded": 2 * closed_boundary_pairs,
        "zero_boundaries_live": 2 * (len(rows) - closed_boundary_pairs),
    }


def coefficient_counterfixture() -> dict[str, Any]:
    k, indices, d, g, lam = 5, (1, 2, 3), TARGET, 1, Fraction(188)
    weights, gamma = oriented_lattice(k, indices)
    t = lam.numerator * d // lam.denominator
    third_values = [
        -9 * row.constant * t
        + 180 * row.quadratic * row.delta * g**2 * d
        + 108 * row.linear * row.delta * g**2
        for row in owner_rows(k, indices)
    ]
    weighted = [
        weight * value
        for weight, value in zip(weights, third_values, strict=True)
    ]
    if sum(weighted) != gamma or _kind(map(_sign, weighted)) != "mixed":
        raise AssertionError((weights, gamma, weighted))
    return {
        "k": k,
        "indices": list(indices),
        "d": d,
        "g": g,
        "lambda": _fraction_string(lam),
        "weights": list(weights),
        "gamma": gamma,
        "third_values": third_values,
        "weighted_terms": weighted,
        "term_signs": [_sign(value) for value in weighted],
    }


def _second_obstruction(k: int, owner: int, left: int, right: int, t: int, g: int) -> int:
    constant, linear = local_coefficients(k, owner)[:2]
    delta, _ = owner_geometry(owner, left, right)
    return 3 * (constant * t - 12 * linear * g**2 * delta)


def _third_obstruction(
    k: int, owner: int, left: int, right: int, t: int, g: int, d: int
) -> int:
    quadratic = local_coefficients(k, owner)[2]
    delta, _ = owner_geometry(owner, left, right)
    return -3 * _second_obstruction(k, owner, left, right, t, g) + 180 * quadratic * g**2 * delta * d


def _fourth_correction(k: int, owner: int, left: int, right: int, t: int, g: int) -> int:
    _, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta, sigma = owner_geometry(owner, left, right)
    return (
        -9 * linear * t**2
        - 108 * linear * t * g**2 * sigma
        + 324 * quadratic * t * g**2 * delta
        + 6804 * cubic * g**4 * delta**2
    )


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


def _block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def _validate_fixture(specification: dict[str, Any]) -> dict[str, Any]:
    k = 5
    indices = tuple(specification["indices"])
    components = tuple(specification["components"])
    g = specification["g"]
    anchor_residual = specification["anchor_residual"]
    residuals = tuple(
        anchor_residual + 3 * (index - indices[0]) for index in indices
    )
    if any(residual % component**2 for residual, component in zip(residuals, components, strict=True)):
        raise AssertionError((specification, "square residual"))
    cofactors = tuple(
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    )
    d = g * prod(components)
    t = prod(cofactors)
    n_integral = (anchor_residual + d) % 3 == 0
    n = (anchor_residual + d) // 3 - indices[0] if n_integral else -1
    local_checks: list[bool] = []
    composed_checks: list[bool] = []
    quotients: list[int] = []
    for position, (owner, component, cofactor) in enumerate(
        zip(indices, components, cofactors, strict=True)
    ):
        other_positions = tuple(candidate for candidate in range(3) if candidate != position)
        left_position, right_position = other_positions
        left, right = indices[left_position], indices[right_position]
        opposite = d // component
        second, third, fourth = _local_lifts(k, owner, component, cofactor, opposite)
        local_checks.append(
            second % component == 0
            and third % component**2 == 0
            and fourth % component**3 == 0
            and n_integral
            and (n + owner) % component == 0
        )
        composed_second = _second_obstruction(k, owner, left, right, t, g)
        composed_third = _third_obstruction(k, owner, left, right, t, g, d)
        if composed_third % component**2:
            raise AssertionError((specification, owner, "nonintegral quotient"))
        quotient = composed_third // component**2
        quotients.append(quotient)
        correction = _fourth_correction(k, owner, left, right, t, g)
        composed_fourth = (
            3 * cofactors[left_position] * cofactors[right_position] * composed_third
            + component**2 * correction
        )
        constant = local_coefficients(k, owner)[0]
        fixed = reduced_fourth_coefficient(k, owner, left, right)
        reduced = (
            27 * constant**2 * cofactors[left_position] * cofactors[right_position] * quotient
            + fixed * g**4
        )
        overlap_left = gcd(component, cofactors[left_position])
        overlap_right = gcd(component, cofactors[right_position])
        quotient_gcd = gcd(component, abs(quotient))
        composed_checks.append(
            composed_second % component == 0
            and composed_third % component**2 == 0
            and composed_fourth % component**3 == 0
            and reduced % component == 0
            and fixed * g**4 % quotient_gcd == 0
            and 3 * abs(owner - left) % overlap_left == 0
            and 3 * abs(owner - right) % overlap_right == 0
            and 9 * abs((owner - left) * (owner - right))
            % gcd(component, cofactors[left_position] * cofactors[right_position])
            == 0
        )
    weights, gamma = oriented_lattice(k, indices)
    weighted = [
        weight * component**2 * quotient
        for weight, component, quotient in zip(weights, components, quotients, strict=True)
    ]
    lower = all(5 * d < residual for residual in residuals)
    upper = all(residual < ROWS[k][0] * d for residual in residuals)
    block_equation = (
        n_integral
        and n >= 0
        and _block_product(k, n + d) == 4 * _block_product(k, n)
    )
    lam = Fraction(prod(residuals), d**3)
    if not (
        all(local_checks)
        and all(composed_checks)
        and lower
        and upper
        and sum(weighted) == gamma * g**2
        and _kind(map(_sign, weighted)) == "mixed"
        and not block_equation
    ):
        raise AssertionError((specification, local_checks, composed_checks, weighted))
    return {
        "name": specification["name"],
        "components": list(components),
        "g": g,
        "d": d,
        "residuals": list(residuals),
        "cofactors": list(cofactors),
        "lambda": _fraction_string(lam),
        "weights": list(weights),
        "gamma": gamma,
        "third_quotients": quotients,
        "weighted_terms": weighted,
        "term_signs": [_sign(value) for value in weighted],
        "all_local_lifts": all(local_checks),
        "all_composed_lifts": all(composed_checks),
        "short_window": lower and upper,
        "block_equation": block_equation,
    }


def realized_counterfixtures() -> list[dict[str, Any]]:
    return [
        _validate_fixture(
            {
                "name": "p2_p3_boundary_fixture",
                "indices": (1, 2, 3),
                "components": (3, 5, 2),
                "g": 24,
                "anchor_residual": 4_122,
            }
        ),
        _validate_fixture(
            {
                "name": "largest_recorded_small_short_fixture",
                "indices": (1, 2, 3),
                "components": (4, 3, 11),
                "g": 87,
                "anchor_residual": 151_728,
            }
        ),
    ]


def remaining_scope_report() -> dict[str, Any]:
    rows = []
    for k, (window, loss_bound) in ROWS.items():
        budget = isqrt((TARGET - 1) // (window * loss_bound**6))
        maximum_gamma = max(
            abs(raw_lattice(k, indices)[1])
            for indices in combinations(range(1, k + 1), 3)
        )
        cutoff_check = window * budget**2 * loss_bound**6
        if not (maximum_gamma < budget and cutoff_check < TARGET):
            raise AssertionError((k, budget, maximum_gamma, cutoff_check))
        rows.append(
            {
                "k": k,
                "H_k": budget,
                "maximum_gamma": maximum_gamma,
                "cutoff_check": cutoff_check,
            }
        )
    cells = sign_cell_report()["totals"]
    one_sided = one_sided_report()
    return {
        "rows": rows,
        "mixed_open_cells": cells["open_mixed"],
        "live_positive_zero_boundaries": one_sided["zero_boundaries_live"],
        "remaining_size_lemma": "OPEN",
        "finite_scan_is_lean_wrapped": False,
    }


def report() -> dict[str, Any]:
    frozen = freeze_report()
    surface = public_surface_report()
    stability = ordering_stability_report()
    weights = weight_report()
    cells = sign_cell_report()
    one_sided = one_sided_report()
    fixtures = realized_counterfixtures()
    remaining = remaining_scope_report()
    if not (
        frozen["all_match"]
        and surface["public_theorems"] == 9
        and stability["target_correction_cannot_reorder"]
        and weights["triples"] == 1_035
        and cells["totals"]["open_positive"] == 9
        and one_sided["strict_slivers_excluded"] == 9
        and all(row["all_local_lifts"] and row["all_composed_lifts"] for row in fixtures)
        and remaining["remaining_size_lemma"] == "OPEN"
    ):
        raise AssertionError("hostile audit invariant failed")
    return {
        "verdict": "PASS partial package",
        "safe_to_integrate_generic_lean": True,
        "finite_row_scan_attestation_ready": False,
        "closes_three_owner_branch": False,
        "closes_erdos_686": False,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(report(), indent=2, sort_keys=True))
