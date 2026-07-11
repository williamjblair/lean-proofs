#!/usr/bin/env python3
"""Exact sign and size audit for the Erdős 686 quotient lattice.

The quotient package consumed here is frozen by SHA-256.  This file does not
alter it.  It studies the exact sign thresholds

    lambda = 20 E_s delta_s / C_s + 12 D_s delta_s / (C_s d)

for the three integers ``P_s^2 z_s`` in the lattice identity.  All ordering
and sign decisions use :class:`fractions.Fraction`.

The audit distinguishes three levels of evidence:

* coefficient cells, which use only ``d >= 10^120`` and ``125 < lambda < A^3``;
* one-sided cells, where the lattice gives genuine component bounds;
* full local fourth-lift fixtures, which additionally satisfy the square and
  local/composed congruences checked by the frozen validator.

It does not claim to close the mixed-cancellation branch.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from typing import Any, Iterable

import short_window_quotient_attack as frozen


TARGET = 10**120
REPO_ROOT = Path(__file__).resolve().parents[2]
FROZEN_SHA256 = {
    "ErdosProblems/Erdos686ShortWindowQuotient.lean":
        "bf18db4af88be78e7f4400a6cdc67b5bfb66ddef8dc12fe1072e7ad1b3903ccc",
    "ErdosProblems/Erdos686ShortWindowQuotientAudit.lean":
        "6ff2c48c62b4c77e560378888553485ede2502126ba468abbe1e45cbd373d54a",
    "compute/campaign686/short_window_quotient_attack.py":
        "af60785ae52a199a13a72759d133b6c1d6919a22dcb0d4b4172a892a2faafe0d",
    "compute/campaign686/test_short_window_quotient_attack.py":
        "37e2f43d6169ae6fe0cf7cecbb4c23213087504d87e4d873f1a27f33ec1d78f3",
    "compute/campaign686/short_window_quotient_findings.md":
        "b1365cdaba351c96f453c08737bf48babbe94a906a094512babd145f047f010a",
    "docs/plans/2026-07-10-erdos686-short-window-quotient-attack.md":
        "4c228bff302f2e5fcd45ff4b9347eec1101299412807953b202415cfd0eced29",
}


def sign(value: int | Fraction) -> int:
    return (value > 0) - (value < 0)


def fraction_string(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def file_sha256(relative_path: str) -> str:
    return hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()


def verify_frozen_package() -> dict[str, str]:
    actual = {path: file_sha256(path) for path in FROZEN_SHA256}
    if actual != FROZEN_SHA256:
        raise AssertionError({"expected": FROZEN_SHA256, "actual": actual})
    return actual


@dataclass(frozen=True)
class OwnerSignRow:
    owner: int
    constant: int
    linear: int
    quadratic: int
    delta: int
    root: Fraction
    correction: Fraction

    def threshold(self, d: int) -> Fraction:
        return self.root + self.correction / d

    def scaled_third(self, lam: Fraction, d: int) -> Fraction:
        """Return ``T_s / (g^2 d)`` exactly."""

        return (
            -9 * self.constant * lam
            + 180 * self.quadratic * self.delta
            + Fraction(108 * self.linear * self.delta, d)
        )


def owner_sign_rows(k: int, indices: tuple[int, int, int]) -> tuple[OwnerSignRow, ...]:
    result = []
    for owner in indices:
        others = tuple(index for index in indices if index != owner)
        constant, linear, quadratic = frozen.local_coefficients(k, owner)[:3]
        delta, _ = frozen.owner_geometry(owner, *others)
        result.append(
            OwnerSignRow(
                owner=owner,
                constant=constant,
                linear=linear,
                quadratic=quadratic,
                delta=delta,
                root=Fraction(20 * quadratic * delta, constant),
                correction=Fraction(12 * linear * delta, constant),
            )
        )
    return tuple(result)


def oriented_lattice(
    k: int, indices: tuple[int, int, int]
) -> tuple[tuple[int, int, int], int]:
    weights, gamma = frozen.lattice_weights(k, indices)
    if gamma < 0:
        return tuple(-weight for weight in weights), -gamma
    return weights, gamma


def term_signs_at(
    k: int,
    indices: tuple[int, int, int],
    lam: Fraction,
    d: int,
) -> tuple[int, int, int]:
    weights, _ = oriented_lattice(k, indices)
    rows = owner_sign_rows(k, indices)
    return tuple(
        sign(weight) * sign(row.scaled_third(lam, d)) if weight else 0
        for weight, row in zip(weights, rows, strict=True)
    )


def state_kind(term_signs: Iterable[int]) -> str:
    nonzero = set(term_signs) - {0}
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
    window, _ = frozen.ROWS[k]
    lower = Fraction(125)
    upper = Fraction(window**3)
    rows = owner_sign_rows(k, indices)
    internal = sorted(
        {
            row.threshold(d)
            for row in rows
            if lower < row.threshold(d) < upper
        }
    )
    points = [lower, *internal, upper]
    states: list[dict[str, Any]] = []
    for position, point in enumerate(points):
        if 0 < position < len(points) - 1:
            quotient_signs = tuple(
                sign(row.scaled_third(point, d)) for row in rows
            )
            term_signs = term_signs_at(k, indices, point, d)
            states.append(
                {
                    "kind": "boundary",
                    "at": point,
                    "term_signs": term_signs,
                    "quotient_signs": quotient_signs,
                    "orientation": state_kind(term_signs),
                    "zero_owners": [
                        row.owner
                        for row in rows
                        if row.scaled_third(point, d) == 0
                    ],
                }
            )
        if position + 1 < len(points):
            right = points[position + 1]
            sample = (point + right) / 2
            quotient_signs = tuple(
                sign(row.scaled_third(sample, d)) for row in rows
            )
            term_signs = term_signs_at(k, indices, sample, d)
            states.append(
                {
                    "kind": "open",
                    "left": point,
                    "right": right,
                    "sample": sample,
                    "term_signs": term_signs,
                    "quotient_signs": quotient_signs,
                    "orientation": state_kind(term_signs),
                    "zero_owners": [],
                }
            )
    return states


def ordering_stability_audit() -> dict[str, Any]:
    minimum_separation: Fraction | None = None
    minimum_case: tuple[Any, ...] | None = None
    maximum_correction = Fraction(0)
    maximum_case: tuple[Any, ...] | None = None
    equal_root_pairs: list[tuple[int, tuple[int, int, int], int, int]] = []
    zero_weights = 0
    for k, (window, _) in frozen.ROWS.items():
        endpoints = (Fraction(125), Fraction(window**3))
        for indices in combinations(range(1, k + 1), 3):
            weights, _ = oriented_lattice(k, indices)
            zero_weights += sum(weight == 0 for weight in weights)
            rows = owner_sign_rows(k, indices)
            for row in rows:
                if abs(row.correction) > maximum_correction:
                    maximum_correction = abs(row.correction)
                    maximum_case = (k, indices, row.owner, row.correction)
                for endpoint in endpoints:
                    separation = abs(row.root - endpoint)
                    if separation == 0:
                        raise AssertionError(("root at window endpoint", k, indices, row))
                    if minimum_separation is None or separation < minimum_separation:
                        minimum_separation = separation
                        minimum_case = (k, indices, row.owner, endpoint, row.root)
            for left, right in combinations(range(3), 2):
                separation = abs(rows[left].root - rows[right].root)
                if separation == 0:
                    equal_root_pairs.append(
                        (k, indices, rows[left].owner, rows[right].owner)
                    )
                    continue
                if minimum_separation is None or separation < minimum_separation:
                    minimum_separation = separation
                    minimum_case = (
                        k,
                        indices,
                        rows[left].owner,
                        rows[right].owner,
                        rows[left].root,
                        rows[right].root,
                    )

    if minimum_separation is None or maximum_case is None:
        raise AssertionError("empty target scan")
    if not 2 * maximum_correction / TARGET < minimum_separation:
        raise AssertionError("target correction could reorder unequal roots")
    if len(equal_root_pairs) != 27 or zero_weights != 27:
        raise AssertionError((len(equal_root_pairs), zero_weights))
    for k, indices, left_owner, right_owner in equal_root_pairs:
        weights, _ = oriented_lattice(k, indices)
        rows = owner_sign_rows(k, indices)
        positions = {
            row.owner: position for position, row in enumerate(rows)
        }
        if not (
            indices[1] == (k + 1) // 2
            and indices[0] + indices[2] == k + 1
            and weights[1] == 0
            and {left_owner, right_owner} == {indices[0], indices[2]}
            and weights[positions[left_owner]] != 0
            and weights[positions[right_owner]] != 0
        ):
            raise AssertionError((k, indices, weights, left_owner, right_owner))
    return {
        "minimum_unequal_root_or_endpoint_separation": fraction_string(
            minimum_separation
        ),
        "minimum_separation_case": repr(minimum_case),
        "maximum_absolute_correction": fraction_string(maximum_correction),
        "maximum_correction_case": repr(maximum_case),
        "twice_maximum_correction_over_target_is_smaller": True,
        "equal_root_pairs": len(equal_root_pairs),
        "zero_weight_components": zero_weights,
        "all_equal_roots_are_reflected_around_the_row_center": True,
    }


def one_sided_cases() -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []
    for k, (window, loss_bound) in frozen.ROWS.items():
        for indices in combinations(range(1, k + 1), 3):
            weights, gamma = oriented_lattice(k, indices)
            rows = owner_sign_rows(k, indices)
            positive_open = [
                state
                for state in sign_states(k, indices)
                if state["kind"] == "open"
                and state["orientation"] == "positive"
            ]
            if not positive_open:
                continue
            if len(positive_open) != 1:
                raise AssertionError((k, indices, positive_open))
            nonzero_positions = [
                position for position, weight in enumerate(weights) if weight
            ]
            if not (
                indices[1] == (k + 1) // 2
                and indices[0] + indices[2] == k + 1
                and weights[1] == 0
                and {abs(weights[position]) for position in nonzero_positions}
                == {1}
                and rows[0].root == rows[2].root
                and rows[0].correction == -rows[2].correction
            ):
                raise AssertionError((k, indices, weights, rows))
            fixed_coefficients = []
            for position in nonzero_positions:
                owner = indices[position]
                others = tuple(index for index in indices if index != owner)
                fixed_coefficients.append(
                    abs(
                        frozen.reduced_fourth_coefficient(
                            k, owner, *others
                        )
                    )
                )
            if len(set(fixed_coefficients)) != 1:
                raise AssertionError((k, indices, fixed_coefficients))
            fixed = fixed_coefficients[0]
            strict_gap_bound = window * gamma**2 * loss_bound**6
            shared = gcd(fixed**2, gamma)
            boundary_gap_bound = (
                window
                * fixed**2
                * gamma
                * loss_bound**10
                // shared
            )
            state = positive_open[0]
            cases.append(
                {
                    "k": k,
                    "indices": list(indices),
                    "weights": list(weights),
                    "gamma": gamma,
                    "shared_root": fraction_string(rows[0].root),
                    "half_width_times_d": fraction_string(
                        abs(rows[0].correction)
                    ),
                    "term_signs": list(state["term_signs"]),
                    "strict_gap_bound": strict_gap_bound,
                    "strict_gap_bound_below_target": strict_gap_bound < TARGET,
                    "zero_boundary_fixed_coefficient": fixed,
                    "zero_boundary_gcd": shared,
                    "zero_boundary_gap_bound": boundary_gap_bound,
                    "zero_boundary_gap_bound_below_target":
                        boundary_gap_bound < TARGET,
                }
            )
    return cases


def sign_cell_audit() -> dict[str, Any]:
    row_results: list[dict[str, Any]] = []
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
        f"{cell_kind}_{orientation}": 0
        for cell_kind in ("open", "boundary")
        for orientation in ("mixed", "positive", "negative", "zero")
    }
    for k in frozen.ROWS:
        row = {key: 0 for key in totals}
        row["k"] = k
        for indices in combinations(range(1, k + 1), 3):
            row["triples"] += 1
            weights, gamma = oriented_lattice(k, indices)
            if gamma <= 0:
                raise AssertionError((k, indices, weights, gamma))
            row["zero_weight_components"] += sum(
                weight == 0 for weight in weights
            )
            for state in sign_states(k, indices):
                key = f"{state['kind']}_{state['orientation']}"
                row[key] += 1
                quotient_key = (
                    f"{state['kind']}_{state_kind(state['quotient_signs'])}"
                )
                quotient_totals[quotient_key] += 1
        for key in totals:
            totals[key] += row[key]
        row_results.append(row)
    if totals["triples"] != 1_035:
        raise AssertionError(totals)
    if totals["open_negative"] or totals["open_zero"]:
        raise AssertionError(totals)
    if totals["boundary_negative"] or totals["boundary_zero"]:
        raise AssertionError(totals)
    return {
        "rows": row_results,
        "totals": totals,
        "quotient_sign_totals": quotient_totals,
    }


def weight_and_correction_audit() -> dict[str, Any]:
    raw_gamma_signs = {"positive": 0, "negative": 0, "zero": 0}
    oriented_components = {"positive": 0, "negative": 0, "zero": 0}
    oriented_patterns: dict[str, int] = {}
    minimum_gamma: int | None = None
    maximum_gamma = 0
    for k in frozen.ROWS:
        for indices in combinations(range(1, k + 1), 3):
            raw_weights, raw_gamma = frozen.lattice_weights(k, indices)
            raw_gamma_signs[
                "positive" if raw_gamma > 0 else "negative" if raw_gamma < 0 else "zero"
            ] += 1
            weights, gamma = oriented_lattice(k, indices)
            pattern = tuple(sign(weight) for weight in weights)
            oriented_patterns[str(pattern)] = oriented_patterns.get(str(pattern), 0) + 1
            for component_sign in pattern:
                oriented_components[
                    "positive"
                    if component_sign > 0
                    else "negative"
                    if component_sign < 0
                    else "zero"
                ] += 1
            minimum_gamma = gamma if minimum_gamma is None else min(minimum_gamma, gamma)
            maximum_gamma = max(maximum_gamma, gamma)
    if raw_gamma_signs["zero"] or minimum_gamma is None:
        raise AssertionError((raw_gamma_signs, minimum_gamma))
    return {
        "raw_gamma_signs": raw_gamma_signs,
        "oriented_weight_components": oriented_components,
        "oriented_weight_patterns": dict(sorted(oriented_patterns.items())),
        "minimum_positive_gamma": minimum_gamma,
        "maximum_positive_gamma": maximum_gamma,
    }


def coefficient_counterfixture() -> dict[str, Any]:
    """A target-scale mixed-sign fixture for the coefficient identity only."""

    k = 5
    indices = (1, 2, 3)
    d = TARGET
    g = 1
    lam = Fraction(188)
    t = 188 * d
    weights, gamma = oriented_lattice(k, indices)
    third_values = []
    for row in owner_sign_rows(k, indices):
        third_values.append(
            -9 * row.constant * t
            + 180 * row.quadratic * row.delta * g**2 * d
            + 108 * row.linear * row.delta * g**2
        )
    weighted = [
        weight * value
        for weight, value in zip(weights, third_values, strict=True)
    ]
    if sum(weighted) != gamma * g**2:
        raise AssertionError((weights, third_values, weighted, gamma))
    if state_kind(sign(value) for value in weighted) != "mixed":
        raise AssertionError(weighted)
    return {
        "scope": "coefficient identity only; not a square/local pseudo-witness",
        "k": k,
        "indices": list(indices),
        "d": d,
        "g": g,
        "lambda": fraction_string(lam),
        "weights": list(weights),
        "gamma": gamma,
        "third_values": third_values,
        "weighted_terms": weighted,
        "weighted_sum": sum(weighted),
        "term_signs": [sign(value) for value in weighted],
    }


def realized_counterfixtures() -> list[dict[str, Any]]:
    specifications = [
        {
            "name": "p2_p3_boundary_fixture",
            "indices": (1, 2, 3),
            "components": (3, 5, 2),
            "g": 24,
            "anchor_residual": 4_122,
        },
        {
            "name": "largest_recorded_small_short_fixture",
            "indices": (1, 2, 3),
            "components": (4, 3, 11),
            "g": 87,
            "anchor_residual": 151_728,
        },
    ]
    results = []
    for specification in specifications:
        validated = frozen.validate_short_tuple(
            k=5,
            indices=specification["indices"],
            components=specification["components"],
            g=specification["g"],
            anchor_residual=specification["anchor_residual"],
        )
        weights, gamma = oriented_lattice(5, specification["indices"])
        quotients = tuple(
            row["third_quotient"] for row in validated["composed_rows"]
        )
        weighted = tuple(
            weight * component**2 * quotient
            for weight, component, quotient in zip(
                weights,
                specification["components"],
                quotients,
                strict=True,
            )
        )
        if not (
            validated["lower_window"]
            and validated["upper_window"]
            and validated["all_local_lifts"]
            and validated["all_composed_lifts"]
            and validated["lattice_identity"]
            and not validated["block_equation"]
            and state_kind(sign(value) for value in weighted) == "mixed"
            and sum(weighted) == gamma * specification["g"] ** 2
        ):
            raise AssertionError((specification, validated, weighted))
        lam = Fraction(1)
        for residual in validated["residuals"]:
            lam *= residual
        lam /= validated["d"] ** 3
        results.append(
            {
                "name": specification["name"],
                "k": 5,
                "indices": list(specification["indices"]),
                "components": list(specification["components"]),
                "g": specification["g"],
                "d": validated["d"],
                "residuals": validated["residuals"],
                "cofactors": validated["cofactors"],
                "lambda": fraction_string(lam),
                "weights": list(weights),
                "gamma": gamma,
                "third_quotients": list(quotients),
                "weighted_terms": list(weighted),
                "weighted_sum": sum(weighted),
                "all_local_lifts": True,
                "all_composed_lifts": True,
                "short_window": True,
                "below_target": validated["d"] < TARGET,
                "block_equation": False,
            }
        )
    return results


def remaining_cancellation_lemma() -> dict[str, Any]:
    rows = []
    for k, (window, loss_bound) in frozen.ROWS.items():
        cutoff_budget = isqrt((TARGET - 1) // (window * loss_bound**6))
        maximum_gamma = max(
            abs(frozen.lattice_weights(k, indices)[1])
            for indices in combinations(range(1, k + 1), 3)
        )
        if not (
            maximum_gamma < cutoff_budget
            and window * cutoff_budget**2 * loss_bound**6 < TARGET
        ):
            raise AssertionError((k, cutoff_budget, maximum_gamma))
        rows.append(
            {
                "k": k,
                "window": window,
                "loss_bound": loss_bound,
                "H_k": cutoff_budget,
                "maximum_gamma": maximum_gamma,
                "minimum_available_negative_mass_allowance":
                    cutoff_budget - maximum_gamma,
                "cutoff_check": window
                * cutoff_budget**2
                * loss_bound**6,
            }
        )
    return {
        "status": "unproved remaining lemma",
        "definition": (
            "Orient the primitive lattice so Gamma>0 and put "
            "V_s=P_s^2*max(1,abs(w_s*z_s))."
        ),
        "claim": (
            "For every target solution left after the proved one-sided "
            "cutoffs, there are two distinct owners r,s with "
            "V_r <= H_k*g^2 and V_s <= H_k*g^2."
        ),
        "consequence": (
            "Because V_i >= P_i^2, two component squares are <= H_k*g^2; "
            "the short upper "
            "window gives d < A_k*H_k^2*g^6 < 10^120."
        ),
        "mixed_cell_sufficient_form": (
            "If U_s=w_s*P_s^2*z_s and N=sum(max(0,-U_s)), then "
            "N <= (H_k-Gamma)*g^2 supplies the claim whenever at least "
            "two weighted quotients are nonzero."
        ),
        "single_zero_boundary_form": (
            "On the ten still-live reflected zero boundaries the claim is "
            "exactly the missing H_k*g^2 bound for the zero-quotient "
            "endpoint, since the other endpoint is already bounded by "
            "Gamma*g^2."
        ),
        "rows": rows,
    }


def boundary_audit() -> dict[str, Any]:
    telescopes = []
    for k, n in ((9, 2), (15, 4)):
        holds = frozen.block_product(k, n + 1) == 4 * frozen.block_product(k, n)
        if not holds:
            raise AssertionError((k, n))
        telescopes.append({"k": k, "n": n, "d": 1, "equation": True})
    return {
        "d_eq_one_telescopes": telescopes,
        "p2_p3_fixture_rechecked": realized_counterfixtures()[0],
    }


def full_audit() -> dict[str, Any]:
    hashes = verify_frozen_package()
    stability = ordering_stability_audit()
    cells = sign_cell_audit()
    one_sided = one_sided_cases()
    if len(one_sided) != 9:
        raise AssertionError(one_sided)
    strict_closed = sum(case["strict_gap_bound_below_target"] for case in one_sided)
    boundary_closed = 2 * sum(
        case["zero_boundary_gap_bound_below_target"] for case in one_sided
    )
    if strict_closed != 9 or boundary_closed != 8:
        raise AssertionError((strict_closed, boundary_closed))
    return {
        "frozen_package_sha256": hashes,
        "ordering_stability": stability,
        "weights_and_correction": weight_and_correction_audit(),
        "sign_cells": cells,
        "one_sided_cases": one_sided,
        "one_sided_summary": {
            "strict_positive_slivers": 9,
            "strict_positive_slivers_below_target_by_size": strict_closed,
            "positive_zero_boundaries": 18,
            "positive_zero_boundaries_below_target_by_current_bounds":
                boundary_closed,
            "positive_zero_boundaries_still_unresolved": 18 - boundary_closed,
        },
        "target_scale_coefficient_counterfixture": coefficient_counterfixture(),
        "realized_short_fourth_lift_counterfixtures": realized_counterfixtures(),
        "remaining_cancellation_lemma": remaining_cancellation_lemma(),
        "boundary_audit": boundary_audit(),
    }


def main() -> None:
    print(json.dumps(full_audit(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
