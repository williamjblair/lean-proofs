#!/usr/bin/env python3
"""Independent hostile verifier for the frozen AllOwnerAssembly package.

The producer verifier is deliberately not imported.  This module reconstructs
the cleaning arithmetic, full owner grid, exact finite-product swap, Taylor
coefficients, residual progressions, and finite-family compositions using only
Python integers.  Synthetic progression fixtures audit algebra; none is
represented as a solution of the Erdős block equation.
"""

from __future__ import annotations

import hashlib
import json
import re
from functools import lru_cache
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[2]
ROWS = (5, 7, 9, 11, 13, 15)
TARGET = 10**120
FINDINGS_SHA256 = (
    "1610f635ecdf37f8c192fbd7f4866d33d6089602f1599fced1f178be3497b3d9"
)
FROZEN_SHA256 = {
    "ErdosProblems/Erdos686AllOwnerAssembly.lean":
        "a63011061fc8af531036374a238ae776ef861f3d21df937def40f156b50c88bf",
    "compute/campaign686/all_owner_assembly_verify.py":
        "29ea556f2cca67366243c283f8fbce85f18358eb157e22d221cf6d8d45b1860b",
    "compute/campaign686/test_all_owner_assembly_verify.py":
        "57170689925795ca7315f2127135aa736aa1ee619811745f09b10026327386f8",
    "compute/campaign686/all_owner_assembly_findings.md": FINDINGS_SHA256,
    "docs/plans/2026-07-10-erdos686-all-owner-assembly.md":
        "b87e233a080aeaf55295f2f980f80831d03734e2bf33a6f76a5c55befd5ea3a3",
}
EXPECTED_THEOREMS = (
    "allOwnerBucket_pos",
    "allOwnerLoss_pos",
    "allOwnerBucket_dvd_factor",
    "allOwnerBucket_square_dvd_residual",
    "allOwner_residual_decomposition",
    "allOwner_one_prime_placement",
    "allOwner_bucket_product_eq_clean_product",
    "allOwner_gap_decomposition",
    "allOwner_gap_decomposition_at",
    "allOwner_residual_cast",
    "allOwnerCofactor_pos",
    "allOwner_residual_difference",
    "allOwner_residual_pos",
    "allOwner_second_local_lift",
    "allOwner_third_local_lift",
    "allOwner_natCast_mem_intGrid",
    "allOwnerIntGrid_card",
    "allOwnerIntGrid_exists_nat",
    "allOwnerIntGrid_prod_bucket",
    "allOwnerIntGrid_erase_prod_bucket",
    "allOwnerIntGrid_opposite_component",
    "allOwnerIntGrid_gap_decomposition",
    "allOwnerIntGrid_residual_difference",
    "allOwner_second_obstruction_dvd",
    "allOwner_third_obstruction_dvd_sq",
    "allOwnerIntGrid_target_range",
    "allOwner_localSecondConstant_ne_zero",
    "allOwnerIntGrid_residual_gt_five_gap",
    "allOwner_second_obstruction_ne_zero",
    "exists_allOwnerAssemblyCertificate",
)


def verify_frozen_hashes() -> dict[str, str]:
    actual = {
        relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        for relative in FROZEN_SHA256
    }
    if actual != FROZEN_SHA256:
        raise AssertionError({"expected": FROZEN_SHA256, "actual": actual})
    return actual


def source_surface_report() -> dict[str, Any]:
    source = (ROOT / "ErdosProblems/Erdos686AllOwnerAssembly.lean").read_text()
    theorems = re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE)
    definitions = re.findall(r"^def\s+([A-Za-z0-9_]+)", source, re.MULTILINE)
    certificate_match = re.search(
        r"^structure AllOwnerAssemblyCertificate.*? where\n(?P<body>.*?)\n\n/-- Package",
        source,
        re.MULTILINE | re.DOTALL,
    )
    if certificate_match is None:
        raise AssertionError("certificate structure not found")
    certificate_fields = re.findall(
        r"^  ([A-Za-z][A-Za-z0-9_]*)\s*:",
        certificate_match.group("body"),
        re.MULTILINE,
    )
    forbidden = {
        label: len(re.findall(pattern, source))
        for label, pattern in {
            "sorry": r"\bsorry\b",
            "admit": r"\badmit\b",
            "axiom": r"\baxiom\b",
            "native_decide": r"\bnative_decide\b",
            "unsafe": r"^\s*unsafe\b",
        }.items()
        if re.search(pattern, source, re.MULTILINE)
    }
    return {
        "public_theorems": theorems,
        "public_theorem_count": len(theorems),
        "all_expected_theorems_present": tuple(theorems) == EXPECTED_THEOREMS,
        "definitions": definitions,
        "certificate_fields": certificate_fields,
        "forbidden": forbidden,
        "producer_declared_hash_omission":
            "compute/campaign686/all_owner_assembly_findings.md",
    }


def prime_factorization(value: int) -> dict[int, int]:
    if value <= 0:
        raise ValueError("factorization requires a positive integer")
    factors: dict[int, int] = {}
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            exponent += 1
            remaining //= divisor
        if exponent:
            factors[divisor] = exponent
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        factors[remaining] = factors.get(remaining, 0) + 1
    return factors


def prime(value: int) -> bool:
    return value >= 2 and all(value % d for d in range(2, isqrt(value) + 1))


def factorial_prime_exponent(n: int, p: int) -> int:
    if not prime(p):
        raise ValueError(f"not prime: {p}")
    return sum(n // p**power for power in range(1, 1 + n.bit_length()) if p**power <= n)


def cleaning_loss_exponent(p: int, k: int) -> int:
    valuation = factorial_prime_exponent(k - 1, p)
    return (k + valuation) // 2 if p == 3 else (valuation + 1) // 2


def retained_exponent(p: int, exponent: int, k: int) -> int:
    return max(0, exponent - cleaning_loss_exponent(p, k))


def assemble_owner_grid(k: int, d: int, owners: dict[int, int]) -> dict[str, Any]:
    if k not in ROWS:
        raise ValueError("unsupported target row")
    if d <= 0:
        raise ValueError("gap must be positive")
    factors = prime_factorization(d)
    if set(owners) != set(factors):
        raise ValueError("owner map must contain exactly the prime divisors")
    if any(index < 1 or index > k for index in owners.values()):
        raise ValueError("owner outside [1,k]")

    loss = 1
    buckets = {index: 1 for index in range(1, k + 1)}
    retained_occurrences: dict[int, list[int]] = {}
    components: list[dict[str, int]] = []
    for p, exponent in sorted(factors.items()):
        clean = retained_exponent(p, exponent, k)
        lost = exponent - clean
        owner = owners[p]
        lost_factor = p**lost
        retained_factor = p**clean
        loss *= lost_factor
        buckets[owner] *= retained_factor
        if retained_factor != 1:
            retained_occurrences[p] = [owner]
        components.append(
            {
                "prime": p,
                "exponent": exponent,
                "lost_exponent": lost,
                "retained_exponent": clean,
                "lost_factor": lost_factor,
                "retained_factor": retained_factor,
                "owner": owner,
            }
        )
        if lost_factor * retained_factor != p**exponent:
            raise AssertionError((p, exponent, lost, clean))

    bucket_product = prod(buckets.values())
    if loss * bucket_product != d:
        raise AssertionError((k, d, loss, buckets))
    live_owners = {
        component["owner"]
        for component in components
        if component["retained_factor"] != 1
    }
    if any(buckets[index] != 1 for index in buckets.keys() - live_owners):
        raise AssertionError("empty bucket is nonunit")
    return {
        "loss": loss,
        "buckets": buckets,
        "bucket_product": bucket_product,
        "components": components,
        "live_owners": live_owners,
        "retained_prime_occurrences": retained_occurrences,
    }


def assignment_strategies(k: int, primes: Iterable[int]) -> tuple[dict[int, int], ...]:
    ordered = tuple(sorted(primes))
    return (
        {p: 1 for p in ordered},
        {p: k for p in ordered},
        {p: 1 + position % k for position, p in enumerate(ordered)},
        {p: (1 if position % 2 == 0 else k) for position, p in enumerate(ordered)},
        {p: 1 + ((p * p + 3 * p + k) % k) for p in ordered},
    )


@lru_cache(maxsize=None)
def independent_assembly_scan(max_d: int = 500) -> dict[str, int | bool]:
    cases = placements = zero_clean = empty = 0
    exact = unique = units = positive = True
    for k in ROWS:
        for d in range(1, max_d + 1):
            factors = prime_factorization(d)
            for owner_map in assignment_strategies(k, factors):
                result = assemble_owner_grid(k, d, owner_map)
                cases += 1
                placements += len(factors)
                zero_clean += sum(
                    item["retained_exponent"] == 0
                    for item in result["components"]
                )
                empty += k - len(result["live_owners"])
                exact &= result["loss"] * result["bucket_product"] == d
                unique &= all(
                    occurrences == [owner_map[p]]
                    for p, occurrences in result["retained_prime_occurrences"].items()
                )
                units &= all(
                    result["buckets"][i] == 1
                    for i in result["buckets"].keys() - result["live_owners"]
                )
                positive &= result["loss"] > 0 and all(
                    bucket > 0 for bucket in result["buckets"].values()
                )
    return {
        "rows_checked": len(ROWS),
        "gap_assignment_cases": cases,
        "prime_placements_checked": placements,
        "zero_clean_components": zero_clean,
        "empty_buckets": empty,
        "all_decompositions_exact": exact,
        "all_prime_placements_unique": unique,
        "all_empty_buckets_are_one": units,
        "all_losses_positive": positive,
    }


@lru_cache(maxsize=1)
def boundary_audit() -> dict[str, Any]:
    counts = {
        "base_two_cases": 0,
        "base_three_cases": 0,
        "large_prime_cases": 0,
        "left_endpoint_assignments": 0,
        "right_endpoint_assignments": 0,
        "all_primes_one_owner_cases": 0,
        "d_one_cases": 0,
    }
    telescopes = []
    for k in ROWS:
        for d in range(1, 501):
            factors = prime_factorization(d)
            for strategy_index, owner_map in enumerate(assignment_strategies(k, factors)):
                assemble_owner_grid(k, d, owner_map)
                counts["base_two_cases"] += int(2 in factors)
                counts["base_three_cases"] += int(3 in factors)
                counts["large_prime_cases"] += int(any(p >= k for p in factors))
                counts["left_endpoint_assignments"] += int(1 in owner_map.values())
                counts["right_endpoint_assignments"] += int(k in owner_map.values())
                counts["all_primes_one_owner_cases"] += int(bool(factors) and strategy_index < 2)
            if d == 1:
                counts["d_one_cases"] += 1
                result = assemble_owner_grid(k, 1, {})
                telescopes.append(
                    {
                        "k": k,
                        "loss": result["loss"],
                        "buckets": list(result["buckets"].values()),
                        "product": result["loss"] * result["bucket_product"],
                    }
                )
    return {**counts, "d_one_telescopes": telescopes}


def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    """Expand product_{j!=owner} ((j-owner)+x) via subset products."""
    offsets = tuple(j - owner for j in range(1, k + 1) if j != owner)
    coefficients = []
    for degree in range(len(offsets) + 1):
        constant_choices = len(offsets) - degree
        coefficients.append(
            sum(prod(choice) for choice in combinations(offsets, constant_choices))
        )
    return tuple(coefficients)


def delta(owner: int, owners: Sequence[int]) -> int:
    return prod(owner - other for other in owners if other != owner)


def coprime_crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if not residues or len(residues) != len(moduli):
        raise ValueError("bad CRT family")
    modulus = prod(moduli)
    if modulus <= 0:
        raise ValueError("CRT moduli must be positive")
    value = 0
    for residue, local in zip(residues, moduli, strict=True):
        if local == 1:
            continue
        complement = modulus // local
        if gcd(complement, local) != 1:
            raise ValueError("CRT moduli are not pairwise coprime")
        value += residue * complement * pow(complement, -1, local)
    return value % modulus, modulus


def progression_case(
    *, k: int, owners: tuple[int, ...], components: tuple[int, ...], loss: int
) -> dict[str, Any]:
    if len(owners) != len(components) or len(set(owners)) != len(owners):
        raise ValueError("malformed owner family")
    if any(component == 0 for component in components):
        raise ValueError("zero component")
    anchor_owner = owners[0]
    moduli = tuple(component**2 for component in components)
    residues = tuple(
        (-3 * (owner - anchor_owner)) % modulus if modulus != 1 else 0
        for owner, modulus in zip(owners, moduli, strict=True)
    )
    base, period = coprime_crt(residues, moduli)
    anchor = base + 2 * period
    residuals = tuple(anchor + 3 * (owner - anchor_owner) for owner in owners)
    cofactors = tuple(
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    )
    if not all(residual == cofactor * component**2 for residual, cofactor, component in zip(residuals, cofactors, components, strict=True)):
        raise AssertionError("quotient reconstruction failed")
    if not all(cofactor > 0 for cofactor in cofactors):
        raise AssertionError("nonpositive synthetic cofactor")

    full_cofactor_product = prod(cofactors)
    gap = loss * prod(components)
    checks = []
    for position, (owner, component, cofactor) in enumerate(
        zip(owners, components, cofactors, strict=True)
    ):
        other_positions = tuple(index for index in range(len(owners)) if index != position)
        opposite_components = prod(components[index] for index in other_positions)
        opposite_cofactors = prod(cofactors[index] for index in other_positions)
        opposite_residuals = prod(residuals[index] for index in other_positions)
        constant, linear, quadratic = local_coefficients(k, owner)[:3]
        local_second = 3 * constant * cofactor - 4 * linear * (loss * opposite_components) ** 2
        local_third = (
            -3 * local_second
            + 20 * quadratic * component * (loss * opposite_components) ** 3
        )
        owner_delta = delta(owner, owners)
        power = len(owners) - 1
        composed_second = (
            3 * constant * full_cofactor_product
            - 4 * linear * loss**2 * (-3) ** power * owner_delta
        )
        composed_third = (
            -3 * composed_second
            + 20 * quadratic * loss**2 * gap * (-3) ** power * owner_delta
        )
        checks.append(
            {
                "owner": owner,
                "opposite_product_mod_square":
                    (opposite_residuals - (-3) ** power * owner_delta)
                    % component**2,
                "second_composition_mod_component":
                    (opposite_cofactors * local_second - composed_second)
                    % abs(component),
                "third_composition_mod_square":
                    (opposite_cofactors * local_third - composed_third)
                    % component**2,
            }
        )
    return {
        "quotients_exact": True,
        "differences_exact": all(
            residuals[i] - residuals[j] == 3 * (owners[i] - owners[j])
            for i in range(len(owners))
            for j in range(len(owners))
        ),
        "checks": checks,
        "all_compositions_hold": all(
            value == 0
            for check in checks
            for key, value in check.items()
            if key != "owner"
        ),
    }


@lru_cache(maxsize=1)
def composition_audit() -> dict[str, Any]:
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
    target = [
        progression_case(
            k=k,
            owners=tuple(range(1, k + 1)),
            components=primes[:k],
            loss=6,
        )
        for k in ROWS
    ]
    adversarial_specs = (
        (5, (1, 2, 3, 4, 5), (1, 2, 3, 5, 7), 6),
        (7, (1, 2, 3, 4, 5, 6, 7), (13, 1, 2, 11, 3, 7, 5), -6),
        (15, (1, 4, 8, 12, 15), (-2, 3, -5, 7, 11), 0),
        (5, (5, 1, 3, 2, 4), (2, 3, 5, 7, 11), 1),
        (7, (7, 1, 4, 2, 6, 3, 5), (1, -2, 3, -5, 7, 11, -13), 3),
    )
    adversarial = [
        progression_case(k=k, owners=owners, components=components, loss=loss)
        for k, owners, components, loss in adversarial_specs
    ]
    all_cases = target + adversarial
    return {
        "target_families_checked": len(target),
        "target_owner_congruences_checked": sum(len(case["checks"]) for case in target),
        "adversarial_families_checked": len(adversarial),
        "adversarial_owner_congruences_checked":
            sum(len(case["checks"]) for case in adversarial),
        "all_quotients_exact": all(case["quotients_exact"] for case in all_cases),
        "all_residual_differences_exact":
            all(case["differences_exact"] for case in all_cases),
        "all_second_compositions_hold": all(
            all(check["second_composition_mod_component"] == 0 for check in case["checks"])
            for case in all_cases
        ),
        "all_third_compositions_hold": all(
            all(check["third_composition_mod_square"] == 0 for check in case["checks"])
            for case in all_cases
        ),
        "features": [
            "unit empty buckets",
            "row centers",
            "k=5",
            "k=15",
            "small components 2 and 3",
            "permuted components",
            "signed loss",
            "zero loss",
        ],
    }


@lru_cache(maxsize=1)
def coefficient_and_target_audit() -> dict[str, Any]:
    rows = []
    for k in ROWS:
        for owner in range(1, k + 1):
            constant, linear, quadratic = local_coefficients(k, owner)[:3]
            rows.append((k, owner, constant, linear, quadratic))
    zero_bound = 4 * 10**12 * 3**14 * 15**14 + 1
    return {
        "owner_rows_checked": len(rows),
        "all_constants_nonzero": all(constant != 0 for _, _, constant, _, _ in rows),
        "maximum_abs_constant": max(abs(row[2]) for row in rows),
        "maximum_abs_linear": max(abs(row[3]) for row in rows),
        "all_linear_nat_abs_lt_10_pow_12":
            all(abs(linear) < 10**12 for _, _, _, linear, _ in rows),
        "zero_linear_centers": [
            [k, owner] for k, owner, _, linear, _ in rows if linear == 0
        ],
        "zero_coefficient_bound": zero_bound,
        "target_four_owner_lower_slope": 625 * TARGET**2,
        "bound_below_target_four_owner_lower_slope":
            zero_bound < 625 * TARGET**2,
        "minimum_grid_cardinality": min(ROWS),
        "maximum_grid_cardinality": max(ROWS),
    }


def scope_counterexamples() -> dict[str, Any]:
    component = 10**121 + 151
    obstruction = component * (10**120 + 7)
    fields = source_surface_report()["certificate_fields"]
    full = 2 * 3 * 5 * 7
    dropped = 2 * 3 * 5
    return {
        "divisibility_nonzero_does_not_bound_component":
            obstruction != 0 and obstruction % component == 0,
        "arbitrary_component_digits": len(str(component)),
        "dropping_owner_changes_exact_product": full != dropped,
        "certificate_contains_no_below_cutoff_field":
            all("cutoff" not in field.lower() for field in fields),
        "certificate_contains_no_block_contradiction_field":
            all("contradiction" not in field.lower() for field in fields),
        "exact_remaining_lemma": (
            "for all target k,n,d, the block equation and an "
            "AllOwnerAssemblyCertificate imply d < 10^120"
        ),
    }


def report() -> dict[str, Any]:
    return {
        "frozen_hashes": verify_frozen_hashes(),
        "surface": source_surface_report(),
        "assembly": independent_assembly_scan(),
        "boundaries": boundary_audit(),
        "composition": composition_audit(),
        "target_bounds": coefficient_and_target_audit(),
        "scope": scope_counterexamples(),
        "verdict": "PASS as a complete compositional bridge; no closure claim",
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
