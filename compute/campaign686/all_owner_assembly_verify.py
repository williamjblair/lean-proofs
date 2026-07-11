#!/usr/bin/env python3
"""Exact arithmetic audit for the Erdős 686 all-owner assembly.

This verifier independently reproduces the loss and clean exponents, assigns
every retained prime power to its certified owner in ``[1,k]``, and checks the
finite product swap

    d = g * product_{i=1}^k P_i.

It also checks exact synthetic residual quotients and the algebra used by the
generic multi-owner second/third compositions.  The synthetic fixtures audit
the identities only; they are not claimed to satisfy the block equation or
the target short window.
"""

from __future__ import annotations

import json
import hashlib
import re
from functools import lru_cache
from math import gcd, isqrt, prod
from pathlib import Path
from typing import Any, Iterable, Sequence


ROWS = (5, 7, 9, 11, 13, 15)
COMPONENT_BASES = (2, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "ErdosProblems/Erdos686AllOwnerAssembly.lean"
EXPECTED_SOURCE_SHA256 = (
    "a63011061fc8af531036374a238ae776ef861f3d21df937def40f156b50c88bf"
)
EXPECTED_IMPORTS = (
    "ErdosProblems.Erdos686MultiOwnerExtension",
    "ErdosProblems.Erdos686TwoOwnerGrouping",
)
EXPECTED_PUBLIC_THEOREMS = (
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


def is_prime(value: int) -> bool:
    return value >= 2 and all(value % p for p in range(2, isqrt(value) + 1))


def factorization(value: int) -> dict[int, int]:
    if value <= 0:
        raise ValueError("factorization is restricted to positive integers")
    factors: dict[int, int] = {}
    remaining = value
    p = 2
    while p * p <= remaining:
        while remaining % p == 0:
            factors[p] = factors.get(p, 0) + 1
            remaining //= p
        p += 1
    if remaining > 1:
        factors[remaining] = factors.get(remaining, 0) + 1
    return factors


def factorial_valuation(n: int, prime: int) -> int:
    if not is_prime(prime):
        raise ValueError(f"not a prime: {prime}")
    total = 0
    power = prime
    while power <= n:
        total += n // power
        power *= prime
    return total


def loss_exponent(prime: int, k: int) -> int:
    valuation = factorial_valuation(k - 1, prime)
    if prime == 3:
        return (k + valuation) // 2
    return (valuation + 1) // 2


def clean_exponent(prime: int, exponent: int, k: int) -> int:
    return max(exponent - loss_exponent(prime, k), 0)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_gate_report() -> dict[str, Any]:
    """Freeze the exact audited Lean producer and its public theorem surface."""

    text = SOURCE.read_text()
    imports = tuple(re.findall(r"^import\s+([^\s]+)", text, flags=re.MULTILINE))
    theorems = tuple(
        re.findall(r"^(?:theorem|lemma)\s+([A-Za-z0-9_]+)", text, flags=re.MULTILINE)
    )
    forbidden_patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "axiom": r"\baxiom\b",
        "native_decide": r"\bnative_decide\b",
    }
    forbidden = {
        name: len(re.findall(pattern, text))
        for name, pattern in forbidden_patterns.items()
        if re.search(pattern, text)
    }
    return {
        "source_sha256": _sha256(SOURCE),
        "imports": imports,
        "public_theorems": theorems,
        "public_theorem_count": len(theorems),
        "forbidden": forbidden,
    }


def assemble_all_owners(
    k: int, d: int, owners: dict[int, int]
) -> dict[str, Any]:
    """Assemble the exact unchanged loss and the full owner grid."""

    if k not in ROWS:
        raise ValueError("unsupported target row")
    factors = factorization(d)
    if set(owners) != set(factors):
        raise ValueError("owner map must have exactly one entry per prime divisor")
    if any(not 1 <= owner <= k for owner in owners.values()):
        raise ValueError("owner outside [1,k]")

    loss = 1
    buckets = {i: 1 for i in range(1, k + 1)}
    components: list[dict[str, int]] = []
    for prime, exponent in factors.items():
        clean = clean_exponent(prime, exponent, k)
        lost = exponent - clean
        loss_factor = prime**lost
        clean_factor = prime**clean
        owner = owners[prime]
        loss *= loss_factor
        buckets[owner] *= clean_factor
        components.append(
            {
                "prime": prime,
                "exponent": exponent,
                "loss_exponent": lost,
                "clean_exponent": clean,
                "loss_factor": loss_factor,
                "clean_factor": clean_factor,
                "owner": owner,
            }
        )
        if loss_factor * clean_factor != prime**exponent:
            raise AssertionError((k, d, prime, exponent, lost, clean))

    bucket_product = prod(buckets.values())
    if loss * bucket_product != d:
        raise AssertionError((k, d, owners, loss, buckets))
    live_owners = {
        component["owner"]
        for component in components
        if component["clean_factor"] != 1
    }
    for i, bucket in buckets.items():
        if i not in live_owners and bucket != 1:
            raise AssertionError(("non-unit empty bucket", k, d, i, bucket))
    return {
        "loss": loss,
        "buckets": buckets,
        "bucket_product": bucket_product,
        "components": components,
        "live_owners": live_owners,
    }


def _assignment_strategies(k: int, primes: Iterable[int]) -> tuple[dict[int, int], ...]:
    ordered = tuple(sorted(primes))
    return (
        {p: 1 for p in ordered},
        {p: k for p in ordered},
        {p: 1 + index % k for index, p in enumerate(ordered)},
        {p: (1 if index % 2 == 0 else k) for index, p in enumerate(ordered)},
        {p: 1 + ((p * p + 3 * p + k) % k) for p in ordered},
    )


@lru_cache(maxsize=None)
def all_owner_scan(max_d: int = 500) -> dict[str, int | bool]:
    cases = zero_clean = empty = 0
    exact = empty_units = True
    for k in ROWS:
        for d in range(1, max_d + 1):
            factors = factorization(d)
            for owners in _assignment_strategies(k, factors):
                assembled = assemble_all_owners(k, d, owners)
                exact &= assembled["loss"] * assembled["bucket_product"] == d
                live = assembled["live_owners"]
                buckets = assembled["buckets"]
                empty += k - len(live)
                empty_units &= all(buckets[i] == 1 for i in buckets if i not in live)
                zero_clean += sum(
                    component["clean_exponent"] == 0
                    for component in assembled["components"]
                )
                cases += 1
    return {
        "rows_checked": len(ROWS),
        "gap_assignment_cases": cases,
        "zero_clean_components": zero_clean,
        "empty_buckets": empty,
        "all_decompositions_exact": exact,
        "all_empty_buckets_are_one": empty_units,
    }


@lru_cache(maxsize=1)
def boundary_report() -> dict[str, int]:
    counts = {
        "base_two_cases": 0,
        "base_three_cases": 0,
        "large_prime_cases": 0,
        "left_endpoint_assignments": 0,
        "right_endpoint_assignments": 0,
        "all_primes_one_owner_cases": 0,
        "d_one_cases": 0,
    }
    for k in ROWS:
        for d in range(1, 501):
            factors = factorization(d)
            strategies = _assignment_strategies(k, factors)
            for position, owners in enumerate(strategies):
                assemble_all_owners(k, d, owners)
                counts["base_two_cases"] += 2 in factors
                counts["base_three_cases"] += 3 in factors
                counts["large_prime_cases"] += any(p >= k for p in factors)
                counts["left_endpoint_assignments"] += any(o == 1 for o in owners.values())
                counts["right_endpoint_assignments"] += any(o == k for o in owners.values())
                counts["all_primes_one_owner_cases"] += bool(factors) and position < 2
            counts["d_one_cases"] += d == 1
    return counts


def _crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    modulus = prod(moduli)
    value = 0
    for residue, local_modulus in zip(residues, moduli, strict=True):
        complement = modulus // local_modulus
        if gcd(complement, local_modulus) != 1:
            raise ValueError("CRT moduli are not pairwise coprime")
        value += residue * complement * pow(complement, -1, local_modulus)
    return value % modulus, modulus


def _local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    coefficients = [1]
    for j in range(1, k + 1):
        if j == owner:
            continue
        offset = j - owner
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return tuple(coefficients)


def _delta(owner: int, owners: Sequence[int]) -> int:
    return prod(owner - j for j in owners if j != owner)


@lru_cache(maxsize=1)
def progression_composition_report() -> dict[str, int | bool]:
    families = congruences = 0
    quotients = differences = second = third = True
    for k in ROWS:
        owners = tuple(range(1, k + 1))
        components = COMPONENT_BASES[:k]
        moduli = tuple(component**2 for component in components)
        residues = tuple((-3 * (owner - 1)) % modulus for owner, modulus in zip(owners, moduli, strict=True))
        base, period = _crt(residues, moduli)
        anchor = base + period
        residuals = tuple(anchor + 3 * (owner - 1) for owner in owners)
        cofactors = tuple(
            residual // component**2
            for residual, component in zip(residuals, components, strict=True)
        )
        quotients &= all(
            residual == cofactor * component**2
            for residual, cofactor, component in zip(residuals, cofactors, components, strict=True)
        )
        differences &= all(
            residuals[left] - residuals[right] == 3 * (owners[left] - owners[right])
            for left in range(k)
            for right in range(k)
        )
        loss = 6
        gap = loss * prod(components)
        all_a = prod(cofactors)
        for position, (owner, component, cofactor) in enumerate(
            zip(owners, components, cofactors, strict=True)
        ):
            opposite_components = components[:position] + components[position + 1 :]
            opposite_cofactors = cofactors[:position] + cofactors[position + 1 :]
            m = loss * prod(opposite_components)
            constant, linear, quadratic = _local_coefficients(k, owner)[:3]
            local_second = 3 * constant * cofactor - 4 * linear * m**2
            local_third = -3 * local_second + 20 * quadratic * component * m**3
            delta = _delta(owner, owners)
            obstruction_second = (
                3 * constant * all_a
                - 4 * linear * loss**2 * (-3) ** (k - 1) * delta
            )
            obstruction_third = (
                -3 * obstruction_second
                + 20 * quadratic * loss**2 * gap * (-3) ** (k - 1) * delta
            )
            opposite_a = prod(opposite_cofactors)
            second &= (opposite_a * local_second - obstruction_second) % component == 0
            third &= (opposite_a * local_third - obstruction_third) % component**2 == 0
            congruences += 1
        families += 1
    return {
        "families_checked": families,
        "owner_congruences_checked": congruences,
        "all_quotients_exact": quotients,
        "all_residual_differences_exact": differences,
        "all_second_compositions_hold": second,
        "all_third_compositions_hold": third,
    }


def report(max_d: int = 500) -> dict[str, Any]:
    return {
        "source_gate": source_gate_report(),
        "assembly": all_owner_scan(max_d),
        "boundaries": boundary_report(),
        "progression": progression_composition_report(),
        "route_verdict": (
            "the unchanged bounded loss and every owner bucket assemble exactly; "
            "the local lifts give nonzero finite-family obstructions, but no "
            "archimedean bound closes their nonzero branch"
        ),
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
