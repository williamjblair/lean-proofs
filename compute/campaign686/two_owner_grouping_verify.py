#!/usr/bin/env python3
"""Exact verifier for the finite two-owner grouping checkpoint.

The verifier is deliberately independent of Lean evaluation.  It recomputes
factorizations and Legendre valuations with Python integers, exhausts all
binary owner assignments for small gaps, and exercises the unit/zero-cleaned
and coincident-owner boundaries that are easiest to mishandle in the product
assembly.
"""

from __future__ import annotations

import hashlib
import json
import re
from itertools import product
from math import gcd, isqrt
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "ErdosProblems/Erdos686TwoOwnerGrouping.lean"
AGGREGATE_SOURCE = ROOT / "ErdosProblems/Erdos686TwoOwnerAggregate.lean"
ROWS = (5, 7, 9, 11, 13, 15)
EXPECTED_LOSSES = {
    5: 108,
    7: 1_620,
    9: 136_080,
    11: 1_224_720,
    13: 242_494_560,
    15: 18_914_575_680,
}
EXPECTED_SOURCE_SHA256 = (
    "63799ee4a2cc6fc0632776c231ac0961ddc038d60348c1b2fc43def3803797ef"
)
EXPECTED_PUBLIC_THEOREMS = (
    "globalResidualGroupedLossFactor_mul_clean",
    "globalResidualGroupedLossFactor_dvd_targetAggregateLoss",
    "globalResidualGroupedLoss_le_targetAggregateLoss",
    "globalResidualGrouped_decomposition",
    "globalResidualGroupedLeft_coprime_right",
    "globalResidualGroupedLeft_dvd_factor",
    "globalResidualGroupedRight_dvd_factor",
    "globalResidualGroupedLeft_square_dvd_residual",
    "globalResidualGroupedRight_square_dvd_residual",
    "hasAtMostTwoGlobalResidualOwners_of_assignment",
    "exists_globalResidualOwnerAssignment",
    "two_owner_range_equation_below_cutoff",
    "exists_globalResidualOwnerAssignment_not_two_cover",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    return all(value % divisor for divisor in range(2, isqrt(value) + 1))


def primes_below(bound: int) -> list[int]:
    return [value for value in range(2, bound) if is_prime(value)]


def factorization(value: int) -> dict[int, int]:
    if value <= 0:
        raise ValueError("factorization is restricted to positive integers")
    result: dict[int, int] = {}
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        while remaining % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            remaining //= divisor
        divisor += 1
    if remaining > 1:
        result[remaining] = result.get(remaining, 0) + 1
    return result


def factorial_valuation(n: int, prime: int) -> int:
    if not is_prime(prime):
        raise ValueError(f"not prime: {prime}")
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


def aggregate_loss(k: int) -> int:
    result = 1
    for prime in primes_below(k):
        result *= prime ** loss_exponent(prime, k)
    return result


def parse_lean_loss_table() -> dict[int, int]:
    text = AGGREGATE_SOURCE.read_text()
    section = text.split("def targetAggregateLoss", 1)[1].split("| _ =>", 1)[0]
    return {
        int(k): int(value.replace("_", ""))
        for k, value in re.findall(r"\|\s*(\d+)\s*=>\s*([\d_]+)", section)
    }


def assemble(
    k: int,
    d: int,
    owners: dict[int, int],
    i: int,
    j: int,
) -> tuple[int, int, int, list[dict[str, int]]]:
    """Mirror the Lean factors, including first-owner precedence."""

    g = left = right = 1
    components: list[dict[str, int]] = []
    for prime, exponent in factorization(d).items():
        clean = clean_exponent(prime, exponent, k)
        loss = exponent - clean
        owner = owners[prime]
        if clean != 0 and owner not in (i, j):
            raise ValueError("nontrivial cleaned owner lies outside the cover")
        loss_factor = prime**loss
        clean_factor = prime**clean
        left_factor = clean_factor if owner == i else 1
        right_factor = clean_factor if owner != i and owner == j else 1
        if prime**exponent != loss_factor * left_factor * right_factor:
            raise AssertionError((k, d, prime, exponent, owner, i, j))
        g *= loss_factor
        left *= left_factor
        right *= right_factor
        components.append(
            {
                "prime": prime,
                "exponent": exponent,
                "clean_exponent": clean,
                "loss_factor": loss_factor,
                "clean_factor": clean_factor,
                "owner": owner,
                "left_factor": left_factor,
                "right_factor": right_factor,
            }
        )
    return g, left, right, components


def _assert_component_divisibilities(
    components: Iterable[dict[str, int]],
    left: int,
    right: int,
    i: int,
    j: int,
) -> None:
    # These exact multiples model the four targets in the assignment
    # predicate.  When i=j, first-owner precedence makes right=1, and one
    # common target is used for both buckets.
    if i == j:
        factor_i = left * right * 7
        residual_i = (left * right) ** 2 * 11
        factor_targets = {i: factor_i}
        residual_targets = {i: residual_i}
    else:
        factor_targets = {i: left * 7, j: right * 11}
        residual_targets = {i: left**2 * 13, j: right**2 * 17}
    for component in components:
        owner = component["owner"]
        clean_factor = component["clean_factor"]
        if clean_factor == 1 and owner not in factor_targets:
            # Zero-clean components impose only 1-divisibility and may use an
            # owner outside the two-value cover.
            continue
        if factor_targets[owner] % clean_factor:
            raise AssertionError(("factor", component, factor_targets))
        if residual_targets[owner] % clean_factor**2:
            raise AssertionError(("square", component, residual_targets))
    if factor_targets[i] % left or residual_targets[i] % left**2:
        raise AssertionError(("left aggregate", left, factor_targets, residual_targets))
    if factor_targets[j] % right or residual_targets[j] % right**2:
        raise AssertionError(("right aggregate", right, factor_targets, residual_targets))


def exhaustive_grouping_certificate(max_d: int = 2000) -> dict[str, Any]:
    assignment_cases = 0
    same_owner_cases = 0
    zero_clean_components = 0
    outside_owner_zero_clean_components = 0
    primes_at_least_k = 0
    both_unit = left_unit = right_unit = 0
    nontrivial_left = nontrivial_right = 0
    maximum_ratio: tuple[int, int, int] = (0, 1, 0)

    i, j, outside = 2, 4, 99
    for k in ROWS:
        G = aggregate_loss(k)
        for d in range(1, max_d + 1):
            factors = list(factorization(d))
            for bits in product((0, 1), repeat=len(factors)):
                owners = {
                    prime: (i if side == 0 else j)
                    for prime, side in zip(factors, bits)
                }
                g, left, right, components = assemble(k, d, owners, i, j)
                if d != g * left * right or gcd(left, right) != 1 or g > G:
                    raise AssertionError((k, d, bits, g, left, right, G))
                for component in components:
                    if G % component["loss_factor"]:
                        raise AssertionError(("loss divisor", k, d, component, G))
                    zero_clean_components += component["clean_exponent"] == 0
                    primes_at_least_k += component["prime"] >= k
                    if component["prime"] >= k and loss_exponent(component["prime"], k) != 0:
                        raise AssertionError(("large prime loss", k, component))
                _assert_component_divisibilities(components, left, right, i, j)
                assignment_cases += 1
                both_unit += left == right == 1
                left_unit += left == 1
                right_unit += right == 1
                nontrivial_left += left > 1
                nontrivial_right += right > 1
                maximum_ratio = max(maximum_ratio, (g, G, d))

            # Coincident owners are a distinct boundary: every retained
            # component goes left and the right bucket is exactly one.
            same_owners = {prime: i for prime in factors}
            g, left, right, components = assemble(k, d, same_owners, i, i)
            if d != g * left * right or right != 1 or gcd(left, right) != 1:
                raise AssertionError(("same owner", k, d, g, left, right))
            _assert_component_divisibilities(components, left, right, i, i)
            same_owner_cases += 1

            # A zero-clean component may use an arbitrary owner because the
            # quantified range condition explicitly exempts exponent zero.
            for component in components:
                if component["clean_exponent"] != 0:
                    continue
                altered = dict(same_owners)
                altered[component["prime"]] = outside
                g0, left0, right0, components0 = assemble(k, d, altered, i, i)
                if (g0, left0, right0) != (g, left, right):
                    raise AssertionError(("zero clean owner", k, d, component))
                _assert_component_divisibilities(components0, left0, right0, i, i)
                outside_owner_zero_clean_components += 1

    if min(
        assignment_cases,
        same_owner_cases,
        zero_clean_components,
        outside_owner_zero_clean_components,
        primes_at_least_k,
        both_unit,
        left_unit,
        right_unit,
        nontrivial_left,
        nontrivial_right,
    ) <= 0:
        raise AssertionError("a required grouping boundary was not exercised")
    return {
        "max_d": max_d,
        "assignment_cases": assignment_cases,
        "same_owner_cases": same_owner_cases,
        "zero_clean_components": zero_clean_components,
        "outside_owner_zero_clean_components": outside_owner_zero_clean_components,
        "primes_at_least_k_components": primes_at_least_k,
        "both_buckets_unit": both_unit,
        "left_bucket_unit": left_unit,
        "right_bucket_unit": right_unit,
        "nontrivial_left_bucket": nontrivial_left,
        "nontrivial_right_bucket": nontrivial_right,
        "maximum_loss_ratio_fixture": maximum_ratio,
    }


def range_rejection_certificate() -> dict[str, int]:
    rejected = 0
    zero_clean_accepted = 0
    for k in ROWS:
        # Exponent one is nontrivial for a prime >= k because its loss is 0.
        prime = next(value for value in range(k, 2 * k + 20) if is_prime(value))
        try:
            assemble(k, prime, {prime: 99}, 2, 4)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError(("outside nontrivial owner accepted", k, prime))

        # A sufficiently small exponent of 3 is completely cleaned in every
        # row and therefore legally ignored by the two-value range predicate.
        g, left, right, _ = assemble(k, 3, {3: 99}, 2, 4)
        if (g, left, right) != (3, 1, 1):
            raise AssertionError(("zero-clean outside owner", k, g, left, right))
        zero_clean_accepted += 1
    return {
        "outside_nontrivial_rejected": rejected,
        "outside_zero_clean_accepted": zero_clean_accepted,
    }


def strip_lean_comments_and_strings(text: str) -> str:
    output: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                output.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                output.extend("  ")
                i += 2
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            char = text[i]
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                output.append(" ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            output.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            output.append(text[i])
            i += 1
    return "".join(output)


def source_gate_certificate() -> dict[str, Any]:
    code = strip_lean_comments_and_strings(SOURCE.read_text())
    forbidden: dict[str, list[int]] = {}
    for token, pattern in {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "axiom": r"^\s*axiom\b",
        "unsafe": r"^\s*unsafe\b",
    }.items():
        lines = [
            number
            for number, line in enumerate(code.splitlines(), 1)
            if re.search(pattern, line)
        ]
        if lines:
            forbidden[token] = lines
    public_theorems = tuple(
        re.findall(r"(?m)^theorem\s+([A-Za-z0-9_']+)", code)
    )
    imports = tuple(re.findall(r"(?m)^import\s+([^\s]+)", code))
    return {
        "source_sha256": sha256(SOURCE),
        "forbidden": forbidden,
        "imports": imports,
        "public_theorems": public_theorems,
        "public_theorem_count": len(public_theorems),
    }


def report(max_d: int = 2000) -> dict[str, Any]:
    recomputed = {k: aggregate_loss(k) for k in ROWS}
    parsed = parse_lean_loss_table()
    if recomputed != EXPECTED_LOSSES or parsed != EXPECTED_LOSSES:
        raise AssertionError((recomputed, parsed))
    source = source_gate_certificate()
    if source["forbidden"]:
        raise AssertionError(source["forbidden"])
    if source["source_sha256"] != EXPECTED_SOURCE_SHA256:
        raise AssertionError(source["source_sha256"])
    if source["imports"] != ("ErdosProblems.Erdos686TwoOwnerAggregate",):
        raise AssertionError(source["imports"])
    if source["public_theorems"] != EXPECTED_PUBLIC_THEOREMS:
        raise AssertionError(source["public_theorems"])
    return {
        "source": source,
        "loss_table": {"recomputed": recomputed, "lean": parsed},
        "grouping": exhaustive_grouping_certificate(max_d),
        "range_boundaries": range_rejection_certificate(),
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
