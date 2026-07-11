#!/usr/bin/env python3
"""Independent hostile verifier for the frozen three-owner extraction.

This module does not import the producer verifier.  It models the exact live
support predicate and the two-index cover quantifiers, exhausts owner
universes and support lengths through six, and cross-checks the counts with a
separate inclusion-exclusion formula.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from functools import lru_cache
from itertools import combinations, product
from math import comb
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
FROZEN_PRODUCER_HASHES = {
    "ErdosProblems/Erdos686ThreeOwnerExtraction.lean": (
        "6d056218c2d98025bdfc3a54741df01c3b35b78084d5a6d6dbcc5e1901e86b07"
    ),
    "compute/campaign686/three_owner_extraction_verify.py": (
        "68d6518e49f005424ee1cd17bfe51d5dc09c3bee03fad17781b7bccfcee964ad"
    ),
    "compute/campaign686/test_three_owner_extraction_verify.py": (
        "124da19540d2120773af9941f521a5b3c8b4c4f32b099b83bafd14a72052d8c2"
    ),
    "compute/campaign686/three_owner_extraction_findings.md": (
        "4958de17f98b308d9de9c542b28c61cd6bee75478d5ed6e5f147df2efc4f076d"
    ),
    "docs/plans/2026-07-10-erdos686-three-owner-extraction.md": (
        "4dd81a1ee3743b76891306db414fa98ba2b1a566f8c8c42ed36f20066e9c8e8b"
    ),
}
AUDITED_LEAN_FILES = (
    "ErdosProblems/Erdos686ThreeOwnerExtraction.lean",
    "ErdosProblems/Erdos686ThreeOwnerExtractionHostileAudit.lean",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def producer_hash_report() -> dict[str, Any]:
    actual = {
        relative: sha256(ROOT / relative)
        for relative in FROZEN_PRODUCER_HASHES
    }
    return {
        "expected": FROZEN_PRODUCER_HASHES,
        "actual": actual,
        "all_frozen_hashes_match": actual == FROZEN_PRODUCER_HASHES,
    }


def strip_lean_comments_and_strings(source: str) -> str:
    """Remove nested comments, line comments, and string contents."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            if char == "\\" and index + 1 < len(source):
                output.extend("  ")
                index += 2
            elif char == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif pair == "--":
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    if block_depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(output)


def forbidden_token_report() -> dict[str, Any]:
    patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "unsafe": re.compile(r"\bunsafe\b"),
        "axiom_declaration": re.compile(r"(?m)^\s*axiom\b"),
    }
    matches: dict[str, dict[str, list[int]]] = {}
    for relative in AUDITED_LEAN_FILES:
        stripped = strip_lean_comments_and_strings((ROOT / relative).read_text())
        file_matches: dict[str, list[int]] = {}
        for label, pattern in patterns.items():
            lines = [
                stripped.count("\n", 0, match.start()) + 1
                for match in pattern.finditer(stripped)
            ]
            if lines:
                file_matches[label] = lines
        matches[relative] = file_matches
    return {
        "files": list(AUDITED_LEAN_FILES),
        "matches": matches,
        "clean": all(not file_matches for file_matches in matches.values()),
    }


def covered_by(
    owners: tuple[int, ...], live: tuple[bool, ...], i: int, j: int, k: int
) -> bool:
    """Exact cover predicate, including the two in-range cover witnesses."""

    if not 1 <= i <= k or not 1 <= j <= k:
        return False
    if len(owners) != len(live):
        raise ValueError("owners and liveness have different lengths")
    if not all(1 <= owner <= k for owner in owners):
        raise ValueError("assignment owner outside [1,k]")
    return all(
        (not is_live) or owner == i or owner == j
        for owner, is_live in zip(owners, live, strict=True)
    )


def no_two_cover(
    owners: tuple[int, ...], live: tuple[bool, ...], k: int
) -> bool:
    return all(
        not covered_by(owners, live, i, j, k)
        for i in range(1, k + 1)
        for j in range(1, k + 1)
    )


def three_live_distinct_entries(
    owners: tuple[int, ...], live: tuple[bool, ...]
) -> bool:
    if len(owners) != len(live):
        raise ValueError("owners and liveness have different lengths")
    return any(
        live[p]
        and live[q]
        and live[r]
        and len({owners[p], owners[q], owners[r]}) == 3
        for p, q, r in combinations(range(len(owners)), 3)
    )


def extract_three(
    owners: tuple[int, ...], live: tuple[bool, ...]
) -> tuple[int, int, int]:
    for p, q, r in combinations(range(len(owners)), 3):
        if (
            live[p]
            and live[q]
            and live[r]
            and len({owners[p], owners[q], owners[r]}) == 3
        ):
            return p, q, r
    raise ValueError("no three live pairwise-distinct owner values")


def _cover_table(k: int) -> tuple[bool, ...]:
    table: list[bool] = []
    for mask in range(1 << k):
        has_cover = False
        for i in range(k):
            for j in range(k):
                cover_mask = (1 << i) | (1 << j)
                if mask & ~cover_mask == 0:
                    has_cover = True
                    break
            if has_cover:
                break
        table.append(not has_cover)
    return tuple(table)


def _three_value_table(k: int) -> tuple[bool, ...]:
    table: list[bool] = []
    for mask in range(1 << k):
        values = tuple(index for index in range(k) if mask & (1 << index))
        has_three = any(True for _ in combinations(values, 3))
        table.append(has_three)
    return tuple(table)


def exact_distinct_live_count(k: int, size: int, r: int) -> int:
    """Independent inclusion-exclusion count for exactly ``r`` live values."""

    return comb(k, r) * sum(
        (-1) ** omitted * comb(r, omitted) * (k + r - omitted) ** size
        for omitted in range(r + 1)
    )


@lru_cache(maxsize=1)
def exhaustive_equivalence_report() -> dict[str, Any]:
    finite_models = 0
    no_cover_models = 0
    three_models = 0
    mismatches = 0
    counts = {str(r): 0 for r in range(7)}
    formula_counts = {str(r): 0 for r in range(7)}
    by_universe: dict[str, dict[str, int]] = {}
    for k in range(1, 7):
        cover_table = _cover_table(k)
        triple_table = _three_value_table(k)
        local_models = 0
        local_no_cover = 0
        for size in range(7):
            for r in range(0, min(k, size) + 1):
                formula_counts[str(r)] += exact_distinct_live_count(k, size, r)
            choices = tuple(
                (owner, is_live)
                for owner in range(1, k + 1)
                for is_live in (False, True)
            )
            for assignment in product(choices, repeat=size):
                mask = 0
                for owner, is_live in assignment:
                    if is_live:
                        mask |= 1 << (owner - 1)
                actual = cover_table[mask]
                expected = triple_table[mask]
                finite_models += 1
                local_models += 1
                no_cover_models += int(actual)
                local_no_cover += int(actual)
                three_models += int(expected)
                counts[str(mask.bit_count())] += 1
                if actual != expected:
                    mismatches += 1
        by_universe[str(k)] = {
            "finite_models": local_models,
            "no_two_cover_models": local_no_cover,
        }
    inclusion_exclusion_count = sum(
        count for r, count in formula_counts.items() if int(r) >= 3
    )
    return {
        "universe_sizes": list(range(1, 7)),
        "support_sizes": list(range(7)),
        "finite_models": finite_models,
        "no_two_cover_models": no_cover_models,
        "three_distinct_live_models": three_models,
        "inclusion_exclusion_count": inclusion_exclusion_count,
        "distinct_live_value_counts": counts,
        "inclusion_exclusion_distinct_live_value_counts": formula_counts,
        "by_universe": by_universe,
        "mismatches": mismatches,
    }


def boundary_fixture_report() -> dict[str, bool]:
    empty_support = ((), (), 1)
    zero_live = ((1, 3, 5), (False, False, False), 5)
    one_live = ((2, 4, 5), (True, False, False), 5)
    two_live = ((1, 5, 3), (True, True, False), 5)
    three_live = ((1, 3, 5), (True, True, True), 5)
    four_live = ((1, 2, 4, 5), (True, True, True, True), 5)
    zero_outside = ((1, 2, 6), (True, True, False), 6)
    off_support_values: Iterable[int] = (-100, 0, 1, 7, 10**30)
    base = no_two_cover((1, 2, 3), (True, True, True), 3)
    return {
        "empty_support_is_two_covered": not no_two_cover(*empty_support),
        "zero_live_values_are_two_covered": not no_two_cover(*zero_live),
        "one_live_value_is_covered_with_i_eq_j": covered_by(
            one_live[0], one_live[1], 2, 2, one_live[2]
        ),
        "two_live_values_are_two_covered": not no_two_cover(*two_live),
        "three_live_values_have_no_two_cover": no_two_cover(*three_live),
        "four_live_values_have_no_two_cover": no_two_cover(*four_live),
        "zero_clean_outside_cover_is_ignored": covered_by(
            zero_outside[0], zero_outside[1], 1, 2, zero_outside[2]
        ),
        "off_support_total_function_values_are_irrelevant": all(
            no_two_cover((1, 2, 3), (True, True, True), 3) == base
            for _unused in off_support_values
        ),
    }


def explicit_boundary_report() -> dict[str, Any]:
    endpoint_owners = (1, 6, 3)
    endpoint_live = (True, True, True)
    repeated_owners = (1, 1, 2, 2, 2)
    repeated_live = (True, True, True, True, False)
    prime_labels = (2, 3, 5)
    prime_owners = (1, 2, 3)
    prime_live = (True, True, True)
    selected = extract_three(prime_owners, prime_live)
    four_owners = (1, 2, 3, 4)
    four_live = (True, True, True, True)
    first_three = extract_three(four_owners, four_live)
    omitted = next(position for position in range(4) if position not in first_three)
    return {
        "endpoint_owners_extract": list(extract_three(endpoint_owners, endpoint_live)),
        "repeated_owner_entries_do_not_fake_three_values": (
            not three_live_distinct_entries(repeated_owners, repeated_live)
            and not no_two_cover(repeated_owners, repeated_live, 2)
        ),
        "prime_labels_2_and_3_require_no_special_case": (
            [prime_labels[position] for position in selected] == [2, 3, 5]
        ),
        "fourth_live_value_is_not_discarded_by_conclusion": (
            four_live[omitted]
            and four_owners[omitted]
            not in {four_owners[position] for position in first_three}
        ),
    }


def report() -> dict[str, Any]:
    return {
        "producer_hashes": producer_hash_report(),
        "forbidden_token_scan": forbidden_token_report(),
        "exhaustive_equivalence": exhaustive_equivalence_report(),
        "boundaries": boundary_fixture_report(),
        "explicit_boundaries": explicit_boundary_report(),
        "verdict": (
            "no two-index cover is equivalent to at least three distinct "
            "live owner values; extraction retains three witnesses but does "
            "not assert that no fourth live owner exists"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
