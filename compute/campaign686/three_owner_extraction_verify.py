#!/usr/bin/env python3
"""Exact finite models for the three-cleaned-owner extraction interface."""

from __future__ import annotations

import argparse
import json
from itertools import product
from typing import Any


ROWS = (5, 7, 9, 11, 13, 15)


def covered_by(owner: tuple[int, ...], clean: tuple[bool, ...], i: int, j: int) -> bool:
    return all(not live or value == i or value == j for value, live in zip(owner, clean))


def no_two_cover(owner: tuple[int, ...], clean: tuple[bool, ...], k: int) -> bool:
    return all(not covered_by(owner, clean, i, j) for i in range(1, k + 1) for j in range(1, k + 1))


def extract_three(owner: tuple[int, ...], clean: tuple[bool, ...]) -> tuple[int, int, int]:
    selected: list[int] = []
    seen: set[int] = set()
    for position, (value, live) in enumerate(zip(owner, clean)):
        if live and value not in seen:
            selected.append(position)
            seen.add(value)
            if len(selected) == 3:
                return selected[0], selected[1], selected[2]
    raise ValueError("fewer than three nonzero owner values")


def report() -> dict[str, Any]:
    fixtures = 0
    no_cover_fixtures = 0
    extracted = 0
    zero_clean_outside_two_cover = 0
    boundary_counts = {"zero": 0, "one": 0, "two": 0, "three_or_more": 0}
    for k in ROWS:
        alphabet = tuple(range(1, min(k, 4) + 1))
        for size in range(6):
            for owner in product(alphabet, repeat=size):
                for clean in product((False, True), repeat=size):
                    fixtures += 1
                    values = {value for value, live in zip(owner, clean) if live}
                    if len(values) == 0:
                        boundary_counts["zero"] += 1
                    elif len(values) == 1:
                        boundary_counts["one"] += 1
                    elif len(values) == 2:
                        boundary_counts["two"] += 1
                    else:
                        boundary_counts["three_or_more"] += 1
                    expected = len(values) >= 3
                    actual = no_two_cover(owner, clean, k)
                    if actual != expected:
                        raise AssertionError((k, owner, clean, values, actual))
                    if actual:
                        no_cover_fixtures += 1
                        p, q, r = extract_three(owner, clean)
                        if not (clean[p] and clean[q] and clean[r]):
                            raise AssertionError("extracted a zero-clean component")
                        if len({owner[p], owner[q], owner[r]}) != 3:
                            raise AssertionError("extracted owners are not distinct")
                        extracted += 1
                    for i in alphabet:
                        for j in alphabet:
                            for position, live in enumerate(clean):
                                if not live and owner[position] not in (i, j):
                                    if covered_by(owner, clean, i, j):
                                        zero_clean_outside_two_cover += 1
                                        break
    return {
        "rows": list(ROWS),
        "finite_models": fixtures,
        "no_two_cover_models": no_cover_fixtures,
        "successful_three_owner_extractions": extracted,
        "boundary_counts": boundary_counts,
        "zero_clean_outside_cover_occurrences": zero_clean_outside_two_cover,
        "equivalence": "no two-index cover iff at least three live owner values",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
