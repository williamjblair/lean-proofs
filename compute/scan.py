from __future__ import annotations

import argparse
import json
from bisect import bisect_left, bisect_right
from collections.abc import Iterable
from typing import Any

from compute.erdos699 import counterexample_candidate, dominated, primes_upto


def _sorted_i_values(i_values: Iterable[int] | None) -> list[int] | None:
    if i_values is None:
        return None
    values = sorted(set(i_values))
    for i in values:
        if i < 1:
            raise ValueError("i values must be positive")
    return values


def scan_full_short_circuit(
    limit: int, i_values: Iterable[int] | None = None
) -> dict[str, Any]:
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    selected_i = _sorted_i_values(i_values)
    primes = primes_upto(limit)
    candidates: list[dict[str, int]] = []
    checked_triples = 0

    for n in range(1, limit + 1):
        half = n // 2
        if selected_i is None:
            row_i_values = range(1, half)
        else:
            row_i_values = (i for i in selected_i if i < half)
        for i in row_i_values:
            for j in range(i + 1, half + 1):
                checked_triples += 1
                if counterexample_candidate(n, i, j, primes=primes):
                    candidates.append({"n": n, "i": i, "j": j})

    return {
        "mode": "full",
        "algorithm": "short_circuit_obstruction",
        "limit": limit,
        "i_values": selected_i,
        "checked_triples": checked_triples,
        "candidate_count": len(candidates),
        "candidates": candidates,
    }


def _prime_masks_by_threshold(primes_for_n: list[int], half: int) -> list[int]:
    all_mask = (1 << len(primes_for_n)) - 1
    masks = [0] * (half + 1)
    for i in range(1, half + 1):
        first_relevant = bisect_left(primes_for_n, i)
        masks[i] = all_mask & ~((1 << first_relevant) - 1)
    return masks


def _failure_masks_for_n(n: int, half: int, primes_for_n: list[int]) -> list[int]:
    masks = [0] * (half + 1)
    for k in range(1, half + 1):
        mask = 0
        for bit, p in enumerate(primes_for_n):
            if not dominated(k, n, p):
                mask |= 1 << bit
        masks[k] = mask
    return masks


def scan_full(limit: int, i_values: Iterable[int] | None = None) -> dict[str, Any]:
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    selected_i = _sorted_i_values(i_values)
    primes = primes_upto(limit)
    candidates: list[dict[str, int]] = []
    checked_triples = 0

    for n in range(1, limit + 1):
        half = n // 2
        primes_for_n = primes[: bisect_right(primes, n)]
        relevant_masks = _prime_masks_by_threshold(primes_for_n, half)
        failure_masks = _failure_masks_for_n(n, half, primes_for_n)
        if selected_i is None:
            row_i_values = range(1, half)
        else:
            row_i_values = (i for i in selected_i if i < half)
        for i in row_i_values:
            bad_i_relevant = failure_masks[i] & relevant_masks[i]
            for j in range(i + 1, half + 1):
                checked_triples += 1
                if bad_i_relevant & failure_masks[j] == 0:
                    candidates.append({"n": n, "i": i, "j": j})

    return {
        "mode": "full",
        "algorithm": "bitset_domination",
        "limit": limit,
        "i_values": selected_i,
        "checked_triples": checked_triples,
        "candidate_count": len(candidates),
        "candidates": candidates,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact Erdős #699 Lucas-criterion full sweep."
    )
    parser.add_argument("--limit", type=int, required=True)
    parser.add_argument("--i", dest="i_values", type=int, action="append")
    args = parser.parse_args(argv)

    result = scan_full(args.limit, i_values=args.i_values)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
