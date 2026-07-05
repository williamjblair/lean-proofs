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


def _row_obstruction_primes(n: int, i: int, primes_for_n: list[int]) -> list[int]:
    return [p for p in primes_for_n if i <= p and not dominated(i, n, p)]


def _base_p_digits_through(n: int, p: int) -> list[int]:
    digits: list[int] = []
    place = 1
    while place <= n:
        digits.append((n // place) % p)
        place *= p
    return digits


def _merge_intervals(intervals: list[tuple[int, int]]) -> list[tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for start, stop in intervals[1:]:
        prev_start, prev_stop = merged[-1]
        if start <= prev_stop + 1:
            merged[-1] = (prev_start, max(prev_stop, stop))
        else:
            merged.append((start, stop))
    return merged


def _dominated_intervals(n: int, p: int, limit: int) -> list[tuple[int, int]]:
    digits = _base_p_digits_through(n, p)
    powers = [1]
    for _ in range(1, len(digits)):
        powers.append(powers[-1] * p)

    lower_unconstrained = [True]
    for digit_value in digits:
        lower_unconstrained.append(lower_unconstrained[-1] and digit_value == p - 1)

    intervals: list[tuple[int, int]] = []

    def visit(level: int, prefix: int) -> None:
        if level < 0:
            if prefix <= limit:
                intervals.append((prefix, prefix))
            return
        place = powers[level]
        for digit_value in range(digits[level] + 1):
            start = prefix + digit_value * place
            if limit < start:
                break
            if lower_unconstrained[level]:
                intervals.append((start, min(start + place - 1, limit)))
            else:
                visit(level - 1, start)

    visit(len(digits) - 1, 0)
    return _merge_intervals(intervals)


def _intersect_intervals(
    left: list[tuple[int, int]], right: list[tuple[int, int]]
) -> list[tuple[int, int]]:
    intersections: list[tuple[int, int]] = []
    i = 0
    j = 0
    while i < len(left) and j < len(right):
        left_start, left_stop = left[i]
        right_start, right_stop = right[j]
        start = max(left_start, right_start)
        stop = min(left_stop, right_stop)
        if start <= stop:
            intersections.append((start, stop))
        if left_stop < right_stop:
            i += 1
        else:
            j += 1
    return intersections


def scan_rows(limit: int, i_values: Iterable[int] | None) -> dict[str, Any]:
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    selected_i = _sorted_i_values(i_values)
    if not selected_i:
        raise ValueError("row scan requires at least one i value")
    primes = primes_upto(limit)
    candidates: list[dict[str, int]] = []
    checked_triples = 0

    for n in range(1, limit + 1):
        half = n // 2
        primes_for_n = primes[: bisect_right(primes, n)]
        for i in selected_i:
            if half <= i:
                continue
            obstruction_primes = _row_obstruction_primes(n, i, primes_for_n)
            checked_triples += half - i
            allowed_intervals = [(i + 1, half)]
            interval_cache: dict[int, list[tuple[int, int]]] = {}
            for p in obstruction_primes:
                if p not in interval_cache:
                    interval_cache[p] = _dominated_intervals(n, p, half)
                allowed_intervals = _intersect_intervals(
                    allowed_intervals, interval_cache[p]
                )
                if not allowed_intervals:
                    break
            for start, stop in allowed_intervals:
                for j in range(start, stop + 1):
                    candidates.append({"n": n, "i": i, "j": j})

    return {
        "mode": "rows",
        "algorithm": "row_obstruction_primes",
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
    parser.add_argument(
        "--row-scan",
        action="store_true",
        help="use the exact row-specialized scanner; requires at least one --i",
    )
    args = parser.parse_args(argv)

    if args.row_scan:
        if not args.i_values:
            parser.error("--row-scan requires at least one --i")
        result = scan_rows(args.limit, i_values=args.i_values)
    else:
        result = scan_full(args.limit, i_values=args.i_values)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
