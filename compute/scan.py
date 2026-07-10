from __future__ import annotations

import argparse
import json
import math
from bisect import bisect_left, bisect_right
from collections.abc import Iterable
from typing import Any

from compute.erdos699 import counterexample_candidate, dominated, primes_upto

DEFAULT_POWER_TWO_MULTIPLIERS = [1, 3, 5, 7, 9, 11, 13, 15, 21, 25]


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


def power_two_family_values(max_exponent: int, multipliers: Iterable[int]) -> list[int]:
    if max_exponent < 0:
        raise ValueError("max exponent must be nonnegative")
    selected_multipliers = sorted(set(multipliers))
    if not selected_multipliers:
        raise ValueError("at least one multiplier is required")
    for multiplier in selected_multipliers:
        if multiplier < 1:
            raise ValueError("multipliers must be positive")
    limit = 2**max_exponent
    values: set[int] = set()
    for multiplier in selected_multipliers:
        value = multiplier
        while value <= limit:
            values.add(value)
            value *= 2
    return sorted(values)


def _is_prime_by_trial(n: int) -> bool:
    if n < 2:
        return False
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            return False
    return True


def _prime_factors_from_primes(n: int, primes: list[int]) -> list[int]:
    factors: list[int] = []
    remaining = n
    for p in primes:
        if remaining < p * p:
            break
        if remaining % p == 0:
            factors.append(p)
            while remaining % p == 0:
                remaining //= p
    if 1 < remaining:
        factors.append(remaining)
    return factors


def _row_obstruction_primes_by_factorization(
    n: int, i: int, factor_primes: list[int]
) -> list[int]:
    obstructions: set[int] = set()
    if _is_prime_by_trial(i) and i <= n and not dominated(i, n, i):
        obstructions.add(i)
    for r in range(i):
        for p in _prime_factors_from_primes(n - r, factor_primes):
            if i < p <= n and not dominated(i, n, p):
                obstructions.add(p)
    return sorted(obstructions)


def _first_representative_greater_than(
    residue: int, modulus: int, lower: int
) -> int:
    if lower < residue:
        return residue
    return residue + ((lower - residue) // modulus + 1) * modulus


def _crt_pair_coprime(residue: int, modulus: int, target: int, prime: int) -> int:
    step = ((target - residue) % prime) * pow(modulus, -1, prime) % prime
    return residue + modulus * step


def _candidate_js_by_factor_crt(
    n: int, i: int, obstruction_primes: list[int]
) -> tuple[list[int], int]:
    half = n // 2
    states = [0]
    modulus = 1
    max_states = 1
    for p in sorted((p for p in obstruction_primes if i < p), reverse=True):
        next_modulus = modulus * p
        next_states: list[int] = []
        for residue in states:
            for target in range(n % p + 1):
                combined = _crt_pair_coprime(residue, modulus, target, p)
                if (
                    _first_representative_greater_than(combined, next_modulus, i)
                    <= half
                ):
                    next_states.append(combined)
        states = sorted(set(next_states))
        modulus = next_modulus
        max_states = max(max_states, len(states))
        if not states:
            break

    candidates: list[int] = []
    for residue in states:
        j = _first_representative_greater_than(residue, modulus, i)
        while j <= half:
            if all(dominated(j, n, p) for p in obstruction_primes):
                candidates.append(j)
            j += modulus
    return sorted(set(candidates)), max_states


def scan_n_values(n_values: Iterable[int], i_values: Iterable[int] | None) -> dict[str, Any]:
    selected_n_values = sorted(set(n_values))
    if not selected_n_values:
        raise ValueError("at least one n value is required")
    for n in selected_n_values:
        if n < 1:
            raise ValueError("n values must be positive")
    selected_i = _sorted_i_values(i_values)
    if not selected_i:
        raise ValueError("sparse scan requires at least one i value")

    factor_primes = primes_upto(math.isqrt(max(selected_n_values)) + 1)
    candidates: list[dict[str, int]] = []
    checked_triples = 0
    cells_checked = 0
    max_crt_states = 0

    for n in selected_n_values:
        half = n // 2
        for i in selected_i:
            if half <= i:
                continue
            cells_checked += 1
            checked_triples += half - i
            obstruction_primes = _row_obstruction_primes_by_factorization(
                n, i, factor_primes
            )
            row_candidates, row_max_states = _candidate_js_by_factor_crt(
                n, i, obstruction_primes
            )
            max_crt_states = max(max_crt_states, row_max_states)
            for j in row_candidates:
                candidates.append({"n": n, "i": i, "j": j})

    return {
        "mode": "n_values",
        "algorithm": "factor_crt_row_obstruction",
        "n_values": selected_n_values,
        "i_values": selected_i,
        "cells_checked": cells_checked,
        "checked_triples": checked_triples,
        "candidate_count": len(candidates),
        "candidates": candidates,
        "max_crt_states": max_crt_states,
    }


def scan_power_two_family(
    max_exponent: int,
    multipliers: Iterable[int],
    i_values: Iterable[int] | None,
) -> dict[str, Any]:
    selected_multipliers = sorted(set(multipliers))
    n_values = power_two_family_values(max_exponent, selected_multipliers)
    result = scan_n_values(n_values, i_values)
    result["mode"] = "power_two_family"
    result["max_exponent"] = max_exponent
    result["family_limit"] = 2**max_exponent
    result["multipliers"] = selected_multipliers
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact Erdős #699 Lucas-criterion full sweep."
    )
    parser.add_argument("--limit", type=int)
    parser.add_argument("--i", dest="i_values", type=int, action="append")
    parser.add_argument(
        "--row-scan",
        action="store_true",
        help="use the exact row-specialized scanner; requires at least one --i",
    )
    parser.add_argument(
        "--power-two-family",
        action="store_true",
        help="scan n = 2^A * M sparse families; requires at least one --i",
    )
    parser.add_argument("--family-max-exponent", type=int, default=36)
    parser.add_argument("--multiplier", dest="multipliers", type=int, action="append")
    args = parser.parse_args(argv)

    if args.power_two_family:
        if not args.i_values:
            parser.error("--power-two-family requires at least one --i")
        multipliers = args.multipliers or DEFAULT_POWER_TWO_MULTIPLIERS
        result = scan_power_two_family(
            args.family_max_exponent, multipliers, args.i_values
        )
    elif args.row_scan:
        if args.limit is None:
            parser.error("--limit is required unless --power-two-family is used")
        if not args.i_values:
            parser.error("--row-scan requires at least one --i")
        result = scan_rows(args.limit, i_values=args.i_values)
    else:
        if args.limit is None:
            parser.error("--limit is required unless --power-two-family is used")
        result = scan_full(args.limit, i_values=args.i_values)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
