#!/usr/bin/env python3
"""Deterministic greedy search for the certified k=28 prime-field cover."""

from __future__ import annotations

from even_k28_verify import (
    CANDIDATE_COUNT,
    FIXED,
    KERNEL_COVER,
    KERNEL_COVER_COUNTS,
    allowed_data,
)


def primes_through(limit: int) -> list[int]:
    primes = []
    for n in range(2, limit + 1):
        if all(n % p for p in primes if p * p <= n):
            primes.append(n)
    return primes


def greedy_cover(limit: int = 997) -> tuple[list[int], list[int]]:
    masks = {
        p: allowed_data(p)[0]
        for p in primes_through(limit)
        if p > 3 and FIXED % p
    }
    survivors = list(range(1, CANDIDATE_COUNT + 1))
    chosen = []
    counts = [len(survivors)]
    while survivors:
        choices = []
        for p, allowed in masks.items():
            if p in chosen:
                continue
            filtered = [t for t in survivors if t % p in allowed]
            choices.append((len(filtered), p, filtered))
        if not choices:
            break
        _, p, survivors = min(choices, key=lambda row: (row[0], row[1]))
        chosen.append(p)
        counts.append(len(survivors))
    return chosen, counts


if __name__ == "__main__":
    primes, counts = greedy_cover()
    print("unrestricted greedy primes", primes)
    print("unrestricted greedy counts", counts)
    print("kernel primes", KERNEL_COVER)
    print("kernel counts", KERNEL_COVER_COUNTS)
