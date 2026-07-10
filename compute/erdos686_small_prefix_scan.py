#!/usr/bin/env python3
"""Exact bounded scan for the Erdos 686 N=4 polynomial-prefix target.

The scan checks ratio-window triples `(k,n,d)` and records the first failed
congruence among `a = 0,...,prefix`.  It uses integer arithmetic only.
"""

from __future__ import annotations

import argparse
from math import prod


def ratio_d_range(k: int, n: int) -> tuple[int, int]:
    """Return the exact inclusive d-window forced by the N=4 ratio bounds."""
    hi = max(1, 2 * n + 10 * k + 10)
    while (n + hi + 1) ** k < 4 * (n + 1) ** k:
        hi *= 2

    left = 0
    right = hi
    while left < right:
        mid = (left + right) // 2
        if (n + mid + 1) ** k >= 4 * (n + 1) ** k:
            right = mid
        else:
            left = mid + 1
    dmin = left

    hi = max(dmin, 1)
    while (n + hi + k) ** k <= 4 * (n + k) ** k:
        hi *= 2

    left = dmin
    right = hi
    while left + 1 < right:
        mid = (left + right) // 2
        if (n + mid + k) ** k <= 4 * (n + k) ** k:
            left = mid
        else:
            right = mid
    return dmin, left


def h_mod(k: int, d: int, a: int, modulus: int) -> int:
    """Compute H_{k,d}(a) modulo a positive modulus."""
    upper = 1 % modulus
    lower = 1 % modulus
    for i in range(1, k + 1):
        upper = (upper * ((d - a + i) % modulus)) % modulus
        lower = (lower * ((i - a) % modulus)) % modulus
    return (upper - 4 * lower) % modulus


def h_exact(k: int, d: int, a: int) -> int:
    """Compute H_{k,d}(a) exactly."""
    upper = prod(d - a + i for i in range(1, k + 1))
    lower = prod(i - a for i in range(1, k + 1))
    return upper - 4 * lower


def first_failed_prefix(k: int, n: int, d: int, prefix: int) -> int:
    """Return first failing a, or prefix+1 if every congruence passes."""
    for a in range(prefix + 1):
        modulus = n + a
        if modulus == 0:
            ok = h_exact(k, d, a) == 0
        else:
            ok = h_mod(k, d, a, modulus) == 0
        if not ok:
            return a
    return prefix + 1


def scan(kmin: int, kmax: int, nmax: int, prefix: int, examples: int) -> None:
    buckets = [0 for _ in range(prefix + 2)]
    first: list[list[tuple[int, int, int]]] = [[] for _ in range(prefix + 2)]
    total = 0

    for k in range(kmin, kmax + 1):
        local_buckets = [0 for _ in range(prefix + 2)]
        local_first: list[list[tuple[int, int, int]]] = [
            [] for _ in range(prefix + 2)
        ]
        local_total = 0
        for n in range(nmax + 1):
            dmin, dmax = ratio_d_range(k, n)
            dmin = max(dmin, k)
            if dmin > dmax:
                continue
            for d in range(dmin, dmax + 1):
                failed = first_failed_prefix(k, n, d, prefix)
                total += 1
                local_total += 1
                buckets[failed] += 1
                local_buckets[failed] += 1
                if len(first[failed]) < examples:
                    first[failed].append((k, n, d))
                if len(local_first[failed]) < examples:
                    local_first[failed].append((k, n, d))

        print(f"k={k} nmax={nmax} prefix={prefix} total={local_total}")
        print(f"  buckets={local_buckets}")
        print(f"  first={local_first}")

    print(f"ALL k={kmin}..{kmax} nmax={nmax} prefix={prefix} total={total}")
    print(f"  buckets={buckets}")
    print(f"  first={first}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kmin", type=int, default=5)
    parser.add_argument("--kmax", type=int, default=7)
    parser.add_argument("--nmax", type=int, default=1_000_000)
    parser.add_argument("--prefix", type=int, default=8)
    parser.add_argument("--examples", type=int, default=8)
    args = parser.parse_args()
    scan(args.kmin, args.kmax, args.nmax, args.prefix, args.examples)


if __name__ == "__main__":
    main()
