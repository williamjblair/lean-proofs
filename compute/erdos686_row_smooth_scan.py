#!/usr/bin/env python3
"""Exact scan for the Erdos 686 N=4 row-prefix capped-smooth obstruction.

For each ratio-window triple `(k,n,d)`, this script checks whether the first
`prefix` lower terms can all satisfy the row-specific smoothness condition

    every prime p | n+j has p <= d+k-j.

The scan is exact.  It uses a sieve for largest prime factors up to
`nmax + prefix`, then reduces the smoothness condition to one lower bound on
`d` for each `(k,n)`.
"""

from __future__ import annotations

import argparse


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


def largest_prime_factors(limit: int) -> list[int]:
    """Return `lpf[x]`, the largest prime factor of x; `lpf[0]=lpf[1]=1`."""
    lpf = [1] * (limit + 1)
    for p in range(2, limit + 1):
        if lpf[p] == 1:
            for multiple in range(p, limit + 1, p):
                lpf[multiple] = p
    return lpf


def smooth_lower_bound_for_d(k: int, n: int, prefix: int, lpf: list[int]) -> int:
    """Smallest d that can satisfy all row-prefix smoothness inequalities."""
    lower = 0
    for j in range(1, prefix + 1):
        needed = lpf[n + j] - k + j
        if needed > lower:
            lower = needed
    return lower


def row_product_mod(k: int, n: int, d: int, j: int) -> int:
    """Return `shiftedDiffProductAt k d j mod (n+j)`."""
    modulus = n + j
    value = 1 % modulus
    for i in range(1, k + 1):
        value = (value * ((d + i - j) % modulus)) % modulus
    return value


def first_failed_row(k: int, n: int, d: int, prefix: int) -> int | None:
    """Return the first failed row divisibility, or None if all prefix rows pass."""
    for j in range(1, min(prefix, k) + 1):
        if row_product_mod(k, n, d, j) != 0:
            return j
    return None


def scan(
    kmin: int,
    kmax: int,
    nmax: int,
    prefix: int,
    examples: int,
    check_rows: bool,
    failure_examples: int,
    expect_row_survivors: int | None,
    expect_max_failure_row: int | None,
) -> None:
    lpf = largest_prime_factors(nmax + prefix)
    total = 0
    survivors = 0
    row_survivors = 0
    row_failure_buckets = [0 for _ in range(prefix + 2)]
    first: list[tuple[int, int, int, int, int, list[int]]] = []
    first_row: list[tuple[int, int, int]] = []
    first_by_failure: list[list[tuple[int, int, int, list[int], list[int]]]] = [
        [] for _ in range(prefix + 2)
    ]

    for k in range(kmin, kmax + 1):
        local_total = 0
        local_survivors = 0
        local_row_survivors = 0
        local_row_failure_buckets = [0 for _ in range(prefix + 2)]
        local_first: list[tuple[int, int, int, int, int, list[int]]] = []
        local_first_row: list[tuple[int, int, int]] = []
        local_first_by_failure: list[list[tuple[int, int, int, list[int], list[int]]]] = [
            [] for _ in range(prefix + 2)
        ]
        row_count = min(prefix, k)
        for n in range(nmax + 1):
            dmin, dmax = ratio_d_range(k, n)
            dmin = max(dmin, k)
            if dmin > dmax:
                continue
            local_total += dmax - dmin + 1
            total += dmax - dmin + 1

            dsmooth = smooth_lower_bound_for_d(k, n, row_count, lpf)
            d = max(dmin, dsmooth)
            if d <= dmax:
                local_survivors += dmax - d + 1
                survivors += dmax - d + 1
                for candidate_d in range(d, dmax + 1):
                    if len(local_first) < examples or len(first) < examples:
                        caps = [candidate_d + k - j for j in range(1, row_count + 1)]
                        lpfs = [lpf[n + j] for j in range(1, row_count + 1)]
                        item = (k, n, candidate_d, dmin, dmax, lpfs)
                        if len(local_first) < examples:
                            local_first.append(item)
                        if len(first) < examples:
                            first.append(item)
                        assert all(
                            lpfs[j - 1] <= caps[j - 1]
                            for j in range(1, row_count + 1)
                        )
                    if check_rows:
                        failed = first_failed_row(k, n, candidate_d, row_count)
                        bucket = row_count + 1 if failed is None else failed
                        local_row_failure_buckets[bucket] += 1
                        row_failure_buckets[bucket] += 1
                        if failed is None:
                            local_row_survivors += 1
                            row_survivors += 1
                            if len(local_first_row) < examples:
                                local_first_row.append((k, n, candidate_d))
                            if len(first_row) < examples:
                                first_row.append((k, n, candidate_d))
                        if len(local_first_by_failure[bucket]) < failure_examples or (
                            len(first_by_failure[bucket]) < failure_examples
                        ):
                            caps = [
                                candidate_d + k - j for j in range(1, row_count + 1)
                            ]
                            lpfs = [lpf[n + j] for j in range(1, row_count + 1)]
                            item2 = (k, n, candidate_d, lpfs, caps)
                            if len(local_first_by_failure[bucket]) < failure_examples:
                                local_first_by_failure[bucket].append(item2)
                            if len(first_by_failure[bucket]) < failure_examples:
                                first_by_failure[bucket].append(item2)

        print(
            f"k={k} nmax={nmax} prefix={prefix} "
            f"total={local_total} smooth_survivors={local_survivors}"
        )
        if check_rows:
            print(
                f"  row_survivors={local_row_survivors} "
                f"row_failure_buckets={local_row_failure_buckets}"
            )
        for item in local_first:
            k0, n0, d0, dmin0, dmax0, lpfs0 = item
            print(
                f"  example k={k0} n={n0} d={d0} "
                f"d_window=[{dmin0},{dmax0}] lpfs={lpfs0}"
            )
        for k0, n0, d0 in local_first_row:
            print(f"  row-survivor k={k0} n={n0} d={d0}")
        if check_rows and failure_examples:
            for bucket, items in enumerate(local_first_by_failure):
                if not items:
                    continue
                label = "survive" if bucket == row_count + 1 else f"fail{bucket}"
                for k0, n0, d0, lpfs0, caps0 in items:
                    print(
                        f"  {label} example k={k0} n={n0} d={d0} "
                        f"lpfs={lpfs0} caps={caps0}"
                    )

    print(
        f"ALL k={kmin}..{kmax} nmax={nmax} prefix={prefix} "
        f"total={total} smooth_survivors={survivors}"
    )
    if check_rows:
        print(
            f"  row_survivors={row_survivors} "
            f"row_failure_buckets={row_failure_buckets}"
        )
    for item in first:
        k0, n0, d0, dmin0, dmax0, lpfs0 = item
        print(
            f"  first k={k0} n={n0} d={d0} "
            f"d_window=[{dmin0},{dmax0}] lpfs={lpfs0}"
        )
    for k0, n0, d0 in first_row:
        print(f"  first-row-survivor k={k0} n={n0} d={d0}")
    if check_rows and failure_examples:
        for bucket, items in enumerate(first_by_failure):
            if not items:
                continue
            label = "survive" if bucket == min(prefix, kmax) + 1 else f"fail{bucket}"
            for k0, n0, d0, lpfs0, caps0 in items:
                print(
                    f"  first-{label} k={k0} n={n0} d={d0} "
                    f"lpfs={lpfs0} caps={caps0}"
                )

    if check_rows and expect_row_survivors is not None:
        if row_survivors != expect_row_survivors:
            raise SystemExit(
                f"expected row_survivors={expect_row_survivors}, got {row_survivors}"
            )
    if check_rows and expect_max_failure_row is not None:
        for bucket, count in enumerate(row_failure_buckets):
            if count and bucket > expect_max_failure_row:
                raise SystemExit(
                    f"expected all row failures by {expect_max_failure_row}, "
                    f"but bucket {bucket} has {count}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kmin", type=int, default=5)
    parser.add_argument("--kmax", type=int, default=50)
    parser.add_argument("--nmax", type=int, default=100_000)
    parser.add_argument("--prefix", type=int, default=16)
    parser.add_argument("--examples", type=int, default=3)
    parser.add_argument("--check-rows", action="store_true")
    parser.add_argument("--failure-examples", type=int, default=0)
    parser.add_argument("--expect-row-survivors", type=int)
    parser.add_argument("--expect-max-failure-row", type=int)
    args = parser.parse_args()
    scan(
        args.kmin,
        args.kmax,
        args.nmax,
        args.prefix,
        args.examples,
        args.check_rows,
        args.failure_examples,
        args.expect_row_survivors,
        args.expect_max_failure_row,
    )


if __name__ == "__main__":
    main()
