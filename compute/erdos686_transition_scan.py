#!/usr/bin/env python3
"""Exact checks for the Erdos 686 N=4 transition-denominator obstruction.

The relevant Lean bridge proves that, once row `j` divides,

    transitionDenom k n d j ∣ skeletonQuotient k n d j

is equivalent to row `j+1` divisibility.  This script preserves the exact
integer evidence around the remaining boundary target:

* bounded scans over ratio-window triples;
* exact diagnostics for a supplied `(k,n,d)`.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import gcd, isqrt, prod


@dataclass(frozen=True)
class RatioWindow:
    dmin: int
    dmax: int


@dataclass(frozen=True)
class TransitionDiagnostic:
    j: int
    row_divides: bool
    next_row_divides: bool | None
    denom: int | None
    quotient_mod_denom: int | None
    denom_factors: list[tuple[int, int]] | None
    quotient_factors: list[tuple[int, int]] | None


def ratio_d_range(k: int, n: int) -> RatioWindow:
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
    return RatioWindow(dmin, left)


def shifted_diff_product(k: int, d: int, j: int) -> int:
    """Compute `shiftedDiffProductAt k d j` exactly."""
    return prod(d + i - j for i in range(1, k + 1))


def shifted_diff_product_mod(k: int, d: int, j: int, modulus: int) -> int:
    """Compute `shiftedDiffProductAt k d j mod modulus` exactly."""
    value = 1 % modulus
    for i in range(1, k + 1):
        value = (value * ((d + i - j) % modulus)) % modulus
    return value


def row_divides(k: int, n: int, d: int, j: int) -> bool:
    """Check whether `n+j ∣ shiftedDiffProductAt k d j`."""
    modulus = n + j
    return shifted_diff_product_mod(k, d, j, modulus) == 0


def skeleton_quotient(k: int, n: int, d: int, j: int) -> int:
    """Compute the exact row quotient, assuming row `j` divides."""
    numerator = shifted_diff_product(k, d, j)
    divisor = n + j
    quotient, remainder = divmod(numerator, divisor)
    if remainder != 0:
        raise ValueError(f"row {j} does not divide for {(k, n, d)}")
    return quotient


def transition_denom(k: int, n: int, d: int, j: int) -> int:
    """Compute the Lean `transitionDenom k n d j` exactly."""
    a = (n + j + 1) * (d + k - j)
    b = (n + j) * (d - j)
    return a // gcd(a, b)


def factor(n: int) -> list[tuple[int, int]]:
    """Return the prime factorization of a positive integer."""
    out: list[tuple[int, int]] = []
    exponent = 0
    while n % 2 == 0:
        n //= 2
        exponent += 1
    if exponent:
        out.append((2, exponent))
    p = 3
    root = isqrt(n)
    while p <= root:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            out.append((p, exponent))
            root = isqrt(n)
        p += 2
    if n > 1:
        out.append((n, 1))
    return out


def transition_diagnostic(
    k: int, n: int, d: int, j: int, with_factorization: bool
) -> TransitionDiagnostic:
    """Return exact row and transition data for one index."""
    current = row_divides(k, n, d, j)
    next_row = row_divides(k, n, d, j + 1) if j + 1 <= k else None
    if not current:
        return TransitionDiagnostic(j, False, next_row, None, None, None, None)

    denom = transition_denom(k, n, d, j)
    quotient = skeleton_quotient(k, n, d, j)
    denom_factors = factor(denom) if with_factorization else None
    quotient_factors = factor(quotient) if with_factorization else None
    return TransitionDiagnostic(
        j=j,
        row_divides=True,
        next_row_divides=next_row,
        denom=denom,
        quotient_mod_denom=quotient % denom,
        denom_factors=denom_factors,
        quotient_factors=quotient_factors,
    )


def first_failed_row(k: int, n: int, d: int, row_prefix: int) -> int | None:
    """Return the first failed row among `1..min(row_prefix,k)`, if any."""
    for j in range(1, min(row_prefix, k) + 1):
        if not row_divides(k, n, d, j):
            return j
    return None


def first_transition_escape(
    k: int, n: int, d: int, transition_prefix: int
) -> int | None:
    """Return the first transition denominator that does not divide."""
    for j in range(1, min(transition_prefix, k - 1) + 1):
        if not row_divides(k, n, d, j):
            raise ValueError(f"row {j} does not divide for {(k, n, d)}")
        denom = transition_denom(k, n, d, j)
        quotient = skeleton_quotient(k, n, d, j)
        if quotient % denom != 0:
            return j
    return None


def scan(
    kmin: int,
    kmax: int,
    nmin: int,
    nmax: int,
    row_prefix: int,
    transition_prefix: int,
    examples: int,
    expect_rows: int | None,
    expect_escapes: int | None,
    expect_counterexamples: int | None,
) -> None:
    """Scan exact ratio-window triples for row-prefix and transition behavior."""
    total_window = 0
    rows_survive = 0
    transition_escapes = 0
    transition_counterexamples = 0
    first_rows: list[tuple[int, int, int]] = []
    first_escapes: list[tuple[int, int, int, int]] = []
    first_counterexamples: list[tuple[int, int, int]] = []

    for k in range(kmin, kmax + 1):
        local_total = 0
        local_rows = 0
        local_escapes = 0
        local_counterexamples = 0
        for n in range(nmin, nmax + 1):
            window = ratio_d_range(k, n)
            dmin = max(window.dmin, k)
            dmax = window.dmax
            if dmin > dmax:
                continue
            local_total += dmax - dmin + 1
            total_window += dmax - dmin + 1

            for d in range(dmin, dmax + 1):
                if first_failed_row(k, n, d, row_prefix) is not None:
                    continue
                rows_survive += 1
                local_rows += 1
                if len(first_rows) < examples:
                    first_rows.append((k, n, d))

                escape = first_transition_escape(k, n, d, transition_prefix)
                if escape is None:
                    transition_counterexamples += 1
                    local_counterexamples += 1
                    if len(first_counterexamples) < examples:
                        first_counterexamples.append((k, n, d))
                else:
                    transition_escapes += 1
                    local_escapes += 1
                    if len(first_escapes) < examples:
                        first_escapes.append((k, n, d, escape))

        print(
            f"k={k} nrange={nmin}..{nmax} total_window={local_total} "
            f"rows{row_prefix}={local_rows} "
            f"transition_escapes={local_escapes} "
            f"transition_counterexamples={local_counterexamples}"
        )

    print(
        f"ALL k={kmin}..{kmax} nrange={nmin}..{nmax} "
        f"total_window={total_window} rows{row_prefix}={rows_survive} "
        f"transition_escapes={transition_escapes} "
        f"transition_counterexamples={transition_counterexamples}"
    )
    for item in first_rows:
        print(f"  first-rows{row_prefix} k={item[0]} n={item[1]} d={item[2]}")
    for k, n, d, j in first_escapes:
        print(f"  first-transition-escape k={k} n={n} d={d} j={j}")
    for item in first_counterexamples:
        print(f"  first-transition-counterexample k={item[0]} n={item[1]} d={item[2]}")

    if expect_rows is not None and rows_survive != expect_rows:
        raise SystemExit(f"expected rows{row_prefix}={expect_rows}, got {rows_survive}")
    if expect_escapes is not None and transition_escapes != expect_escapes:
        raise SystemExit(
            f"expected transition_escapes={expect_escapes}, got {transition_escapes}"
        )
    if (
        expect_counterexamples is not None
        and transition_counterexamples != expect_counterexamples
    ):
        raise SystemExit(
            "expected transition_counterexamples="
            f"{expect_counterexamples}, got {transition_counterexamples}"
        )


def check_triple(
    k: int, n: int, d: int, row_prefix: int, transition_prefix: int
) -> None:
    """Print exact diagnostics for one ratio-window triple."""
    window = ratio_d_range(k, n)
    in_window = k <= d and window.dmin <= d <= window.dmax
    print(
        f"triple={(k, n, d)} ratio_window=[{window.dmin},{window.dmax}] "
        f"in_window={in_window}"
    )
    failed = first_failed_row(k, n, d, row_prefix)
    print(f"rows1..{min(row_prefix, k)} first_failed_row={failed}")
    escape = None
    if failed is None:
        escape = first_transition_escape(k, n, d, transition_prefix)
    print(f"transitions1..{min(transition_prefix, k - 1)} first_escape={escape}")

    for j in range(1, min(transition_prefix, k - 1) + 1):
        diagnostic = transition_diagnostic(k, n, d, j, with_factorization=(j == escape))
        print(
            f"  j={j} row={diagnostic.row_divides} "
            f"next_row={diagnostic.next_row_divides} "
            f"denom={diagnostic.denom} "
            f"quotient_mod_denom={diagnostic.quotient_mod_denom}"
        )
        if diagnostic.denom_factors is not None:
            print(f"    denom_factors={diagnostic.denom_factors}")
        if diagnostic.quotient_factors is not None:
            print(f"    quotient_factors={diagnostic.quotient_factors}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kmin", type=int, default=5)
    parser.add_argument("--kmax", type=int, default=20)
    parser.add_argument("--nmin", type=int, default=0)
    parser.add_argument("--nmax", type=int, default=10_000)
    parser.add_argument("--row-prefix", type=int, default=15)
    parser.add_argument("--transition-prefix", type=int, default=15)
    parser.add_argument("--examples", type=int, default=5)
    parser.add_argument("--expect-rows", type=int)
    parser.add_argument("--expect-escapes", type=int)
    parser.add_argument("--expect-counterexamples", type=int)
    parser.add_argument("--triple", nargs=3, type=int, metavar=("K", "N", "D"))
    args = parser.parse_args()

    if args.triple is not None:
        check_triple(
            args.triple[0],
            args.triple[1],
            args.triple[2],
            args.row_prefix,
            args.transition_prefix,
        )
        return

    scan(
        args.kmin,
        args.kmax,
        args.nmin,
        args.nmax,
        args.row_prefix,
        args.transition_prefix,
        args.examples,
        args.expect_rows,
        args.expect_escapes,
        args.expect_counterexamples,
    )


if __name__ == "__main__":
    main()
