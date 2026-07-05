from __future__ import annotations

import argparse
import json
import math
from typing import Any


_MR_BASES_64 = (
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    325,
    9375,
    28178,
    450775,
    9780504,
    1795265022,
)


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    for base in _MR_BASES_64:
        a = base % n
        if a == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def _pollard_rho_factor(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    c = 1
    while True:
        x = 2
        y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
        c += 1


def _collect_prime_factors(n: int, factors: list[int]) -> None:
    if n == 1:
        return
    if _is_prime(n):
        factors.append(n)
        return
    factor = _pollard_rho_factor(n)
    _collect_prime_factors(factor, factors)
    _collect_prime_factors(n // factor, factors)


def prime_power_factorization(n: int) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("n must be positive")
    if n >= 2**64:
        raise ValueError("prime_power_factorization currently requires n < 2^64")
    prime_factors: list[int] = []
    _collect_prime_factors(n, prime_factors)
    prime_factors.sort()
    factors: list[tuple[int, int]] = []
    i = 0
    while i < len(prime_factors):
        p = prime_factors[i]
        power = 1
        while i < len(prime_factors) and prime_factors[i] == p:
            power *= p
            i += 1
        factors.append((p, power))
    return factors


def _crt_pair_coprime(residue: int, modulus: int, target: int, factor: int) -> int:
    step = ((target - residue) % factor) * pow(modulus, -1, factor) % factor
    return residue + modulus * step


def _first_representative_at_least(residue: int, modulus: int, lower: int) -> int:
    if residue >= lower:
        return residue
    return residue + ((lower - residue + modulus - 1) // modulus) * modulus


def consecutive_kernel_holds(
    n1: int, n2: int, bound: int, t: int, min_t: int = 0
) -> bool:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or t < 0 or min_t < 0:
        raise ValueError("bound, t, and min_t must be nonnegative")
    return (
        min_t <= t
        and 2 * t <= bound
        and (t * (t - 1)) % n1 == 0
        and (t * (t - 1) * (t - 2)) % n2 == 0
    )


def squeezed_normalized_case_i_kernel_holds(F: int, X: int, t: int, g: int) -> bool:
    if F < 0 or X < 0 or t < 0 or g < 0:
        raise ValueError("F, X, t, and g must be nonnegative")
    if F == 0 or X == 0 or t == 0:
        return False
    if F % 2 == 0 or X % 4 != 0 or F < 3:
        return False
    if 2 * t >= X or 4 * F > X or 2 * (F * F) > X:
        return False
    n = F * X
    return (
        t * (X - t) == g * (n - 1)
        and (g * (X - 2 * t)) % (n // 2 - 1) == 0
    )


def scan_squeezed_normalized_case_i_kernel(
    max_f: int,
    max_x: int,
    include_candidates: bool = False,
) -> dict[str, Any]:
    if max_f < 0 or max_x < 0:
        raise ValueError("max_f and max_x must be nonnegative")
    candidates: list[dict[str, int]] = []
    survivors: list[dict[str, int]] = []
    for F in range(3, max_f + 1, 2):
        min_x = max(4 * F, 2 * F * F)
        first_x = ((min_x + 3) // 4) * 4
        for X in range(first_x, max_x + 1, 4):
            n = F * X
            n1 = n - 1
            for t in range(1, (X - 1) // 2 + 1):
                row_one_product = t * (X - t)
                g, remainder = divmod(row_one_product, n1)
                if remainder != 0:
                    continue
                candidate = {"F": F, "X": X, "t": t, "g": g}
                candidates.append(candidate)
                if squeezed_normalized_case_i_kernel_holds(F, X, t, g):
                    survivors.append(candidate)
    result: dict[str, Any] = {
        "mode": "squeezed_normalized_case_i_kernel",
        "algorithm": "bounded_row_one_factor_scan",
        "max_f": max_f,
        "max_x": max_x,
        "candidate_count": len(candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }
    if include_candidates:
        result["candidates"] = candidates
    return result


def kernel_survivors_bruteforce(
    n1: int, n2: int, bound: int, min_t: int = 0
) -> list[int]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or min_t < 0:
        raise ValueError("bound and min_t must be nonnegative")
    return [
        t
        for t in range(min_t, bound // 2 + 1)
        if consecutive_kernel_holds(n1, n2, bound, t, min_t=min_t)
    ]


def _row_one_residue_classes(n1: int) -> tuple[list[int], int]:
    classes = [0]
    modulus = 1
    for _p, prime_power in prime_power_factorization(n1):
        next_classes: list[int] = []
        for residue in classes:
            next_classes.append(_crt_pair_coprime(residue, modulus, 0, prime_power))
            next_classes.append(_crt_pair_coprime(residue, modulus, 1, prime_power))
        modulus *= prime_power
        classes = sorted(set(value % modulus for value in next_classes))
    return classes, modulus


def _product(values: list[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def _row_one_split_diagnostic(
    factors: list[tuple[int, int]], n1: int, n2: int, t: int
) -> dict[str, Any]:
    zero_prime_powers: list[int] = []
    one_prime_powers: list[int] = []
    for _p, prime_power in factors:
        if t % prime_power == 0:
            zero_prime_powers.append(prime_power)
        elif (t - 1) % prime_power == 0:
            one_prime_powers.append(prime_power)
        else:
            raise ValueError("t is not a row-one CRT candidate")
    row_one_product = t * (t - 1)
    if row_one_product % n1 != 0:
        raise ValueError("t is not a row-one CRT candidate")
    row_one_quotient = row_one_product // n1
    row_one_quotient_gcd = math.gcd(row_one_quotient, n2)
    gap_gcd = math.gcd(t - 2, n2)
    quotient_gap_gcd_product = row_one_quotient_gcd * gap_gcd
    row_two_product = t * (t - 1) * (t - 2)
    row_two_remainder = row_two_product % n2
    return {
        "t": t,
        "zero_prime_powers": zero_prime_powers,
        "one_prime_powers": one_prime_powers,
        "zero_product": _product(zero_prime_powers),
        "one_product": _product(one_prime_powers),
        "row_one_quotient": row_one_quotient,
        "row_one_quotient_gcd": row_one_quotient_gcd,
        "gap_gcd": gap_gcd,
        "quotient_gap_gcd_product": quotient_gap_gcd_product,
        "quotient_gap_gcd_product_lt_n2": quotient_gap_gcd_product < n2,
        "row_two_remainder": row_two_remainder,
        "row_two_gcd": math.gcd(row_two_product, n2),
        "survives_row_two": row_two_remainder == 0,
    }


def _row_one_split_summary(splits: list[dict[str, Any]]) -> dict[str, Any]:
    gcd_counts: dict[int, int] = {}
    surviving_split_count = 0
    for split in splits:
        row_two_gcd = split["row_two_gcd"]
        gcd_counts[row_two_gcd] = gcd_counts.get(row_two_gcd, 0) + 1
        if split["survives_row_two"]:
            surviving_split_count += 1
    candidate_count = len(splits)
    return {
        "candidate_count": candidate_count,
        "surviving_split_count": surviving_split_count,
        "failed_split_count": candidate_count - surviving_split_count,
        "row_two_gcd_histogram": [
            {"row_two_gcd": row_two_gcd, "count": gcd_counts[row_two_gcd]}
            for row_two_gcd in sorted(gcd_counts)
        ],
    }


def _merge_row_one_split_summaries(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    gcd_counts: dict[int, int] = {}
    candidate_count = 0
    surviving_split_count = 0
    failed_split_count = 0
    for summary in summaries:
        candidate_count += summary["candidate_count"]
        surviving_split_count += summary["surviving_split_count"]
        failed_split_count += summary["failed_split_count"]
        for row in summary["row_two_gcd_histogram"]:
            row_two_gcd = row["row_two_gcd"]
            gcd_counts[row_two_gcd] = gcd_counts.get(row_two_gcd, 0) + row["count"]
    return {
        "candidate_count": candidate_count,
        "surviving_split_count": surviving_split_count,
        "failed_split_count": failed_split_count,
        "row_two_gcd_histogram": [
            {"row_two_gcd": row_two_gcd, "count": gcd_counts[row_two_gcd]}
            for row_two_gcd in sorted(gcd_counts)
        ],
    }


def scan_kernel_crt(
    n1: int,
    n2: int,
    bound: int,
    min_t: int = 0,
    include_row_one_candidates: bool = False,
    include_row_one_splits: bool = False,
    include_row_one_split_summary: bool = False,
) -> dict[str, Any]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or min_t < 0:
        raise ValueError("bound and min_t must be nonnegative")
    classes, modulus = _row_one_residue_classes(n1)
    row_one_candidates: list[int] = []
    survivors: list[int] = []
    limit = bound // 2
    for residue in classes:
        t = _first_representative_at_least(residue, modulus, min_t)
        while t <= limit:
            if (t * (t - 1)) % n1 == 0:
                row_one_candidates.append(t)
                if (t * (t - 1) * (t - 2)) % n2 == 0:
                    survivors.append(t)
            t += modulus
    row_one_candidates = sorted(set(row_one_candidates))
    survivors = sorted(set(survivors))
    result: dict[str, Any] = {
        "mode": "kernel_crt",
        "algorithm": "row_one_prime_power_crt",
        "n1": n1,
        "n2": n2,
        "bound": bound,
        "min_t": min_t,
        "row_one_modulus": modulus,
        "row_one_class_count": len(classes),
        "row_one_candidate_count": len(row_one_candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }
    if include_row_one_candidates:
        result["row_one_candidates"] = row_one_candidates
    if include_row_one_splits or include_row_one_split_summary:
        factors = prime_power_factorization(n1)
        row_one_candidate_splits = [
            _row_one_split_diagnostic(factors, n1, n2, t)
            for t in row_one_candidates
        ]
        if include_row_one_splits:
            result["row_one_candidate_splits"] = row_one_candidate_splits
        if include_row_one_split_summary:
            result["row_one_split_summary"] = _row_one_split_summary(
                row_one_candidate_splits
            )
    return result


def scan_case_i_power_two_kernel(
    max_exponent: int,
    min_exponent: int = 2,
    min_t: int = 4,
    include_row_one_candidates: bool = False,
    include_row_one_splits: bool = False,
    include_row_one_split_summary: bool = False,
) -> dict[str, Any]:
    if min_exponent < 0 or max_exponent < min_exponent:
        raise ValueError("require 0 <= min_exponent <= max_exponent")
    if min_t < 0:
        raise ValueError("min_t must be nonnegative")
    instances: list[dict[str, Any]] = []
    for exponent in range(min_exponent, max_exponent + 1):
        n = 3 * (2**exponent)
        scan = scan_kernel_crt(
            n - 1,
            n // 2 - 1,
            n,
            min_t=min_t,
            include_row_one_candidates=include_row_one_candidates,
            include_row_one_splits=include_row_one_splits,
            include_row_one_split_summary=include_row_one_split_summary,
        )
        instances.append({"exponent": exponent, "n": n, **scan})
    result: dict[str, Any] = {
        "mode": "case_i_power_two_kernel",
        "algorithm": "case_i_power_two_kernel_crt",
        "min_exponent": min_exponent,
        "max_exponent": max_exponent,
        "min_t": min_t,
        "instance_count": len(instances),
        "total_row_one_candidate_count": sum(
            item["row_one_candidate_count"] for item in instances
        ),
        "survivor_count": sum(item["survivor_count"] for item in instances),
        "instances": instances,
    }
    if include_row_one_split_summary:
        result["row_one_split_summary"] = _merge_row_one_split_summaries(
            [item["row_one_split_summary"] for item in instances]
        )
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact CRT scanner for the Erdős #699 consecutive-divisor kernel."
    )
    parser.add_argument("--n1", type=int)
    parser.add_argument("--n2", type=int)
    parser.add_argument("--bound", type=int)
    parser.add_argument("--min-t", type=int)
    parser.add_argument("--case-i-power-two", action="store_true")
    parser.add_argument("--squeezed-normalized-case-i", action="store_true")
    parser.add_argument("--max-f", type=int)
    parser.add_argument("--max-x", type=int)
    parser.add_argument("--min-exponent", type=int, default=2)
    parser.add_argument("--max-exponent", type=int)
    parser.add_argument("--include-candidates", action="store_true")
    parser.add_argument("--include-row-one-candidates", action="store_true")
    parser.add_argument("--include-row-one-splits", action="store_true")
    parser.add_argument("--include-row-one-split-summary", action="store_true")
    args = parser.parse_args(argv)
    if args.case_i_power_two:
        if args.max_exponent is None:
            parser.error("--case-i-power-two requires --max-exponent")
        min_t = 4 if args.min_t is None else args.min_t
        result = scan_case_i_power_two_kernel(
            args.max_exponent,
            min_exponent=args.min_exponent,
            min_t=min_t,
            include_row_one_candidates=args.include_row_one_candidates,
            include_row_one_splits=args.include_row_one_splits,
            include_row_one_split_summary=args.include_row_one_split_summary,
        )
    elif args.squeezed_normalized_case_i:
        if args.max_f is None or args.max_x is None:
            parser.error("--squeezed-normalized-case-i requires --max-f and --max-x")
        result = scan_squeezed_normalized_case_i_kernel(
            args.max_f,
            args.max_x,
            include_candidates=args.include_candidates,
        )
    else:
        if args.n1 is None or args.n2 is None or args.bound is None:
            parser.error("scalar scan requires --n1, --n2, and --bound")
        min_t = 0 if args.min_t is None else args.min_t
        result = scan_kernel_crt(
            args.n1,
            args.n2,
            args.bound,
            min_t=min_t,
            include_row_one_candidates=args.include_row_one_candidates,
            include_row_one_splits=args.include_row_one_splits,
            include_row_one_split_summary=args.include_row_one_split_summary,
        )
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
