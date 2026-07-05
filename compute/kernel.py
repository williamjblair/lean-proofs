from __future__ import annotations

import argparse
import json
import math
from typing import Any

from compute.erdos699 import criterion_obstruction_primes, primes_upto


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


def squeezed_candidate_original_row_three_obstructions(
    F: int, X: int, t: int, prime_limit: int
) -> list[int]:
    if F < 0 or X < 0 or t < 0 or prime_limit < 0:
        raise ValueError("F, X, t, and prime_limit must be nonnegative")
    n = F * X
    j = F * t
    return criterion_obstruction_primes(n, 3, j, primes=primes_upto(prime_limit))


def _squeezed_candidate_diagnostic(
    candidate: dict[str, int],
    original_obstruction_prime_limit: int | None = None,
) -> dict[str, Any]:
    F = candidate["F"]
    X = candidate["X"]
    t = candidate["t"]
    g = candidate["g"]
    half_row = F * X // 2 - 1
    gap = X - 2 * t
    half_row_value = g * gap
    half_row_remainder = half_row_value % half_row
    diagnostic = {
        **candidate,
        "half_row": half_row,
        "gap": gap,
        "half_row_value": half_row_value,
        "half_row_remainder": half_row_remainder,
        "half_row_gcd": math.gcd(half_row_value, half_row),
        "survives_half_row": half_row_remainder == 0,
    }
    if original_obstruction_prime_limit is not None:
        obstructions = squeezed_candidate_original_row_three_obstructions(
            F, X, t, original_obstruction_prime_limit
        )
        diagnostic.update(
            {
                "original_n": F * X,
                "original_j": F * t,
                "original_obstruction_prime_limit": original_obstruction_prime_limit,
                "original_row_three_obstruction_primes": obstructions,
                "original_row_three_has_obstruction": bool(obstructions),
            }
        )
    return diagnostic


def _squeezed_candidate_summary(
    candidate_diagnostics: list[dict[str, Any]],
) -> dict[str, Any]:
    gcd_counts: dict[int, int] = {}
    first_obstruction_counts: dict[int, int] = {}
    surviving_half_row_count = 0
    original_obstruction_prime_limit: int | None = None
    with_original_obstruction_count = 0
    for candidate in candidate_diagnostics:
        half_row_gcd = candidate["half_row_gcd"]
        gcd_counts[half_row_gcd] = gcd_counts.get(half_row_gcd, 0) + 1
        if candidate["survives_half_row"]:
            surviving_half_row_count += 1
        if "original_row_three_obstruction_primes" in candidate:
            original_obstruction_prime_limit = candidate["original_obstruction_prime_limit"]
            obstructions = candidate["original_row_three_obstruction_primes"]
            if obstructions:
                with_original_obstruction_count += 1
                first = obstructions[0]
                first_obstruction_counts[first] = first_obstruction_counts.get(first, 0) + 1
    candidate_count = len(candidate_diagnostics)
    summary = {
        "candidate_count": candidate_count,
        "surviving_half_row_count": surviving_half_row_count,
        "failed_half_row_count": candidate_count - surviving_half_row_count,
        "half_row_gcd_histogram": [
            {"half_row_gcd": half_row_gcd, "count": gcd_counts[half_row_gcd]}
            for half_row_gcd in sorted(gcd_counts)
        ],
    }
    if original_obstruction_prime_limit is not None:
        original_obstruction_summary = {
            "prime_limit": original_obstruction_prime_limit,
            "candidate_count": candidate_count,
            "with_obstruction_count": with_original_obstruction_count,
            "without_obstruction_count": candidate_count - with_original_obstruction_count,
            "first_obstruction_prime_histogram": [
                {"prime": prime, "count": first_obstruction_counts[prime]}
                for prime in sorted(first_obstruction_counts)
            ],
        }
        summary["original_row_three_obstruction_summary"] = original_obstruction_summary
    return summary


def squeezed_row_one_candidates_discriminant(F: int, X: int) -> list[dict[str, int]]:
    if F < 0 or X < 0:
        raise ValueError("F and X must be nonnegative")
    if F == 0 or X == 0:
        return []
    if F % 2 == 0 or F < 3 or X % 4 != 0:
        return []
    if 4 * F > X or 2 * (F * F) > X:
        return []
    n1 = F * X - 1
    max_g = (X * X - 1) // (4 * n1)
    candidates: list[dict[str, int]] = []
    for g in range(1, max_g + 1):
        discriminant = X * X - 4 * g * n1
        gap = math.isqrt(discriminant)
        if gap == 0 or gap * gap != discriminant:
            continue
        if (X - gap) % 2 != 0:
            continue
        t = (X - gap) // 2
        if t == 0 or 2 * t >= X:
            continue
        if t * (X - t) != g * n1:
            continue
        candidates.append({"F": F, "X": X, "t": t, "g": g})
    return sorted(candidates, key=lambda item: (item["t"], item["g"]))


def scan_squeezed_normalized_case_i_kernel(
    max_f: int,
    max_x: int,
    include_candidates: bool = False,
    include_candidate_diagnostics: bool = False,
    include_candidate_summary: bool = False,
    original_obstruction_prime_limit: int | None = None,
) -> dict[str, Any]:
    if max_f < 0 or max_x < 0:
        raise ValueError("max_f and max_x must be nonnegative")
    if original_obstruction_prime_limit is not None and original_obstruction_prime_limit < 0:
        raise ValueError("original_obstruction_prime_limit must be nonnegative")
    candidates: list[dict[str, int]] = []
    survivors: list[dict[str, int]] = []
    for F in range(3, max_f + 1, 2):
        min_x = max(4 * F, 2 * F * F)
        first_x = ((min_x + 3) // 4) * 4
        for X in range(first_x, max_x + 1, 4):
            for candidate in squeezed_row_one_candidates_discriminant(F, X):
                candidates.append(candidate)
                t = candidate["t"]
                g = candidate["g"]
                if squeezed_normalized_case_i_kernel_holds(F, X, t, g):
                    survivors.append(candidate)
    result: dict[str, Any] = {
        "mode": "squeezed_normalized_case_i_kernel",
        "algorithm": "bounded_discriminant_scan",
        "max_f": max_f,
        "max_x": max_x,
        "candidate_count": len(candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }
    if include_candidates:
        result["candidates"] = candidates
    if include_candidate_diagnostics or include_candidate_summary:
        candidate_diagnostics = [
            _squeezed_candidate_diagnostic(candidate, original_obstruction_prime_limit)
            for candidate in candidates
        ]
        if include_candidate_diagnostics:
            result["candidate_diagnostics"] = candidate_diagnostics
        if include_candidate_summary:
            result["candidate_summary"] = _squeezed_candidate_summary(
                candidate_diagnostics
            )
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


def _relative_product_is_larger(
    candidate: dict[str, int], current: dict[str, int]
) -> bool:
    candidate_product = candidate["quotient_gap_gcd_product"]
    current_product = current["quotient_gap_gcd_product"]
    left = candidate_product * current["n2"]
    right = current_product * candidate["n2"]
    return left > right


def _quotient_gap_summary(
    splits: list[dict[str, Any]], n2: int
) -> dict[str, Any]:
    product_counts: dict[int, int] = {}
    strict_lt_n2_count = 0
    max_quotient_gap_gcd_product = 0
    max_relative_product: dict[str, int] | None = None
    for split in splits:
        product = split["quotient_gap_gcd_product"]
        product_counts[product] = product_counts.get(product, 0) + 1
        if product < n2:
            strict_lt_n2_count += 1
        if product > max_quotient_gap_gcd_product:
            max_quotient_gap_gcd_product = product
        relative_product = {
            "t": split["t"],
            "n2": n2,
            "quotient_gap_gcd_product": product,
        }
        if max_relative_product is None or _relative_product_is_larger(
            relative_product, max_relative_product
        ):
            max_relative_product = relative_product
    candidate_count = len(splits)
    non_strict_lt_n2_count = candidate_count - strict_lt_n2_count
    return {
        "candidate_count": candidate_count,
        "strict_lt_n2_count": strict_lt_n2_count,
        "non_strict_lt_n2_count": non_strict_lt_n2_count,
        "all_strict_lt_n2": non_strict_lt_n2_count == 0,
        "max_quotient_gap_gcd_product": max_quotient_gap_gcd_product,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": product, "count": product_counts[product]}
            for product in sorted(product_counts)
        ],
        "max_relative_product": max_relative_product,
    }


def _add_quotient_gap_summary_context(
    summary: dict[str, Any], context: dict[str, int]
) -> dict[str, Any]:
    max_relative_product = summary["max_relative_product"]
    if max_relative_product is None:
        return dict(summary)
    return {
        **summary,
        "max_relative_product": {**context, **max_relative_product},
    }


def _merge_quotient_gap_summaries(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    product_counts: dict[int, int] = {}
    candidate_count = 0
    strict_lt_n2_count = 0
    non_strict_lt_n2_count = 0
    max_quotient_gap_gcd_product = 0
    max_relative_product: dict[str, int] | None = None
    for summary in summaries:
        candidate_count += summary["candidate_count"]
        strict_lt_n2_count += summary["strict_lt_n2_count"]
        non_strict_lt_n2_count += summary["non_strict_lt_n2_count"]
        max_quotient_gap_gcd_product = max(
            max_quotient_gap_gcd_product,
            summary["max_quotient_gap_gcd_product"],
        )
        for row in summary["quotient_gap_gcd_product_histogram"]:
            product = row["quotient_gap_gcd_product"]
            product_counts[product] = product_counts.get(product, 0) + row["count"]
        candidate_relative_product = summary["max_relative_product"]
        if candidate_relative_product is None:
            continue
        if max_relative_product is None or _relative_product_is_larger(
            candidate_relative_product, max_relative_product
        ):
            max_relative_product = candidate_relative_product
    return {
        "candidate_count": candidate_count,
        "strict_lt_n2_count": strict_lt_n2_count,
        "non_strict_lt_n2_count": non_strict_lt_n2_count,
        "all_strict_lt_n2": non_strict_lt_n2_count == 0,
        "max_quotient_gap_gcd_product": max_quotient_gap_gcd_product,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": product, "count": product_counts[product]}
            for product in sorted(product_counts)
        ],
        "max_relative_product": max_relative_product,
    }


def scan_kernel_crt(
    n1: int,
    n2: int,
    bound: int,
    min_t: int = 0,
    include_row_one_candidates: bool = False,
    include_row_one_splits: bool = False,
    include_row_one_split_summary: bool = False,
    include_quotient_gap_summary: bool = False,
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
    if (
        include_row_one_splits
        or include_row_one_split_summary
        or include_quotient_gap_summary
    ):
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
        if include_quotient_gap_summary:
            result["quotient_gap_summary"] = _quotient_gap_summary(
                row_one_candidate_splits, n2
            )
    return result


def scan_case_i_power_two_kernel(
    max_exponent: int,
    min_exponent: int = 2,
    min_t: int = 4,
    include_row_one_candidates: bool = False,
    include_row_one_splits: bool = False,
    include_row_one_split_summary: bool = False,
    include_quotient_gap_summary: bool = False,
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
            include_quotient_gap_summary=include_quotient_gap_summary,
        )
        if include_quotient_gap_summary:
            scan["quotient_gap_summary"] = _add_quotient_gap_summary_context(
                scan["quotient_gap_summary"],
                {"exponent": exponent, "n": n},
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
    if include_quotient_gap_summary:
        result["quotient_gap_summary"] = _merge_quotient_gap_summaries(
            [item["quotient_gap_summary"] for item in instances]
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
    parser.add_argument("--include-candidate-diagnostics", action="store_true")
    parser.add_argument("--include-candidate-summary", action="store_true")
    parser.add_argument("--include-row-one-candidates", action="store_true")
    parser.add_argument("--include-row-one-splits", action="store_true")
    parser.add_argument("--include-row-one-split-summary", action="store_true")
    parser.add_argument("--include-quotient-gap-summary", action="store_true")
    parser.add_argument("--original-obstruction-prime-limit", type=int)
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
            include_quotient_gap_summary=args.include_quotient_gap_summary,
        )
    elif args.squeezed_normalized_case_i:
        if args.max_f is None or args.max_x is None:
            parser.error("--squeezed-normalized-case-i requires --max-f and --max-x")
        result = scan_squeezed_normalized_case_i_kernel(
            args.max_f,
            args.max_x,
            include_candidates=args.include_candidates,
            include_candidate_diagnostics=args.include_candidate_diagnostics,
            include_candidate_summary=args.include_candidate_summary,
            original_obstruction_prime_limit=args.original_obstruction_prime_limit,
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
            include_quotient_gap_summary=args.include_quotient_gap_summary,
        )
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
