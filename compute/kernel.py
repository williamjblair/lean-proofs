from __future__ import annotations

import argparse
import json
from typing import Any


def prime_power_factorization(n: int) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("n must be positive")
    factors: list[tuple[int, int]] = []
    remaining = n
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            power = 1
            while remaining % p == 0:
                power *= p
                remaining //= p
            factors.append((p, power))
        p = 3 if p == 2 else p + 2
    if remaining > 1:
        factors.append((remaining, remaining))
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


def scan_kernel_crt(n1: int, n2: int, bound: int, min_t: int = 0) -> dict[str, Any]:
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
    return {
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


def scan_case_i_power_two_kernel(
    max_exponent: int, min_exponent: int = 2, min_t: int = 4
) -> dict[str, Any]:
    if min_exponent < 0 or max_exponent < min_exponent:
        raise ValueError("require 0 <= min_exponent <= max_exponent")
    if min_t < 0:
        raise ValueError("min_t must be nonnegative")
    instances: list[dict[str, Any]] = []
    for exponent in range(min_exponent, max_exponent + 1):
        n = 3 * (2**exponent)
        scan = scan_kernel_crt(n - 1, n // 2 - 1, n, min_t=min_t)
        instances.append({"exponent": exponent, "n": n, **scan})
    return {
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact CRT scanner for the Erdős #699 consecutive-divisor kernel."
    )
    parser.add_argument("--n1", type=int)
    parser.add_argument("--n2", type=int)
    parser.add_argument("--bound", type=int)
    parser.add_argument("--min-t", type=int)
    parser.add_argument("--case-i-power-two", action="store_true")
    parser.add_argument("--min-exponent", type=int, default=2)
    parser.add_argument("--max-exponent", type=int)
    args = parser.parse_args(argv)
    if args.case_i_power_two:
        if args.max_exponent is None:
            parser.error("--case-i-power-two requires --max-exponent")
        min_t = 4 if args.min_t is None else args.min_t
        result = scan_case_i_power_two_kernel(
            args.max_exponent, min_exponent=args.min_exponent, min_t=min_t
        )
    else:
        if args.n1 is None or args.n2 is None or args.bound is None:
            parser.error("scalar scan requires --n1, --n2, and --bound")
        min_t = 0 if args.min_t is None else args.min_t
        result = scan_kernel_crt(args.n1, args.n2, args.bound, min_t=min_t)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
