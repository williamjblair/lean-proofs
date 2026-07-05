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


def consecutive_kernel_holds(n1: int, n2: int, bound: int, t: int) -> bool:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or t < 0:
        raise ValueError("bound and t must be nonnegative")
    return (
        2 * t <= bound
        and (t * (t - 1)) % n1 == 0
        and (t * (t - 1) * (t - 2)) % n2 == 0
    )


def kernel_survivors_bruteforce(n1: int, n2: int, bound: int) -> list[int]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return [
        t
        for t in range(bound // 2 + 1)
        if consecutive_kernel_holds(n1, n2, bound, t)
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


def scan_kernel_crt(n1: int, n2: int, bound: int) -> dict[str, Any]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    classes, modulus = _row_one_residue_classes(n1)
    row_one_candidates: list[int] = []
    survivors: list[int] = []
    limit = bound // 2
    for residue in classes:
        t = residue
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
        "row_one_modulus": modulus,
        "row_one_class_count": len(classes),
        "row_one_candidate_count": len(row_one_candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact CRT scanner for the Erdős #699 consecutive-divisor kernel."
    )
    parser.add_argument("--n1", type=int, required=True)
    parser.add_argument("--n2", type=int, required=True)
    parser.add_argument("--bound", type=int, required=True)
    args = parser.parse_args(argv)
    print(json.dumps(scan_kernel_crt(args.n1, args.n2, args.bound), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
