from __future__ import annotations

from math import comb


def primes_upto(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= limit:
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
        p += 1
    return [p for p in range(2, limit + 1) if sieve[p]]


def digit(k: int, p: int, level: int) -> int:
    if p < 2:
        raise ValueError("base p must be at least 2")
    if k < 0 or level < 0:
        raise ValueError("k and level must be nonnegative")
    return (k // (p**level)) % p


def dominated(k: int, n: int, p: int) -> bool:
    if p < 2:
        raise ValueError("base p must be at least 2")
    if k < 0 or n < 0:
        raise ValueError("k and n must be nonnegative")
    m = max(k, n)
    level = 0
    while p**level <= m:
        if digit(k, p, level) > digit(n, p, level):
            return False
        level += 1
    return True


def binom_mod_prime_nonzero_by_lucas(n: int, k: int, p: int) -> bool:
    if not (0 <= k <= n):
        return False
    return comb(n, k) % p != 0


def criterion_obstruction_primes(n: int, i: int, j: int) -> list[int]:
    if not (1 <= i < j <= n // 2):
        return []
    return [
        p
        for p in primes_upto(n)
        if p >= i and not (dominated(i, n, p) or dominated(j, n, p))
    ]


def counterexample_candidate(n: int, i: int, j: int) -> bool:
    if not (1 <= i < j <= n // 2):
        return False
    return criterion_obstruction_primes(n, i, j) == []
