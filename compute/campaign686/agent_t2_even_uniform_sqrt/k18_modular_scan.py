#!/usr/bin/env python3
"""Exact finite-field audit of the k=18 trapped-center candidates."""

from __future__ import annotations

from hashlib import sha256

import numpy as np

from even_uniform_sqrt_verify import eval_poly, make_data


TRAP = 731_939_653
CANDIDATES = (TRAP - 1) // 81
ROW = make_data(18)


def primes_through(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (((n - p * p) // p) + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def values_mod(p: int) -> tuple[list[int], list[int]]:
    s = [int(eval_poly(ROW.s_poly, x)) % p for x in range(p)]
    t = [int(eval_poly(ROW.t_poly, x)) % p for x in range(p)]
    return s, t


def allowed_t_residues(p: int) -> tuple[np.ndarray, int]:
    """Allowed t mod p for m=-81t on S(w)=4S(v)."""
    assert p not in (2, 3)
    s, t = values_mod(p)
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s):
        buckets.setdefault(value, []).append(w)
    m_residues: set[int] = set()
    for v in range(p):
        for w in buckets.get(4 * s[v] % p, ()):
            m_residues.add((t[w] - 2 * t[v]) % p)
    allowed = np.zeros(p, dtype=np.bool_)
    inv = pow((-81) % p, -1, p)
    allowed[np.fromiter((r * inv % p for r in m_residues), dtype=np.int64)] = True
    return allowed, len(m_residues)


def find_pair(t_candidate: int, p: int) -> tuple[int, int] | None:
    """Find one exact (w,v) mod p for m=-81*t_candidate."""
    if p == 2:
        # Both integer centers are odd.
        w = v = 1
        if (eval_poly(ROW.s_poly, w) - 4 * eval_poly(ROW.s_poly, v)) % p == 0 and (
            eval_poly(ROW.t_poly, w) - 2 * eval_poly(ROW.t_poly, v) + 81 * t_candidate
        ) % p == 0:
            return w, v
        return None
    if p == 3:
        # 81 annihilates the target; direct search is tiny.
        pass
    s, t = values_mod(p)
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s):
        buckets.setdefault(value, []).append(w)
    target = (-81 * t_candidate) % p
    for v in range(p):
        for w in buckets.get(4 * s[v] % p, ()):
            if (t[w] - 2 * t[v]) % p == target:
                return w, v
    return None


def audit() -> tuple[list[int], str]:
    # Apply every prime-field obstruction through 1000 to all 9,036,292
    # possible nonzero multiples in the rigorous trap.
    survivors = np.arange(1, CANDIDATES + 1, dtype=np.int64)
    for p in primes_through(1000):
        if p in (2, 3):
            continue
        allowed, _ = allowed_t_residues(p)
        survivors = survivors[allowed[survivors % p]]
    result = survivors.tolist()
    assert result == [2_990_977, 3_541_067]

    # Both remaining candidates have an explicit local point for every prime
    # through 5000.  CRT therefore preserves them against any product of
    # distinct primes in this tested set.
    digest = sha256()
    for p in primes_through(5000):
        for candidate in result:
            pair = find_pair(candidate, p)
            assert pair is not None
            digest.update(f"{p}:{candidate}:{pair[0]}:{pair[1]}\n".encode())
    return result, digest.hexdigest()


def main() -> None:
    survivors, digest = audit()
    print("trap", -TRAP, "< m < 0")
    print("m=-81*t candidates", CANDIDATES)
    print("survivors after every prime p<=1000", survivors)
    print("corresponding m", [-81 * t for t in survivors])
    print("both survive every prime p<=5000; witness digest", digest)


if __name__ == "__main__":
    main()
