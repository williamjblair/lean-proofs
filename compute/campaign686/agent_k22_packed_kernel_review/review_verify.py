#!/usr/bin/env python3
"""Exact independent checks for the original k=22 packed-kernel probe."""

from __future__ import annotations

import ast
from math import gcd, prod
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROBE = HERE.parent / "agent_k22_packed_kernel" / "ActualShardProbe.lean"
WIDTH = 20_000_000
EXPONENT = 18
P23_MASK = 2_228_292


def s_polynomial(value: int) -> int:
    """S(W) = product over the eleven signed odd-root pairs."""
    return prod(value * value - (2 * j - 1) ** 2 for j in range(1, 12))


def t_polynomial(value: int) -> int:
    """The exact integral polynomial part 256*sqrt(S)."""
    return (
        256 * value**11
        - 226_688 * value**9
        + 67_609_696 * value**7
        - 8_111_362_160 * value**5
        + 352_497_378_310 * value**3
        - 6_055_670_906_453 * value
    )


def independently_enumerated_p23_residues() -> frozenset[int]:
    """Enumerate all local (w,v) pairs modulo 23 without importing a verifier."""
    inverse = pow(-33, -1, 23)
    residues: set[int] = set()
    for v in range(23):
        for w in range(23):
            if (s_polynomial(w) - 4 * s_polynomial(v)) % 23 == 0:
                m = (t_polynomial(w) - 2 * t_polynomial(v)) % 23
                residues.add((m * inverse) % 23)
    return frozenset(residues)


def local_allowed_t_residues(modulus: int) -> frozenset[int]:
    """Independently reconstruct one unrestricted local t-mask."""
    assert gcd(modulus, 33) == 1
    s_values = [s_polynomial(x) % modulus for x in range(modulus)]
    t_values = [t_polynomial(x) % modulus for x in range(modulus)]
    s_buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s_values):
        s_buckets.setdefault(value, []).append(w)
    m_values: set[int] = set()
    for v in range(modulus):
        for w in s_buckets.get(4 * s_values[v] % modulus, ()):
            m_values.add((t_values[w] - 2 * t_values[v]) % modulus)
    inverse = pow(-33, -1, modulus)
    return frozenset((m * inverse) % modulus for m in m_values)


def primes_through(limit: int) -> tuple[int, ...]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
    return tuple(primes)


def independently_generated_branch_items(branch: int) -> tuple[tuple[int, int], ...]:
    """Rebuild every active q-mask without importing the original generator."""
    items: list[tuple[int, int]] = []
    for prime in primes_through(953):
        if prime in (2, 3, 11, 23):
            continue
        allowed = local_allowed_t_residues(prime)
        if len(allowed) == prime:
            continue
        inverse = pow(46, -1, prime)
        q_residues = {
            ((allowed_residue - branch) * inverse) % prime
            for allowed_residue in allowed
        }
        items.append((prime, sum(1 << residue for residue in q_residues)))
    return tuple(items)


def odd_p23_classes_mod46() -> tuple[int, ...]:
    allowed = independently_enumerated_p23_residues()
    return tuple(a for a in range(46) if a % 2 == 1 and a % 23 in allowed)


def parse_actual_items() -> tuple[tuple[int, int], ...]:
    source = PROBE.read_text()
    body = source.split("def actualShardItems", 1)[1]
    body = body.split(":= [", 1)[1].split("\n]\n", 1)[0]
    parsed = ast.literal_eval("[" + body + "]")
    return tuple((int(period), int(pattern)) for period, pattern in parsed)


def periodic_pow_mask(width: int, period: int, pattern: int, exponent: int) -> int:
    """Mirror the Lean balanced-doubling definition with exact Python integers."""
    cap = (1 << width) - 1
    previous = pattern & cap
    shift = period
    for _ in range(exponent):
        previous = (previous | (previous << shift)) & cap
        shift *= 2
    return previous


def exact_intersection_audit() -> dict[str, object]:
    items = parse_actual_items()
    expected_items = independently_generated_branch_items(17)
    acc = (1 << WIDTH) - 1
    first_zero_prime: int | None = None
    for period, pattern in items:
        acc &= periodic_pow_mask(WIDTH, period, pattern, EXPONENT)
        if acc == 0:
            first_zero_prime = period
            break
    return {
        "item_count": len(items),
        "unique_period_count": len({period for period, _ in items}),
        "minimum_period": min(period for period, _ in items),
        "minimum_extent": min(period * 2**EXPONENT for period, _ in items),
        "patterns_fit_one_period": all(
            pattern < 2**period for period, pattern in items
        ),
        "inventory_matches_independent_reconstruction": items == expected_items,
        "first_zero_prime": first_zero_prime,
        "intersection_is_zero": acc == 0,
    }


def audit() -> dict[str, object]:
    p23_residues = independently_enumerated_p23_residues()
    return {
        "p23_residues": sorted(p23_residues),
        "p23_mask": sum(1 << residue for residue in p23_residues),
        "odd_classes_mod46": list(odd_p23_classes_mod46()),
        "packed_intersection": exact_intersection_audit(),
    }


if __name__ == "__main__":
    print(audit())
