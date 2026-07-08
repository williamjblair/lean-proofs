#!/usr/bin/env python3
"""Exact checks for refuted Erdos 686 polynomial-prefix targets."""

from __future__ import annotations

from math import isqrt, prod


TRIPLES = [
    # Refutes the proposed prefix-seven large-prime forcing theorem.
    (113, 30171, 373, 8),
    # Refutes polynomial_prefix_eight_escape_in_ratio_window.
    (167, 34235, 286, 9),
    # Shows prefix 9 is not enough.
    (184, 46759, 354, 10),
    # Shows prefix 14 is not enough; first failure at 15.
    (245, 48503, 276, 15),
]


def factor(n: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            out.append((p, exponent))
        p += 1 if p == 2 else 2
    if n > 1:
        out.append((n, 1))
    return out


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    root = isqrt(n)
    p = 3
    while p <= root:
        if n % p == 0:
            return False
        p += 2
    return True


def h_value(k: int, d: int, a: int) -> int:
    upper = prod(d - a + i for i in range(1, k + 1))
    lower = prod(i - a for i in range(1, k + 1))
    return upper - 4 * lower


def first_failure(k: int, n: int, d: int, prefix: int) -> int | None:
    for a in range(prefix + 1):
        if h_value(k, d, a) % (n + a) != 0:
            return a
    return None


def check_triple(k: int, n: int, d: int, prefix: int) -> None:
    assert k <= d
    assert (n + d + k) ** k <= 4 * (n + k) ** k
    assert 4 * (n + 1) ** k <= (n + d + 1) ** k
    failure = first_failure(k, n, d, prefix)
    print(f"triple={(k, n, d)} prefix={prefix} first_failure={failure}")
    for a in range(prefix + 1):
        modulus = n + a
        remainder = h_value(k, d, a) % modulus
        print(f"  a={a:2d} modulus={modulus} remainder={remainder}")
    cap = d + k - 8
    factors = factor(n + 8)
    assert all(is_prime(p) for p, _ in factors)
    print(f"  n+8={n + 8} factorization={factors} cap={cap}")
    print()


def main() -> None:
    for triple in TRIPLES:
        check_triple(*triple)


if __name__ == "__main__":
    main()
