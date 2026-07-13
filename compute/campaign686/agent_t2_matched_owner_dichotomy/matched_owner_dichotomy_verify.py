#!/usr/bin/env python3
"""Exact arithmetic checks for the supplied-owner matched residual dichotomy.

This script is an audit companion, not a proof oracle.  The corresponding
Lean module proves the uniform statements.  Every calculation here uses
Python integers or ``fractions.Fraction``; no floating point is used.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import factorial, gcd


def coefficient(k: int, t: int) -> int:
    assert 1 <= t <= k
    return factorial(t - 1) * factorial(k - t)


def signed_coefficient(k: int, t: int) -> int:
    return (-1) ** (t - 1) * coefficient(k, t)


def owner_slope(k: int, t: int) -> Fraction:
    assert 1 <= t <= k
    return sum(
        (Fraction(1, r - t) for r in range(1, k + 1) if r != t),
        Fraction(0),
    )


def second_linear(k: int, t: int) -> int:
    value = signed_coefficient(k, t) * owner_slope(k, t)
    assert value.denominator == 1
    return value.numerator


def normalization(k: int, i: int, j: int) -> tuple[int, int]:
    ci = coefficient(k, i)
    cj = coefficient(k, j)
    g = gcd(4 * ci, cj)
    return 4 * ci // g, cj // g


def quadratic_coefficient(k: int, i: int, j: int, A: int, B: int) -> int:
    return A * A * second_linear(k, j) - 4 * B * B * second_linear(k, i)


def block_product(k: int, n: int) -> int:
    out = 1
    for r in range(1, k + 1):
        out *= n + r
    return out


def factor_small(n: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def is_prime_u64(n: int) -> bool:
    """Deterministic Miller-Rabin for the 64-bit fixture range."""
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    if n in small:
        return True
    if any(n % p == 0 for p in small):
        return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def verify_uniform(max_k: int = 300) -> dict[str, int]:
    candidates = 0
    for k in range(16, max_k + 1):
        coeffs = [0] + [coefficient(k, t) for t in range(1, k + 1)]
        slopes = [Fraction(0)] + [owner_slope(k, t) for t in range(1, k + 1)]
        seconds = [0] + [signed_coefficient(k, t) * slopes[t] for t in range(1, k + 1)]
        assert all(value.denominator == 1 for value in seconds[1:])
        assert all(slopes[t + 1] < slopes[t] for t in range(1, k))
        for i in range(1, k + 1):
            ci = coeffs[i]
            for j in range(1, k + 1):
                # Signed normalized linear equality requires equal parity.
                if (i - j) % 2:
                    continue
                cj = coeffs[j]
                # B < A < 2B iff Cj < 4Ci < 2Cj.
                if not (cj < 4 * ci < 2 * cj):
                    continue
                A, B = normalization(k, i, j)
                assert 0 < B < A < 2 * B
                assert A * signed_coefficient(k, j) == 4 * B * signed_coefficient(k, i)
                c2 = A * A * seconds[j].numerator - 4 * B * B * seconds[i].numerator
                assert c2 != 0
                candidates += 1
    return {"max_k": max_k, "normalized_candidates": candidates}


def verify_fixtures() -> dict[str, object]:
    k22, n22, d22 = 22, 11_274_465_968_418, 733_303_549_440
    assert factor_small(d22) == {2: 9, 3: 12, 5: 1, 7: 2, 11: 1}
    assert block_product(k22, n22 + d22) != 4 * block_product(k22, n22)
    p22 = 230_091_142_213
    assert n22 + 19 == 49 * p22 and is_prime_u64(p22)
    assert all((n22 + d22 + j) % p22 for j in range(1, k22 + 1))
    zero_pairs: dict[str, dict[str, int]] = {}
    for i, j in ((9, 7), (14, 16)):
        A, B = normalization(k22, i, j)
        c2 = quadratic_coefficient(k22, i, j, A, B)
        assert (A, B) == (16, 15)
        assert c2 == 104_810_845_224_960_000
        assert (A - B) * abs(c2) + k22 - 1 == 104_810_845_224_960_021
        assert d22 < (A - B) * abs(c2) + k22 - 1
        zero_pairs[f"{i},{j}"] = {"A": A, "B": B, "c2": c2}

    k984, n984, d984 = 984, 3_177_026, 4_480
    assert n984 + 17 == 439 * 7_237
    assert is_prime_u64(439) and is_prime_u64(7_237)
    assert 7_237 > d984 + k984 - 1
    assert all((n984 + d984 + j) % 7_237 for j in range(1, k984 + 1))
    assert block_product(k984, n984 + d984) != 4 * block_product(k984, n984)

    # Genuine d=1 telescopes, including both mandatory odd rows.  All lie
    # outside d>=k; in general k=3(n+1) makes the endpoint ratio four.
    for kt, nt in ((6, 1), (9, 2), (15, 4)):
        assert block_product(kt, nt + 1) == 4 * block_product(kt, nt)
        assert not (kt <= 1)

    # Boundary p=k is safe because a k-term block has diameter k-1.
    kb, q, i, j, a, b = 17, 17, 5, 7, 7, 2
    nb = a * q - i
    db = b * q + i - j
    assert db >= kb
    assert nb + i == a * q
    assert nb + db + j == (a + b) * q
    assert [r for r in range(1, kb + 1) if (nb + r) % q == 0] == [i]
    assert [r for r in range(1, kb + 1) if (nb + db + r) % q == 0] == [j]

    center_k, center_i = 17, 9
    center_A, center_B = normalization(center_k, center_i, center_i)
    center_c2 = quadratic_coefficient(center_k, center_i, center_i, center_A, center_B)
    assert (center_A, center_B, center_c2) == (4, 1, 0)
    assert not (center_A < 2 * center_B)

    return {
        "k22_zero_pairs": zero_pairs,
        "k984_large_factor": 7_237,
        "p_equals_k_boundary": q,
        "excluded_center_ratio": [center_A, center_B],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=300)
    args = parser.parse_args()
    result = {"uniform": verify_uniform(args.max_k), "fixtures": verify_fixtures()}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
