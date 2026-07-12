#!/usr/bin/env python3
"""Independent hostile arithmetic for the reflected quadratic lift.

This file imports none of the producer implementation.  It recomputes the
block products, local signed weight, reflected owner terms, and congruence
from their definitions.
"""

from __future__ import annotations

from math import factorial, gcd, prod


def independent_row(k: int, n: int, d: int, i: int, q: int) -> dict[str, int | bool]:
    if k < 1 or n < 0 or d < 0 or not 1 <= i <= k or q < 1:
        raise ValueError("invalid hostile row")
    lower_terms = [n + r for r in range(1, k + 1)]
    upper_terms = [n + d + r for r in range(1, k + 1)]
    A = n + i
    B = n + d + (k + 1 - i)
    W = (-1 if (i - 1) % 2 else 1) * factorial(i - 1) * factorial(k - i)
    epsilon = -1 if (k - 1) % 2 else 1
    equation_error = prod(upper_terms) - 4 * prod(lower_terms)
    linear = epsilon * B - 4 * A
    congruence_error = equation_error - W * linear
    return {
        "lower": A,
        "upper": B,
        "weight": W,
        "equation_error": equation_error,
        "linear": linear,
        "landings": A % q == 0 and B % q == 0,
        "quadratic_congruence": congruence_error % (q * q) == 0,
        "weighted_lift": (W * linear) % (q * q) == 0,
        "bare_lift": linear % (q * q) == 0,
        "cancellable": gcd(abs(W), q) == 1,
    }


def independent_row_passes(k: int, n: int, d: int, row: int) -> bool:
    modulus = n + row
    residue = 1 % modulus
    for value in range(d + 1 - row, d + k - row + 1):
        residue = residue * (value % modulus) % modulus
    return residue == 0


def independent_first_failure(k: int, n: int, d: int) -> int | None:
    for row in range(1, k + 1):
        if not independent_row_passes(k, n, d, row):
            return row
    return None
