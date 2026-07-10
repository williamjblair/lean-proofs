#!/usr/bin/env python3
"""Exact diagnostics for the structured odd-tail equation in Erdős 686.

For odd ``k = 2r+1`` put

    P_k(T) = product(T+a, a=-r..r).

The equation is ``P_k(Y+d) = 4 P_k(Y)``.  This module deliberately uses
only Python integers.  It exposes the homogeneous Taylor data needed by the
large-prime-power lift; it does not use floating point approximations to
``4^(1/k)``.
"""

from __future__ import annotations

from math import prod


TARGET_K = (5, 7, 9, 11, 13, 15)
WINDOW_C = {5: 4, 7: 5, 9: 7, 11: 8, 13: 9, 15: 11}
PRIME_POWER_BOUND_A = {k: 3 * c + 2 for k, c in WINDOW_C.items()}


def centered_product(k: int, value: int) -> int:
    """Return P_k(value) for positive odd k."""
    if k <= 0 or k % 2 == 0:
        raise ValueError("k must be positive and odd")
    radius = (k - 1) // 2
    return prod(value + offset for offset in range(-radius, radius + 1))


def block_product(k: int, n: int) -> int:
    """Return (n+1)...(n+k)."""
    return prod(n + i for i in range(1, k + 1))


def centered_coordinates(k: int, n: int, d: int) -> tuple[int, int]:
    """Return X,Y with block_product(k,n+d)=P_k(X), block_product(k,n)=P_k(Y)."""
    if k % 2 == 0:
        raise ValueError("k must be odd")
    center = (k + 1) // 2
    return n + d + center, n + center


def polynomial_coefficients(k: int) -> list[int]:
    """Coefficients of P_k, low degree first."""
    radius = (k - 1) // 2
    coefficients = [1]
    for offset in range(-radius, radius + 1):
        next_coefficients = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            next_coefficients[degree] += offset * coefficient
            next_coefficients[degree + 1] += coefficient
        coefficients = next_coefficients
    return coefficients


def evaluate(coefficients: list[int], value: int) -> int:
    """Evaluate a low-degree-first integer polynomial."""
    result = 0
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


Bivariate = dict[tuple[int, int], int]


def _multiply_bivariate(left: Bivariate, right: Bivariate) -> Bivariate:
    out: Bivariate = {}
    for (z1, d1), c1 in left.items():
        for (z2, d2), c2 in right.items():
            key = (z1 + z2, d1 + d2)
            out[key] = out.get(key, 0) + c1 * c2
    return {key: coefficient for key, coefficient in out.items() if coefficient}


def shifted_equation_coefficients(k: int, factor_offset: int) -> Bivariate:
    """Coefficients of P_k(-offset+z+d)-4P_k(-offset+z).

    ``factor_offset`` names the centered factor ``Y+factor_offset``.  Thus
    ``z = Y+factor_offset`` and the corresponding root is ``Y=-offset``.
    Keys are ``(z_degree, d_degree)``.
    """
    radius = (k - 1) // 2
    if not -radius <= factor_offset <= radius:
        raise ValueError("factor offset outside the centered block")

    upper: Bivariate = {(0, 0): 1}
    lower: Bivariate = {(0, 0): 1}
    for other in range(-radius, radius + 1):
        constant = other - factor_offset
        upper = _multiply_bivariate(
            upper, {(0, 0): constant, (1, 0): 1, (0, 1): 1}
        )
        lower = _multiply_bivariate(lower, {(0, 0): constant, (1, 0): 1})

    out = dict(upper)
    for key, coefficient in lower.items():
        out[key] = out.get(key, 0) - 4 * coefficient
    return {key: coefficient for key, coefficient in out.items() if coefficient}


def root_derivative(k: int, factor_offset: int) -> int:
    """Return P_k'(-factor_offset), as a product of root differences."""
    radius = (k - 1) // 2
    return prod(
        other - factor_offset
        for other in range(-radius, radius + 1)
        if other != factor_offset
    )


def unique_factor_offset_mod_prime(k: int, y: int, prime: int) -> int:
    """Return the unique offset a with prime | y+a, requiring prime>=k."""
    if prime < k:
        raise ValueError("prime must be at least k")
    radius = (k - 1) // 2
    offsets = [a for a in range(-radius, radius + 1) if (y + a) % prime == 0]
    if len(offsets) != 1:
        raise ValueError(f"expected one root offset, found {offsets}")
    return offsets[0]


def equation_residue_mod_gap(k: int, y: int, d: int) -> int:
    """Return F(Y,d) modulo d; it equals -3 P_k(Y) modulo d."""
    if d <= 0:
        raise ValueError("d must be positive")
    return (centered_product(k, y + d) - 4 * centered_product(k, y)) % d


def window_power_check(k: int) -> bool:
    """Return the exact check (C_k+1)^k < 4 C_k^k."""
    c = WINDOW_C[k]
    return (c + 1) ** k < 4 * c**k


def p_adic_lift_conclusion(k: int, y: int, d: int, prime: int, h: int) -> tuple[int, int]:
    """Return the offset and lift modulus forced by an exact solution.

    Preconditions are checked: ``prime>=k`` is prime externally, ``h`` is a
    positive power of ``prime`` dividing ``d``, and the centered equation is
    exact.  The returned modulus is ``h^3`` for the center factor and ``h^2``
    otherwise; it divides ``d-3*(y+offset)``.
    """
    if prime < k or h <= 0 or d % h:
        raise ValueError("invalid prime-power divisor")
    if centered_product(k, y + d) != 4 * centered_product(k, y):
        raise ValueError("not an exact centered solution")
    if centered_product(k, y) % h:
        raise ValueError("h does not divide the lower centered product")
    offset = unique_factor_offset_mod_prime(k, y, prime)
    if (y + offset) % h:
        raise ValueError("the full prime power does not lie in its unique factor")
    modulus = h ** (3 if offset == 0 else 2)
    assert (d - 3 * (y + offset)) % modulus == 0
    return offset, modulus
