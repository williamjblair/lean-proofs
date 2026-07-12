#!/usr/bin/env python3
"""Hostile exact audit of good-prime Hensel flexibility in the scale equation.

The good-prime center calculation fixes exact valuations, but it does not
produce a local contradiction at third or fourth order.  This verifier lifts
the full primitive-scale polynomial, not a truncated obstruction, and then
chooses primitive representatives on the correct real side of 4^(1/k).
"""

from __future__ import annotations

import json
import math
from typing import Any

from compute.campaign686.agent_cf_tail.cf_primitive_tail_verify import (
    TARGET_K,
    a_value,
    elementary_square_coefficients,
    scale_residual,
)
from compute.campaign686.agent_cf_tail.scale_newton_verify import (
    discrepancy_bound,
)


# Each prime is larger than its row and avoids 60*e_r*e_(r-1).
GOOD_PRIMES = {5: 7, 7: 11, 9: 11, 11: 13, 13: 17, 15: 17}
SCALE_EXPONENT = 3
LIFT_PRECISION = 32


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero is not used in this audit")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def unique_hensel_lift(
    k: int, prime: int, g: int, v: int, precision: int
) -> tuple[int, int, list[int]]:
    """Lift the simple root u=4v mod p one base-p digit at a time."""
    u = (4 * v) % prime
    modulus = prime
    if scale_residual(k, u, v, g) % modulus:
        raise AssertionError("the initial linear root is absent")
    chosen_digits: list[int] = []
    while modulus < prime**precision:
        candidates = [
            digit
            for digit in range(prime)
            if scale_residual(k, u + digit * modulus, v, g)
            % (prime * modulus)
            == 0
        ]
        if len(candidates) != 1:
            raise AssertionError(
                ("Hensel root is not simple", k, prime, modulus, candidates)
            )
        digit = candidates[0]
        chosen_digits.append(digit)
        u += digit * modulus
        modulus *= prime
    return u, modulus, chosen_digits


def primitive_real_side_fixture(k: int, prime: int) -> dict[str, Any]:
    """Choose a primitive below-alpha representative of the lifted class."""
    a = SCALE_EXPONENT
    g = prime**a
    root, modulus, digits = unique_hensel_lift(
        k, prime, g, 1, LIFT_PRECISION
    )
    if modulus != prime**LIFT_PRECISION:
        raise AssertionError("unexpected final modulus")

    # The deterministic choice L=root-1 gives
    #   v=L*M+1, u=L*M+root=v+(root-1).
    # Hence gcd(u,v)=gcd(root-1,(root-1)M+1)=1.  It also preserves the lifted
    # residue pair (u,v)=(root,1) mod M, while the real ratio is arbitrarily
    # close to one as M grows.
    denominator_block = root - 1
    numerator_block = denominator_block
    v = 1 + denominator_block * modulus
    u = root + numerator_block * modulus
    if not (
        v < u < 2 * v
        and u**k < 4 * v**k
        and math.gcd(u, v) == 1
    ):
        raise AssertionError(("deterministic primitive representative failed", k, prime))
    residual = scale_residual(k, u, v, g)
    if residual % modulus:
        raise AssertionError("full scale polynomial did not retain its lift")

    z = g * g
    a1 = a_value(u, v, 1)
    gap = g * (u - v)
    center = g * v
    centered_residual = 3 * center - gap
    if centered_residual != g * a1:
        raise AssertionError("center identity failed")

    e = elementary_square_coefficients(k)[-1]
    if e * a1 % z:
        raise AssertionError("constant square divisibility failed")
    q = e * a1 // z

    exact = {
        "primitive_gap": valuation(u - v, prime),
        "primitive_denominator": valuation(v, prime),
        "linear_residual": valuation(a1, prime),
        "constant_quotient": valuation(q, prime),
        "gap": valuation(gap, prime),
        "center": valuation(center, prime),
        "centered_residual": valuation(centered_residual, prime),
        "full_scale_residual": valuation(residual, prime),
    }
    expected = {
        "primitive_gap": 0,
        "primitive_denominator": 0,
        "linear_residual": 2 * a,
        "constant_quotient": 0,
        "gap": a,
        "center": a,
        "centered_residual": 3 * a,
    }
    for name, expected_value in expected.items():
        if exact[name] != expected_value:
            raise AssertionError(("exact valuation changed", k, name, exact[name]))
    if exact["full_scale_residual"] < LIFT_PRECISION:
        raise AssertionError("full scale lift lost precision")

    # Record three named finite depths.  The stronger checked fact is the
    # full scale congruence modulo p^32; no Taylor obstruction is substituted
    # for that equation in this hostile audit.
    for order in (3, 4, 5):
        if residual % prime ** (order * a):
            raise AssertionError(("finite-order obstruction survived", k, order))

    return {
        "k": k,
        "prime": prime,
        "scale_exponent": a,
        "g": g,
        "z": z,
        "lift_precision": LIFT_PRECISION,
        "hensel_digits": digits,
        "denominator_block": denominator_block,
        "numerator_block": numerator_block,
        "u": u,
        "v": v,
        "correct_real_side": u**k < 4 * v**k,
        "primitive": math.gcd(u, v) == 1,
        "third_order_full_scale_congruence": residual % prime ** (3 * a) == 0,
        "fourth_order_full_scale_congruence": residual % prime ** (4 * a) == 0,
        "fifth_order_full_scale_congruence": residual % prime ** (5 * a) == 0,
        "valuations": exact,
    }


def full_report() -> dict[str, Any]:
    rows = []
    for k in TARGET_K:
        prime = GOOD_PRIMES[k]
        if prime <= k or discrepancy_bound(k) % prime == 0:
            raise AssertionError(("declared prime is not good", k, prime))
        rows.append(primitive_real_side_fixture(k, prime))
    return {
        "status": (
            "good-prime exact valuations hold, but the full scale equation "
            "remains Hensel-flexible through third, fourth, and fifth order"
        ),
        "rows": rows,
    }


def main() -> None:
    print(json.dumps(full_report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
