#!/usr/bin/env python3
"""Exact certificates for the corrected #730 near-affine payment.

The theorem proved in the companion findings file is analytic, but every
finite calculation made there is reproduced here with integers or
``fractions.Fraction``.  No floating-point value is used as a premise.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt
import json


T = 5289


@dataclass(frozen=True)
class Branch:
    slope: int
    intercept: int


BRANCHES = {
    "P": Branch(42 * T, 11),
    "Q": Branch(72 * T, 13),
    "R": Branch(28 * T, 5),
    "S": Branch(72 * T, 19),
}

MAX_SLOPE = 72 * T
MAX_INTERCEPT = 19


def branch_values(x: int) -> dict[str, int]:
    if x < 1:
        raise ValueError("x must be positive")
    return {
        name: branch.slope * x + branch.intercept
        for name, branch in BRANCHES.items()
    }


def max_branch_value(X: int) -> int:
    if X < 1:
        raise ValueError("X must be positive")
    return MAX_SLOPE * X + MAX_INTERCEPT


def divisibility_count(name: str, p: int, a: int, X: int) -> int:
    """Count ``1 <= x <= X`` for which ``p^a`` divides the branch.

    The admissible branch has one residue class modulo ``p^a``.  A branch
    whose slope is not a unit has no count supplied by this helper.
    """

    if p < 2 or a < 1 or X < 1:
        raise ValueError("require p>=2, a>=1, X>=1")
    branch = BRANCHES[name]
    if gcd(branch.slope, p) != 1:
        raise ValueError("branch slope is not invertible modulo p")
    q = p**a
    root = (-branch.intercept * pow(branch.slope, -1, q)) % q
    first = q if root == 0 else root
    if first > X:
        return 0
    return 1 + (X - first) // q


def exact_valuation_count(name: str, p: int, a: int, X: int) -> int:
    """Count ``p^a || L(x)`` on an admissible branch."""

    return divisibility_count(name, p, a, X) - divisibility_count(
        name, p, a + 1, X
    )


def cofactor_test_value(name: str, x: int, p: int, a: int) -> int:
    """Return the exact Kummer test integer on a branch valuation event."""

    if p < 3 or p % 2 == 0 or a < 1:
        raise ValueError("require an odd prime base and a positive exponent")
    values = branch_values(x)
    q = p**a
    if values[name] % q != 0:
        raise ValueError("p^a does not divide the selected branch")
    if name == "P":
        return (values["P"] // q) * values["Q"]
    if name == "Q":
        return values["P"] * (values["Q"] // q)
    if name == "R":
        numerator = 3 * (values["R"] // q) * values["S"] - 1
    elif name == "S":
        numerator = 3 * values["R"] * (values["S"] // q) - 1
    else:
        raise KeyError(name)
    if numerator % 2 != 0:
        raise AssertionError("R/S cofactor numerator must be even")
    return numerator // 2


def base_p_digit_length(value: int, p: int) -> int:
    if value < 1 or p < 2:
        raise ValueError("require value>=1 and p>=2")
    digits = 0
    work = value
    while work:
        work //= p
        digits += 1
    return digits


def kappa_one_third_certificate(p: int) -> bool:
    """Exact algebraic certificate for ``kappa_p <= 1/3`` when p>=5.

    Cubing ``2p/(p+1) <= p^(1/3)`` gives the returned integer inequality.
    """

    if p < 5:
        raise ValueError("certificate is used only for p>=5")
    return 8 * p * p <= (p + 1) ** 3


def near_envelope(a: int, r: int) -> bool:
    """Rational envelope for eta=1/12 and kappa_p<=1/3.

    The actual near condition implies ``12*s < 5*r``.  Paying this larger
    envelope avoids any numerical logarithm.
    """

    if a < 1 or r < 1:
        raise ValueError("require a,r>=1")
    s = max(2 * r - a, 0)
    return 12 * s < 5 * r


def threshold_consequence(
    *,
    X: int,
    p: int,
    a: int,
    r: int,
    residue_count: int,
    next_weight: Fraction,
    global_weight_upper: Fraction,
) -> bool:
    """Check the exact powered threshold from the abstract premises.

    Here ``next_weight`` is ``((r+1) log p)^2`` in the analytic
    instantiation.  The function accepts a rational stand-in so its finite
    certificate is entirely exact.
    """

    if X < 1 or p < 5 or a < 1 or r < 1 or residue_count < 0:
        raise ValueError("invalid threshold parameters")
    if not kappa_one_third_certificate(p) or not near_envelope(a, r):
        raise ValueError("parameters are not in the rational near envelope")
    if a < 2 or 12 * a <= 19 * r:
        raise AssertionError("near envelope must force a>=2 and 12a>19r")
    q = p**a
    if X > q * (residue_count + 1):
        raise ValueError("residue-count lower relation is absent")
    if next_weight < 1:
        raise ValueError("next block weight must be at least one")
    if Fraction(residue_count, 1) >= p ** (r + 1) * next_weight:
        raise ValueError("r is not maximal under the supplied next weight")
    if next_weight > global_weight_upper:
        raise ValueError("global weight does not dominate the next weight")

    lhs = Fraction(X**38, 1)
    rhs = (2 * global_weight_upper) ** 38 * q**81
    if not lhs < rhs:
        raise AssertionError("exact threshold consequence failed")
    return True


def floor_nth_root(value: int, degree: int) -> int:
    if value < 0 or degree < 1:
        raise ValueError("require value>=0 and degree>=1")
    if value < 2 or degree == 1:
        return value
    low, high = 0, 1
    while high**degree <= value:
        high *= 2
    while low + 1 < high:
        middle = (low + high) // 2
        if middle**degree <= value:
            low = middle
        else:
            high = middle
    return low


def ceil_nth_root(value: int, degree: int) -> int:
    root = floor_nth_root(value, degree)
    return root if root**degree == value else root + 1


def _is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def prime_power_tail_partial(
    *, Y: int, prime_limit: int, exponent_limit: int
) -> Fraction:
    """Finite exact diagnostic for the reciprocal prime-power tail."""

    if Y < 1 or prime_limit < 2 or exponent_limit < 2:
        raise ValueError("invalid tail parameters")
    total = Fraction(0, 1)
    for p in range(2, prime_limit + 1):
        if not _is_prime(p):
            continue
        q = p * p
        for _a in range(2, exponent_limit + 1):
            if q >= Y:
                total += Fraction(1, q)
            q *= p
    return total


def rational_tail_upper(Y: int) -> Fraction:
    """Rational upper bound for ``2Y^-1/2 + 3Y^-2/3``."""

    if Y < 1:
        raise ValueError("Y must be positive")
    square_root = max(1, isqrt(Y))
    cube_root = max(1, floor_nth_root(Y, 3))
    return Fraction(2, square_root) + Fraction(3, cube_root * cube_root)


def prime_power_pair_count_upper(M: int) -> int:
    """Upper-bound pairs ``(p,a)``, ``a>=2``, with ``p^a<=M``."""

    if M < 1:
        raise ValueError("M must be positive")
    return isqrt(M) + M.bit_length() * floor_nth_root(M, 3)


def _threshold_integer_floor(X: int, weight_upper: Fraction) -> int:
    """Largest y with ``y^81 (2W)^38 <= X^38``."""

    target = Fraction(X**38, 1) / (2 * weight_upper) ** 38
    low, high = 0, 1
    while Fraction(high**81, 1) <= target:
        high *= 2
    while low + 1 < high:
        middle = (low + high) // 2
        if Fraction(middle**81, 1) <= target:
            low = middle
        else:
            high = middle
    return low


def dyadic_one_percent_certificate() -> dict[str, object]:
    """Exact uniform certificate for every cutoff ``X >= 2^57``.

    The monotonic dyadic reductions are proved in the findings file.  This
    function reproduces the one endpoint calculation on which they land.
    """

    X0 = 2**57
    M_upper = 2**20 * X0
    bit_length_upper = 78
    weight_upper = Fraction(
        (43 * bit_length_upper) ** 2,
        38**2,
    )
    Y_integer_lower = _threshold_integer_floor(X0, weight_upper)
    threshold_powered_inequality = (
        Fraction(Y_integer_lower**81, 1) * (2 * weight_upper) ** 38
        <= Fraction(X0**38, 1)
    )
    sqrt_Y_floor = isqrt(Y_integer_lower)
    cuberoot_Y_floor = floor_nth_root(Y_integer_lower, 3)

    tail_for_four_branches = 4 * rational_tail_upper(Y_integer_lower)
    boundary_for_four_branches = Fraction(
        4
        * (
            ceil_nth_root(M_upper, 2)
            + bit_length_upper * ceil_nth_root(M_upper, 3)
        ),
        X0,
    )
    payment_upper = tail_for_four_branches + boundary_for_four_branches
    return {
        "X0": X0,
        "M_upper": M_upper,
        "bit_length_upper": bit_length_upper,
        "weight_upper": weight_upper,
        "Y_integer_lower": Y_integer_lower,
        "sqrt_Y_floor": sqrt_Y_floor,
        "cuberoot_Y_floor": cuberoot_Y_floor,
        "threshold_powered_inequality": threshold_powered_inequality,
        "tail_for_four_branches": tail_for_four_branches,
        "boundary_for_four_branches": boundary_for_four_branches,
        "payment_upper": payment_upper,
        "payment_below_one_percent": payment_upper < Fraction(1, 100),
    }


def main() -> None:
    cert = dyadic_one_percent_certificate()
    serializable = {
        key: (
            f"{value.numerator}/{value.denominator}"
            if isinstance(value, Fraction)
            else value
        )
        for key, value in cert.items()
    }
    print(json.dumps(serializable, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
