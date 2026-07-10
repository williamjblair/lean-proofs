#!/usr/bin/env python3
"""Exact certificate for the stronger affine-progression obstruction.

The existing near-affine audit partitions a restricted ``r``-digit output
set modulo ``b p^s``.  Along one progression modulo ``p^s`` the quadratic
part vanishes completely, so it is stronger to choose the low ``s`` digits
first and pigeonhole only the remaining ``r-s`` restricted digits modulo
``b``.  This file checks the resulting explicit counterexample to the
zero-error signed far inequality.

Every verdict below is integer or ``Fraction`` arithmetic.  Rational bounds
for logarithms are imported from the already-audited far-range checker.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd
import json
from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compute730.campaign_uniform.repair.far.far_fourier import log_bounds
from compute730.campaign_uniform.test_uniformity import (
    BRANCHES,
    expanded_value,
    phi,
    root_data,
)


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def q_branch_linear_coefficient() -> int:
    return abs(int(BRANCHES["Q"]["b"]))


def separated_far_exact(p: int, r: int, s: int) -> bool:
    """Exact form of ``s >= (kappa_p+1/12)r``.

    With ``H=(p+1)/2`` this is equivalent to
    ``H^(12r) >= p^(13r-12s)``.
    """

    if p < 5 or p % 2 == 0 or r < 1 or not 0 <= s <= r:
        raise ValueError("require odd p>=5, r>=1, and 0<=s<=r")
    exponent = 13 * r - 12 * s
    if exponent < 0:
        return True
    H = (p + 1) // 2
    return H ** (12 * r) >= p**exponent


def progression_hit_lower_bound(p: int, r: int, s: int, b: int) -> int:
    """Pigeonhole lower bound from the surviving high restricted word.

    Fix the low ``s`` output digits to ``1,0,...,0``.  Among the
    ``H^(r-s)`` possible next words, one residue class modulo ``b`` contains
    at least this many elements.  The upper ``r`` output digits are zero.
    """

    if b < 1 or not 1 <= s < r:
        raise ValueError("require b>=1 and 1<=s<r")
    H = (p + 1) // 2
    return (H ** (r - s) + b - 1) // b


def critical_length_upper(p: int, r: int) -> int:
    """Exact rational upper bound for ``ceil(p^r (r log p)^2)``."""

    _, log_upper = log_bounds(p)
    return ceil_fraction(Fraction(p**r * r * r, 1) * log_upper * log_upper)


def advertised_rhs_upper(p: int, r: int) -> Fraction:
    """Upper-bound the claimed zero-error far RHS at critical length.

    The true critical ceiling is at most ``critical_length_upper`` and
    ``1+1/(r log p)`` is at most the expression using the rigorous lower
    logarithm bound.
    """

    H = (p + 1) // 2
    log_lower, _ = log_bounds(p)
    length_upper = critical_length_upper(p, r)
    return (
        Fraction(H ** (2 * r), p ** (2 * r))
        * length_upper
        * (1 + Fraction(1, 1) / (r * log_lower))
    )


def explicit_p5_certificate() -> dict[str, object]:
    """The compact exact witness ``p=5, r=432, s=176``.

    Here ``s/r=11/27`` and ``a=2r-s=688``.  The Q branch is admissible,
    the tuple lies in the advertised separated range, and the constructed
    hit lower bound exceeds a rigorous upper bound for the claimed RHS.
    """

    p = 5
    r = 432
    s = 176
    a = 2 * r - s
    H = (p + 1) // 2
    b = q_branch_linear_coefficient()
    branch = BRANCHES["Q"]
    x0, c0 = root_data(branch, p, a)
    pa = p**a
    v = phi(branch, pa, c0)
    k_for_output_digit_one = ((1 - v) * pow(b, -1, p)) % p
    log_lower, log_upper = log_bounds(p)
    lower = progression_hit_lower_bound(p, r, s, b)
    rhs_upper = advertised_rhs_upper(p, r)
    return {
        "p": p,
        "r": r,
        "s": s,
        "a": a,
        "H": H,
        "b": b,
        "branch_admissible": gcd(int(branch["lam"]), p) == 1 and gcd(b, p) == 1,
        "root_exact": int(branch["lam"]) * x0 + int(branch["mu"]) == pa * c0,
        "root_in_range": 0 <= x0 < pa,
        "output_digit_one_realized": expanded_value(
            branch, p, a, c0, k_for_output_digit_one
        )
        % p
        == 1,
        "output_digit_one_forces_exact_valuation": (
            c0 + int(branch["lam"]) * k_for_output_digit_one
        )
        % p
        != 0,
        "progression_modulus_identity": a + s == 2 * r,
        "separated": separated_far_exact(p, r, s),
        "compact_separation": 3**324 > 5**219,
        "compact_divergence": 5**27 > 3**38,
        "rho_fits_modulus": 1 + p**s * (b - 1) < p ** (2 * r),
        "hit_span_lt_p_to_r": p**s * (p ** (r - s) - 1) < b * p**r,
        "critical_length_covers_p_to_r": Fraction(r * r, 1) * log_lower * log_lower
        >= 1,
        "log_interval_ordered": log_lower < log_upper,
        "hit_lower_bound": lower,
        "critical_length_upper": critical_length_upper(p, r),
        "rhs_upper_numerator": rhs_upper.numerator,
        "rhs_upper_denominator": rhs_upper.denominator,
        "counterexample": Fraction(lower, 1) > rhs_upper,
        "cleared_margin": lower * rhs_upper.denominator - rhs_upper.numerator,
    }


def main() -> None:
    certificate = explicit_p5_certificate()
    compact = {
        key: value
        for key, value in certificate.items()
        if key not in {"rhs_upper_numerator", "rhs_upper_denominator", "cleared_margin"}
    }
    compact["cleared_margin_positive"] = int(certificate["cleared_margin"]) > 0
    print(json.dumps(compact, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
