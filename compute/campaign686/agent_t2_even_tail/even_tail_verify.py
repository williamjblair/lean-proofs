"""Exact certificates for the uniform even-row Runge tail in Erdős 686.

For k=2r, S_r(W) is the centered block polynomial.  This module constructs
the polynomial part of sqrt(S_r), clears denominators, and returns a wholly
explicit threshold above which the standard integer trap closes the row.
All arithmetic is over ``fractions.Fraction`` or Python integers.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import gcd


def lcm(a: int, b: int) -> int:
    return abs(a // gcd(a, b) * b)


def trim(poly: list[Fraction]) -> list[Fraction]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def add(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * max(len(a), len(b))
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    return trim(out)


def mul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def scale(a: list[Fraction], c: Fraction) -> list[Fraction]:
    return trim([c * x for x in a])


def evaluate(a: list[Fraction], x: int) -> Fraction:
    value = Fraction(0)
    for coefficient in reversed(a):
        value = value * x + coefficient
    return value


def centered_polynomial(r: int) -> list[Fraction]:
    if r < 1:
        raise ValueError("r must be positive")
    out = [Fraction(1)]
    for j in range(1, r + 1):
        odd = 2 * j - 1
        out = mul(out, [Fraction(-(odd * odd)), Fraction(0), Fraction(1)])
    return out


def square_root_polynomial_part(s_poly: list[Fraction], r: int) -> list[Fraction]:
    """Unique monic T of degree r for which deg(T^2-S)<r."""

    if len(s_poly) != 2 * r + 1 or s_poly[-1] != 1:
        raise ValueError("S must be monic of degree 2r")
    coefficients = [Fraction(0)] * (r + 1)
    coefficients[r] = Fraction(1)
    # At degree r+j, 0<=j<r, the only still-unknown contribution to T^2
    # is 2*T_j*T_r.  Descending recursion therefore determines T_j.
    for degree in range(2 * r - 1, r - 1, -1):
        j = degree - r
        known = Fraction(0)
        for a in range(j + 1, r + 1):
            b = degree - a
            if 0 <= b <= r and b != j:
                known += coefficients[a] * coefficients[b]
        coefficients[j] = (s_poly[degree] - known) / 2
    return trim(coefficients)


@dataclass(frozen=True)
class EvenTailCertificate:
    r: int
    k: int
    denominator: int
    s_coefficients: tuple[int, ...]
    t_coefficients: tuple[int, ...]
    d_coefficients: tuple[int, ...]
    deficit_degree: int
    deficit_leading: int
    t_lower_norm: int
    deficit_norm: int
    deficit_lower_norm: int
    threshold: int


def certificate(r: int) -> EvenTailCertificate:
    if r < 2:
        raise ValueError("the uniform ratio proof uses r>=2")
    s_q = centered_polynomial(r)
    t_q = square_root_polynomial_part(s_q, r)
    denominator = reduce(lcm, (c.denominator for c in t_q), 1)
    t_z = [int(c * denominator) for c in t_q]
    s_z = [int(c) for c in s_q]
    d_q = add(mul([Fraction(x) for x in t_z], [Fraction(x) for x in t_z]),
              scale(s_q, Fraction(-(denominator * denominator))))
    if any(c.denominator != 1 for c in d_q):
        raise AssertionError("cleared deficit is not integral")
    d_z = [int(c) for c in d_q]
    q = len(d_z) - 1
    if not q < r:
        raise AssertionError(("deficit degree is not below r", r, q))
    leading = d_z[-1]
    if leading == 0:
        raise AssertionError("zero deficit")
    t_lower_norm = sum(abs(x) for x in t_z[:-1])
    deficit_norm = sum(abs(x) for x in d_z)
    deficit_lower_norm = sum(abs(x) for x in d_z[:-1])
    # These deliberately loose integer thresholds imply, for every W>=M:
    # T(W)>0, |D(W)-L W^q| < |L|W^q/7, and 10||D||/W<1.
    threshold = max(
        2 * t_lower_norm + 1,
        7 * deficit_lower_norm + 1,
        10 * deficit_norm + 1,
        2 * r,
    )
    cert = EvenTailCertificate(
        r=r,
        k=2 * r,
        denominator=denominator,
        s_coefficients=tuple(s_z),
        t_coefficients=tuple(t_z),
        d_coefficients=tuple(d_z),
        deficit_degree=q,
        deficit_leading=leading,
        t_lower_norm=t_lower_norm,
        deficit_norm=deficit_norm,
        deficit_lower_norm=deficit_lower_norm,
        threshold=threshold,
    )
    verify_certificate(cert)
    return cert


def verify_certificate(cert: EvenTailCertificate) -> None:
    s = [Fraction(x) for x in cert.s_coefficients]
    t = [Fraction(x) for x in cert.t_coefficients]
    d = [Fraction(x) for x in cert.d_coefficients]
    identity_error = add(
        mul(t, t),
        add(scale(s, Fraction(-(cert.denominator**2))), scale(d, Fraction(-1))),
    )
    if identity_error != [0]:
        raise AssertionError(("T^2-C^2S-D identity failed", cert.r))
    if len(d) - 1 != cert.deficit_degree or d[-1] != cert.deficit_leading:
        raise AssertionError("deficit metadata mismatch")
    if cert.deficit_degree >= cert.r:
        raise AssertionError("bad deficit degree")
    if cert.threshold <= 2 * cert.t_lower_norm:
        raise AssertionError("T positivity threshold is not strict")
    if cert.threshold <= 7 * cert.deficit_lower_norm:
        raise AssertionError("deficit dominance threshold is not strict")
    if cert.threshold <= 10 * cert.deficit_norm:
        raise AssertionError("integer-trap threshold is not strict")

    # Reproduce the pointwise norm estimates at the exact boundary and one
    # displaced point.  Their proofs for all larger W are coefficientwise.
    for w in (cert.threshold, cert.threshold + 17):
        tv = evaluate(t, w)
        dv = evaluate(d, w)
        if tv <= 0:
            raise AssertionError(("T not positive", cert.r, w))
        lead = Fraction(cert.deficit_leading * w**cert.deficit_degree)
        if 7 * abs(dv - lead) >= abs(lead):
            raise AssertionError(("deficit not dominated", cert.r, w))


def ratio_power_bound_holds(r: int, v: int, w: int, q: int) -> bool:
    """Exact finite form of w/v < 1+1/(r-1) => w^q < 3v^q."""

    if not (r >= 2 and v > 0 and 0 <= q < r):
        return False
    if not (r - 1) * w < r * v:
        return False
    return w**q < 3 * v**q


def sample_report(start_r: int = 2, stop_r: int = 20) -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    for r in range(start_r, stop_r + 1):
        cert = certificate(r)
        rows.append(
            {
                "k": cert.k,
                "denominator": cert.denominator,
                "deficit_degree": cert.deficit_degree,
                "threshold_digits": len(str(cert.threshold)),
                "threshold": cert.threshold,
            }
        )
    return rows


if __name__ == "__main__":
    for row in sample_report(2, 20):
        print(row)
