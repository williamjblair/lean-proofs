#!/usr/bin/env python3
"""Exact audit for the even-k square-root polynomial-part route.

All algebra uses ``fractions.Fraction`` and Python integers.  No floating
point value enters a certified claim.  The optional human-readable decimal
columns are derived only after the exact comparisons have been made.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import gcd, lcm
from typing import Dict, Iterable, Tuple


Poly = Dict[int, int]
QPoly = Dict[int, Fraction]


def elementary(values: Iterable[int]) -> list[int]:
    """Elementary symmetric functions e_0,...,e_r."""
    out = [1]
    for a in values:
        out.append(0)
        for j in range(len(out) - 1, 0, -1):
            out[j] += a * out[j - 1]
    return out


def add_term(poly: Poly, degree: int, value: int) -> None:
    poly[degree] = poly.get(degree, 0) + value
    if poly[degree] == 0:
        del poly[degree]


def mul_poly(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for i, ai in a.items():
        for j, bj in b.items():
            add_term(out, i + j, ai * bj)
    return out


def eval_poly(poly: Poly, x: int | Fraction) -> int | Fraction:
    return sum(c * x**e for e, c in poly.items())


def shift_poly(poly: Poly, shift: int) -> Poly:
    """Return p(x+shift), using exact binomial expansion."""
    from math import comb

    out: Poly = {}
    for e, c in poly.items():
        for j in range(e + 1):
            add_term(out, j, c * comb(e, j) * shift ** (e - j))
    return out


@dataclass(frozen=True)
class EvenData:
    k: int
    r: int
    scale: int
    s_poly: Poly
    t_poly: Poly
    d_poly: Poly
    fixed_divisor_odd: int
    first_admissible_odd_center: int


def make_data(k: int) -> EvenData:
    assert k >= 2 and k % 2 == 0
    r = k // 2
    roots_sq = [(2 * j - 1) ** 2 for j in range(1, r + 1)]
    es = elementary(roots_sq)

    # S(W)=W^(2r)+q_1 W^(2r-2)+...+q_r.
    q = [(-1) ** j * es[j] for j in range(r + 1)]
    # sqrt(1+q_1 z+...)=sum b_j z^j, recursively.
    b = [Fraction(1)]
    for n in range(1, r // 2 + 1):
        cross = sum(b[i] * b[n - i] for i in range(1, n))
        b.append((Fraction(q[n]) - cross) / 2)
    scale = reduce(lcm, (x.denominator for x in b), 1)
    t_poly = {r - 2 * j: int(scale * bj) for j, bj in enumerate(b)}
    s_poly = {2 * r - 2 * j: qj for j, qj in enumerate(q)}
    t_sq = mul_poly(t_poly, t_poly)
    d_poly = dict(t_sq)
    for e, c in s_poly.items():
        add_term(d_poly, e, -(scale**2) * c)

    # For an integer polynomial f of degree <=r, gcd(f(0),...,f(r)) is
    # its fixed divisor.  Here f(t)=T(2t+1).
    vals = [int(eval_poly(t_poly, 2 * t + 1)) for t in range(r + 1)]
    fixed = reduce(gcd, (abs(x) for x in vals), 0)
    assert fixed > 0
    # Independent extra values exercise the finite-difference claim.
    for t in range(-r - 2, 2 * r + 3):
        assert int(eval_poly(t_poly, 2 * t + 1)) % fixed == 0

    # If d>=k and S(w)=4S(v), monotonicity of S on W>k-1 gives
    # S(v+2k)<=4S(v).  Find the exact first odd center passing this test.
    def boundary(v: int) -> int:
        return int(eval_poly(s_poly, v + 2 * k) - 4 * eval_poly(s_poly, v))

    v = k + 1
    if v % 2 == 0:
        v += 1
    while boundary(v) > 0:
        v += 2
    assert boundary(v - 2) > 0 and boundary(v) <= 0

    # Identity and degree audit.
    assert mul_poly(t_poly, t_poly) == {
        e: c for e, c in _poly_add_scaled(s_poly, d_poly, scale**2).items() if c
    }
    expected_degree = r - 2 if r % 2 == 0 else r - 1
    assert max(d_poly) == expected_degree

    return EvenData(k, r, scale, s_poly, t_poly, d_poly, fixed, v)


def _poly_add_scaled(s_poly: Poly, d_poly: Poly, scale_sq: int) -> Poly:
    out = dict(d_poly)
    for e, c in s_poly.items():
        add_term(out, e, scale_sq * c)
    return out


def interval_eval(poly: Poly, lo: Fraction, hi: Fraction) -> Tuple[Fraction, Fraction]:
    """Termwise rigorous enclosure for a polynomial on 0<lo<=x<=hi."""
    assert 0 < lo <= hi
    lower = Fraction(0)
    upper = Fraction(0)
    for e, c in poly.items():
        a, b = lo**e, hi**e
        if c >= 0:
            lower += c * a
            upper += c * b
        else:
            lower += c * b
            upper += c * a
    return lower, upper


def eval_shift_coefficients(poly: Poly, base: int) -> Poly:
    """Coefficients of p(base+a), indexed by the exponent of a."""
    return shift_poly(poly, base)


def add_bivariate_term(poly: Dict[tuple[int, int], int], ij: tuple[int, int], c: int) -> None:
    poly[ij] = poly.get(ij, 0) + c
    if poly[ij] == 0:
        del poly[ij]


def shifted_w_coefficients(poly: Poly, base: int) -> Dict[tuple[int, int], int]:
    """Coefficients of p(base+a+b), indexed by powers of (a,b)."""
    from math import comb

    out: Dict[tuple[int, int], int] = {}
    for e, c in poly.items():
        for total in range(e + 1):
            base_part = c * comb(e, total) * base ** (e - total)
            for i in range(total + 1):
                add_bivariate_term(out, (i, total - i), base_part * comb(total, i))
    return out


def k18_trap_certificate() -> dict[str, int]:
    """Exact coefficient certificate for -731939653 < m < 0 at k=18."""
    row = make_data(18)
    trap = 731_939_653
    # E = D(w)+trap*T(w)+2*trap*T(v)-4*D(v), with
    # v=451+a and w=487+a+b.  Every coefficient is strictly positive.
    wpoly = dict(row.d_poly)
    for e, c in row.t_poly.items():
        add_term(wpoly, e, trap * c)
    e_coeff = shifted_w_coefficients(wpoly, 487)
    vpoly: Poly = {}
    for e, c in row.t_poly.items():
        add_term(vpoly, e, 2 * trap * c)
    for e, c in row.d_poly.items():
        add_term(vpoly, e, -4 * c)
    for i, c in eval_shift_coefficients(vpoly, 451).items():
        add_bivariate_term(e_coeff, (i, 0), c)
    assert len(e_coeff) == 55 and min(e_coeff.values()) > 0

    # A conservative upper bound for 11^8*(D(w)-4D(v)) under 11w<=12v.
    A = 78_397_083_729_792
    B = 16_673_477_276_146_464
    C = 945_705_074_655_002_832
    E = 9_110_023_357_135_451_751
    upper_poly: Poly = {
        8: (A * 12**8 - 4 * A * 11**8),
        6: 4 * B * 11**8,
        4: C * 11**4 * 12**4,
        2: 4 * E * 11**8,
    }
    neg_upper_shift = {i: -c for i, c in eval_shift_coefficients(upper_poly, 451).items()}
    assert len(neg_upper_shift) == 9 and min(neg_upper_shift.values()) > 0

    # T is positive throughout both shifted domains used above.
    assert min(eval_shift_coefficients(row.t_poly, 451).values()) > 0
    assert min(eval_shift_coefficients(row.t_poly, 487).values()) > 0
    assert trap - 1 == row.fixed_divisor_odd * 9_036_292
    return {
        "trap": trap,
        "candidate_count": 9_036_292,
        "lower_terms": len(e_coeff),
        "lower_min_coefficient": min(e_coeff.values()),
        "lower_constant": e_coeff[(0, 0)],
        "negative_terms": len(neg_upper_shift),
        "negative_min_coefficient": min(neg_upper_shift.values()),
        "negative_constant": neg_upper_shift[0],
    }


def continuous_boundary_certificate(data: EvenData, bits: int = 384) -> dict[str, int]:
    """Certify the real d=k boundary and enclose T(v+2k)-2T(v).

    The ratio S(v+2k)/S(v) is strictly decreasing for v>k-1, factor by
    factor, so the sign-changing interval contains the unique boundary root.
    Bisection signs and the final H interval are all exact rationals.
    """
    k = data.k
    f_poly = shift_poly(data.s_poly, 2 * k)
    for e, c in data.s_poly.items():
        add_term(f_poly, e, -4 * c)
    h_poly = shift_poly(data.t_poly, 2 * k)
    for e, c in data.t_poly.items():
        add_term(h_poly, e, -2 * c)

    lo = Fraction(data.first_admissible_odd_center - 2)
    hi = Fraction(data.first_admissible_odd_center)
    assert eval_poly(f_poly, lo) > 0 > eval_poly(f_poly, hi)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if eval_poly(f_poly, mid) > 0:
            lo = mid
        else:
            hi = mid
    hlo, hhi = interval_eval(h_poly, lo, hi)
    assert hhi < 0
    return {
        "bits": bits,
        "root_lo_num": lo.numerator,
        "root_lo_den": lo.denominator,
        "root_hi_num": hi.numerator,
        "root_hi_den": hi.denominator,
        "h_lo_num": hlo.numerator,
        "h_lo_den": hlo.denominator,
        "h_hi_num": hhi.numerator,
        "h_hi_den": hhi.denominator,
        "abs_h_exceeds_fixed": int(-hhi > data.fixed_divisor_odd),
        "abs_h_below_fixed": int(-hlo < data.fixed_divisor_odd),
    }


def audit() -> tuple[list[EvenData], dict[int, dict[str, int]]]:
    rows = [make_data(k) for k in range(16, 102, 2)]
    certs = {}
    for k in (16, 18, 20, 24, 32, 50, 100):
        bits = 512 if k == 100 else 384
        certs[k] = continuous_boundary_certificate(rows[(k - 16) // 2], bits)
    assert certs[16]["abs_h_below_fixed"] == 1
    for k in (18, 20, 24, 32, 50, 100):
        assert certs[k]["abs_h_exceeds_fixed"] == 1
    k18_trap_certificate()
    return rows, certs


def main() -> None:
    rows, certs = audit()
    print("k r scale fixed_odd first_center deg_D lead_D boundary_relation")
    for row in rows:
        rel = "<fixed" if row.k == 16 else "not-certified"
        if row.k in certs and certs[row.k]["abs_h_exceeds_fixed"]:
            rel = ">fixed"
        print(
            row.k,
            row.r,
            row.scale,
            row.fixed_divisor_odd,
            row.first_admissible_odd_center,
            max(row.d_poly),
            row.d_poly[max(row.d_poly)],
            rel,
        )
    print("exact continuous-boundary certificates:")
    for k, cert in certs.items():
        print(
            k,
            "bits=", cert["bits"],
            "root_den_bits=", cert["root_lo_den"].bit_length(),
            "H_below_fixed=", cert["abs_h_below_fixed"],
            "H_exceeds_fixed=", cert["abs_h_exceeds_fixed"],
        )
    print("k18 exact trap:", k18_trap_certificate())


if __name__ == "__main__":
    main()
