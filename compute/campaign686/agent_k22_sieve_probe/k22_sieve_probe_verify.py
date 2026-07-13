#!/usr/bin/env python3
"""Exact audit of the quadratic/Runge/local-sieve probe at row k=22.

This file deliberately proves less than a row closure.  It reconstructs the
centered square-root data with ``Fraction`` and Python integers, checks the
quadratic-strip boundary, checks two coefficientwise Runge traps, exhibits
three integral root-pair fixtures that survive every unrestricted local
mask, and reproduces an exact (but not Lean-banked) bounded bit sieve.

No floating-point arithmetic is used in a certified claim.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache, reduce
from math import comb, gcd, lcm
from typing import Iterable


Poly = dict[int, int]
BivariatePoly = dict[tuple[int, int], int]

K = 22
R = 11
QUADRATIC_CUTOFF = K * K


def add_term(poly: Poly, degree: int, value: int) -> None:
    poly[degree] = poly.get(degree, 0) + value
    if poly[degree] == 0:
        del poly[degree]


def add_bivariate_term(
    poly: BivariatePoly, degree: tuple[int, int], value: int
) -> None:
    poly[degree] = poly.get(degree, 0) + value
    if poly[degree] == 0:
        del poly[degree]


def mul_poly(left: Poly, right: Poly) -> Poly:
    out: Poly = {}
    for i, ai in left.items():
        for j, bj in right.items():
            add_term(out, i + j, ai * bj)
    return out


def eval_poly(poly: Poly, value: int) -> int:
    return sum(coefficient * value**degree for degree, coefficient in poly.items())


def shift_poly(poly: Poly, shift: int) -> Poly:
    """Coefficients of p(X+shift), exactly."""
    out: Poly = {}
    for degree, coefficient in poly.items():
        for j in range(degree + 1):
            add_term(
                out,
                j,
                coefficient * comb(degree, j) * shift ** (degree - j),
            )
    return out


def shifted_two_variable(poly: Poly, shift: int) -> BivariatePoly:
    """Coefficients of p(shift+a+b), indexed by powers of (a,b)."""
    out: BivariatePoly = {}
    for degree, coefficient in poly.items():
        for total in range(degree + 1):
            base = coefficient * comb(degree, total) * shift ** (degree - total)
            for i in range(total + 1):
                add_bivariate_term(out, (i, total - i), base * comb(total, i))
    return out


def elementary(values: Iterable[int]) -> list[int]:
    out = [1]
    for value in values:
        out.append(0)
        for j in range(len(out) - 1, 0, -1):
            out[j] += value * out[j - 1]
    return out


@dataclass(frozen=True)
class RowData:
    scale: int
    s_poly: Poly
    t_poly: Poly
    d_poly: Poly
    odd_fixed_divisor: int


@lru_cache(maxsize=1)
def make_row_data() -> RowData:
    roots_squared = [(2 * j - 1) ** 2 for j in range(1, R + 1)]
    es = elementary(roots_squared)
    square_coefficients = [(-1) ** j * es[j] for j in range(R + 1)]

    # Polynomial part of sqrt(S): only terms through degree zero in z are
    # needed.  At odd r=11 this gives exponents 11,9,...,1.
    root_coefficients = [Fraction(1)]
    for n in range(1, R // 2 + 1):
        cross = sum(
            root_coefficients[i] * root_coefficients[n - i]
            for i in range(1, n)
        )
        root_coefficients.append((Fraction(square_coefficients[n]) - cross) / 2)
    scale = reduce(lcm, (coefficient.denominator for coefficient in root_coefficients), 1)

    s_poly = {
        2 * R - 2 * j: coefficient
        for j, coefficient in enumerate(square_coefficients)
    }
    t_poly = {
        R - 2 * j: int(scale * coefficient)
        for j, coefficient in enumerate(root_coefficients)
    }
    d_poly = mul_poly(t_poly, t_poly)
    for degree, coefficient in s_poly.items():
        add_term(d_poly, degree, -(scale**2) * coefficient)

    # For the integer polynomial f(a)=T(2a+1), its fixed divisor is the gcd
    # of any deg(f)+1 consecutive values.  Extra values below audit the same
    # finite-difference conclusion independently of the defining window.
    values = [abs(eval_poly(t_poly, 2 * a + 1)) for a in range(R + 1)]
    fixed = reduce(gcd, values, 0)
    for a in range(-R - 2, 2 * R + 3):
        assert eval_poly(t_poly, 2 * a + 1) % fixed == 0

    assert mul_poly(t_poly, t_poly) == {
        degree: coefficient
        for degree, coefficient in _add_scaled(s_poly, d_poly, scale**2).items()
        if coefficient
    }
    return RowData(scale, s_poly, t_poly, d_poly, fixed)


def _add_scaled(poly: Poly, other: Poly, scale: int) -> Poly:
    out = dict(other)
    for degree, coefficient in poly.items():
        add_term(out, degree, scale * coefficient)
    return out


def quadratic_strip_certificate() -> dict[str, object]:
    closed = [d for d in range(K, 10_000) if 18 * d <= QUADRATIC_CUTOFF]
    assert closed == [22, 23, 24, 25, 26]
    assert 18 * 26 <= QUADRATIC_CUTOFF < 18 * 27
    return {
        "closed_gaps": closed,
        "first_live_gap": 27,
        "boundary": [18 * 26, QUADRATIC_CUTOFF, 18 * 27],
    }


def canonical_tail_threshold() -> dict[str, int]:
    """Concrete coefficient threshold for the reconstructed k=22 data.

    This is an explicit instance of the universal coefficient construction;
    it is not a claim that Lean's noncomputable choice definition reduces to
    this numeral by kernel computation.
    """
    row = make_row_data()
    q = max(row.d_poly)
    A = sum(abs(c) for degree, c in row.t_poly.items() if degree < R)
    E = sum(abs(c) for degree, c in row.d_poly.items() if degree <= q)
    F = sum(abs(c) for degree, c in row.d_poly.items() if degree < q)
    threshold = max(2 * R, 2 * A + 1, 7 * F + 1, 10 * E + 1)
    return {"q": q, "A": A, "E": E, "F": F, "threshold": threshold}


def trap_coefficients(gap_floor: int, bound: int) -> BivariatePoly:
    """Coefficients of the lower Runge expression at d>=gap_floor.

    The exact bracket 4*15^22<16^22 gives n>=15d-21.  Thus at the gap
    floor, v>=30d-19 and w>=v+2d.  We substitute

        v = (30D-19)+a,  w = (32D-19)+a+b,

    where a,b are nonnegative.
    """
    row = make_row_data()
    v0 = 30 * gap_floor - 19
    w0 = v0 + 2 * gap_floor

    w_poly = dict(row.d_poly)
    for degree, coefficient in row.t_poly.items():
        add_term(w_poly, degree, bound * coefficient)
    out = shifted_two_variable(w_poly, w0)

    v_poly: Poly = {}
    for degree, coefficient in row.t_poly.items():
        add_term(v_poly, degree, 2 * bound * coefficient)
    for degree, coefficient in row.d_poly.items():
        add_term(v_poly, degree, -4 * coefficient)
    for degree, coefficient in shift_poly(v_poly, v0).items():
        add_bivariate_term(out, (degree, 0), coefficient)
    return out


def minimal_coefficientwise_bound(gap_floor: int) -> int:
    constant = trap_coefficients(gap_floor, 0)
    at_one = trap_coefficients(gap_floor, 1)
    answer = 0
    for degree in constant.keys() | at_one.keys():
        intercept = constant.get(degree, 0)
        slope = at_one.get(degree, 0) - intercept
        if slope <= 0:
            assert intercept > 0
        elif intercept <= 0:
            answer = max(answer, (-intercept) // slope + 1)
    assert min(trap_coefficients(gap_floor, answer).values()) > 0
    if answer:
        assert min(trap_coefficients(gap_floor, answer - 1).values()) <= 0
    return answer


def upper_negative_certificate(gap_floor: int) -> dict[str, int]:
    """Conservative proof of D(w)-4D(v)<0 under 14w<=15v."""
    row = make_row_data()
    denominator = 14
    numerator = 15
    degree = max(row.d_poly)
    leading = row.d_poly[degree]
    upper: Poly = {
        degree: leading * numerator**degree - 4 * leading * denominator**degree
    }
    for exponent, coefficient in row.d_poly.items():
        if exponent in (degree, 0):
            continue
        if coefficient > 0:
            add_term(
                upper,
                exponent,
                coefficient
                * denominator ** (degree - exponent)
                * numerator**exponent,
            )
        else:
            add_term(upper, exponent, -4 * coefficient * denominator**degree)
    shifted = shift_poly(upper, 30 * gap_floor - 19)
    assert max(shifted.values()) < 0
    return {
        "term_count": len(shifted),
        "largest_coefficient": max(shifted.values()),
        "smallest_coefficient": min(shifted.values()),
    }


def t_positivity_certificate(gap_floor: int) -> dict[str, int]:
    """Shifted-coefficient proof that both T-values in the trap are positive."""
    row = make_row_data()
    v0 = 30 * gap_floor - 19
    w0 = 32 * gap_floor - 19
    at_v = shift_poly(row.t_poly, v0)
    at_w = shift_poly(row.t_poly, w0)
    assert min(at_v.values()) > 0
    assert min(at_w.values()) > 0
    return {
        "v_term_count": len(at_v),
        "v_minimum_coefficient": min(at_v.values()),
        "w_term_count": len(at_w),
        "w_minimum_coefficient": min(at_w.values()),
    }


def trap_certificate(gap_floor: int) -> dict[str, object]:
    bound = minimal_coefficientwise_bound(gap_floor)
    coefficients = trap_coefficients(gap_floor, bound)
    previous = trap_coefficients(gap_floor, bound - 1)
    candidate_bound = (bound - 1) // 33
    return {
        "gap_floor": gap_floor,
        "v_floor": 30 * gap_floor - 19,
        "w_floor": 32 * gap_floor - 19,
        "bound": bound,
        "coefficient_count": len(coefficients),
        "minimum_coefficient": min(coefficients.values()),
        "minimum_degree": list(min(coefficients, key=coefficients.get)),
        "previous_minimum": min(previous.values()),
        "previous_minimum_degree": list(min(previous, key=previous.get)),
        "candidate_bound": candidate_bound,
        "candidate_remainder": (bound - 1) - 33 * candidate_bound,
        "T_positivity": t_positivity_certificate(gap_floor),
        "upper": upper_negative_certificate(gap_floor),
    }


def finite_strip_certificate() -> dict[str, object]:
    row = make_row_data()
    assert 4 * 15**K < 16**K
    assert 82**K < 4 * 77**K
    count = 0
    best: tuple[int, int, int, int] | None = None
    for d in range(27, 250):
        lower = 15 * d - 21
        upper = (77 * d - 6) // 5
        for n in range(lower, upper + 1):
            v = 2 * n + 23
            w = 2 * (n + d) + 23
            error = eval_poly(row.s_poly, w) - 4 * eval_poly(row.s_poly, v)
            assert error != 0
            record = (abs(error), d, n, error)
            if best is None or record[0] < best[0]:
                best = record
            count += 1
    assert best is not None
    return {
        "gap_range": [27, 249],
        "pair_count": count,
        "maximum_n": (77 * 249 - 6) // 5,
        "minimum_abs_error": best[0],
        "minimum_at": [best[1], best[2]],
        "signed_error": best[3],
    }


ROOT_FIXTURES = (
    (28_643_526_033, -3, -1),
    (19_687_413_989, -7, -1),
    (3_809_308_513, 13, 15),
)


def root_fixture_certificate() -> list[dict[str, int]]:
    row = make_row_data()
    out = []
    for t, w, v in ROOT_FIXTURES:
        sw = eval_poly(row.s_poly, w)
        sv = eval_poly(row.s_poly, v)
        tw = eval_poly(row.t_poly, w)
        tv = eval_poly(row.t_poly, v)
        m = tw - 2 * tv
        assert sw == 0 == sv
        assert m == -33 * t
        out.append({"t": t, "w": w, "v": v, "Tw": tw, "Tv": tv, "m": m})
    return out


@lru_cache(maxsize=None)
def local_allowed_t_residues(modulus: int) -> frozenset[int]:
    """Unrestricted local t-mask for moduli coprime to 33."""
    assert gcd(modulus, 33) == 1
    row = make_row_data()
    s_values = [eval_poly(row.s_poly, x) % modulus for x in range(modulus)]
    t_values = [eval_poly(row.t_poly, x) % modulus for x in range(modulus)]
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s_values):
        buckets.setdefault(value, []).append(w)
    m_values: set[int] = set()
    for v in range(modulus):
        for w in buckets.get(4 * s_values[v] % modulus, ()):
            m_values.add((t_values[w] - 2 * t_values[v]) % modulus)
    inverse = pow(-33 % modulus, -1, modulus)
    return frozenset(value * inverse % modulus for value in m_values)


def primes_through(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
    return primes


def periodic_mask(pattern: int, period: int, length: int) -> int:
    """Repeat a low-bit-first pattern, returning exactly ``length`` bits."""
    repetitions = (length + period - 1) // period
    out = 0
    out_length = 0
    block = pattern
    block_length = period
    while repetitions:
        if repetitions & 1:
            out |= block << out_length
            out_length += block_length
        repetitions >>= 1
        if repetitions:
            block |= block << block_length
            block_length *= 2
    return out & ((1 << length) - 1)


def compressed_branch_lengths(candidate_bound: int) -> dict[int, int]:
    """Parity and p=23 give t=46q+a for these four a values."""
    residues = local_allowed_t_residues(23)
    assert residues == frozenset({2, 6, 17, 21})
    branches = (17, 21, 25, 29)
    lengths = {
        residue: (candidate_bound - residue) // 46 + 1
        for residue in branches
        if residue <= candidate_bound
    }
    # Directly audit that this is exactly odd t in the four p=23 classes.
    for residue in branches:
        assert residue % 2 == 1 and residue % 23 in residues
    return lengths


def bounded_sieve_certificate(candidate_bound: int) -> dict[str, object]:
    """Exact packed-integer reproduction of the unformalized local sieve.

    This computation is evidence only.  The hostile audit explains why it is
    not a Lean theorem and why ordinary ``decide`` cannot simply enumerate
    the represented interval.
    """
    lengths = compressed_branch_lengths(candidate_bound)
    branches = [
        [residue, length, (1 << length) - 1]
        for residue, length in sorted(lengths.items())
    ]
    initial_count = sum(length for _, length, _ in branches)
    tail_counts: list[list[int]] = []
    active_primes = 0
    kill_prime = 0
    for prime in primes_through(953):
        if prime in (2, 3, 11, 23):
            continue
        allowed = local_allowed_t_residues(prime)
        if len(allowed) == prime:
            continue
        active_primes += 1
        inverse = pow(46, -1, prime)
        for branch in branches:
            residue, length, bits = branch
            q_residues = {
                ((allowed_residue - residue) * inverse) % prime
                for allowed_residue in allowed
            }
            pattern = sum(1 << q_residue for q_residue in q_residues)
            branch[2] = bits & periodic_mask(pattern, prime, length)
        count = sum(bits.bit_count() for _, _, bits in branches)
        if prime >= 857:
            tail_counts.append([prime, count])
        if count == 0:
            kill_prime = prime
            break
    assert kill_prime == 953
    assert sum(bits.bit_count() for _, _, bits in branches) == 0
    return {
        "candidate_bound": candidate_bound,
        "branch_lengths": {str(k): v for k, v in lengths.items()},
        "initial_count": initial_count,
        "active_prime_count": active_primes,
        "kill_prime": kill_prime,
        "tail_counts": tail_counts,
    }


@lru_cache(maxsize=1)
def audit() -> dict[str, object]:
    row = make_row_data()
    expected_t = {
        11: 256,
        9: -226_688,
        7: 67_609_696,
        5: -8_111_362_160,
        3: 352_497_378_310,
        1: -6_055_670_906_453,
    }
    expected_d = {
        10: 463_278_576_995_462_272,
        8: -216_425_162_804_858_318_080,
        6: 31_355_359_404_386_247_301_764,
        4: -1_470_309_582_711_394_865_435_644,
        2: 21_668_018_076_062_298_043_697_209,
        0: 12_389_157_521_837_708_451_840_000,
    }
    assert row.scale == 256
    assert row.t_poly == expected_t
    assert row.d_poly == expected_d
    assert row.odd_fixed_divisor == 33
    assert row.t_poly[1] % 2 == 1
    assert all(
        coefficient % 2 == 0
        for degree, coefficient in row.t_poly.items()
        if degree != 1
    )

    trap_27 = trap_certificate(27)
    assert trap_27["bound"] == 1_161_715_983_142
    assert trap_27["candidate_bound"] == 35_203_514_640

    trap_250 = trap_certificate(250)
    assert trap_250["bound"] == 125_239_835_548
    assert trap_250["candidate_bound"] == 3_795_146_531

    fixtures = root_fixture_certificate()
    assert all(fixture["t"] <= trap_27["candidate_bound"] for fixture in fixtures)
    assert all(fixture["t"] > trap_250["candidate_bound"] for fixture in fixtures)

    sieve = bounded_sieve_certificate(trap_250["candidate_bound"])
    assert sieve["initial_count"] == 330_012_742

    return {
        "row": {
            "k": K,
            "r": R,
            "scale": row.scale,
            "odd_fixed_divisor": row.odd_fixed_divisor,
            "T": row.t_poly,
            "D": row.d_poly,
        },
        "quadratic_strip": quadratic_strip_certificate(),
        "canonical_tail": canonical_tail_threshold(),
        "ratio_brackets": {
            "upper": 16**K - 4 * 15**K,
            "lower": 4 * 77**K - 82**K,
        },
        "unrestricted_gap_27_trap": trap_27,
        "unrestricted_root_fixtures": fixtures,
        "finite_strip": finite_strip_certificate(),
        "gap_250_trap": trap_250,
        "bounded_local_sieve": sieve,
        "verdict": "exact arithmetic only; no kernel-feasible row closure",
    }


def payload_sha256(payload: dict[str, object]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    payload = audit()
    wrapped = {"payload_sha256": payload_sha256(payload), "payload": payload}
    print(json.dumps(wrapped, indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
