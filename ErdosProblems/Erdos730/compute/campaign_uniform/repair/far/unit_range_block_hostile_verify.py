#!/usr/bin/env python3
"""Independent hostile verifier for the Erdős 730 unit-range payment.

This module deliberately imports no producer verifier and no campaign helper.
All branch data, root classes, translated block counts, logarithm certificates,
geometric sums, and prime sums are reconstructed with Python integers and
``fractions.Fraction``.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import cache
from math import gcd, isqrt
from typing import Any, Iterable


T = 3 * 41 * 43
QUADRATIC_UNIT = 3024 * T * T
BRANCHES: dict[str, dict[str, int]] = {
    "P": {
        "slope": 42 * T,
        "intercept": 11,
        "denominator": 7,
        "linear_constant": -246 * T,
        "u_multiplier": 144 * T,
    },
    "Q": {
        "slope": 72 * T,
        "intercept": 13,
        "denominator": 12,
        "linear_constant": 246 * T,
        "u_multiplier": 84 * T,
    },
    "R": {
        "slope": 28 * T,
        "intercept": 5,
        "denominator": 14,
        "linear_constant": 258 * T,
        "u_multiplier": 216 * T,
    },
    "S": {
        "slope": 72 * T,
        "intercept": 19,
        "denominator": 12,
        "linear_constant": -258 * T,
        "u_multiplier": 84 * T,
    },
}


def branch_numerator(branch: str, pa: int, c: int) -> int:
    if branch == "P":
        return 12 * pa * c * c - 41 * c
    if branch == "Q":
        return 7 * pa * c * c + 41 * c
    if branch == "R":
        return 54 * pa * c * c + 129 * c - 7
    if branch == "S":
        return 7 * pa * c * c - 43 * c - 6
    raise KeyError(branch)


def branch_value(branch: str, pa: int, c: int) -> int:
    numerator = branch_numerator(branch, pa, c)
    denominator = BRANCHES[branch]["denominator"]
    if numerator % denominator:
        raise AssertionError("branch value lost integrality")
    return numerator // denominator


def forbidden_digit(branch: str, p: int) -> int:
    if p < 5 or p % 2 == 0:
        raise ValueError("require odd p>=5")
    if branch in ("P", "Q"):
        return 0
    if branch in ("R", "S"):
        return (p - 1) // 2
    raise KeyError(branch)


def primes_through(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for candidate in range(2, isqrt(limit) + 1):
        if sieve[candidate]:
            count = (limit - candidate * candidate) // candidate + 1
            sieve[candidate * candidate : limit + 1 : candidate] = b"\x00" * count
    return [number for number in range(2, limit + 1) if sieve[number]]


def branch_root(branch: str, p: int, a: int) -> tuple[int, int] | None:
    """Return ``(x0,c0)`` for ``L(x0)=p^a*c0``, or ``None`` if unavailable."""

    if p < 2 or a < 1:
        raise ValueError("require p>=2 and a>=1")
    data = BRANCHES[branch]
    q = p**a
    common = gcd(data["slope"], q)
    if data["intercept"] % common:
        return None
    if common != 1:
        raise AssertionError("unexpected multiple-root branch")
    x0 = (-data["intercept"] * pow(data["slope"], -1, q)) % q
    numerator = data["slope"] * x0 + data["intercept"]
    if numerator % q:
        raise AssertionError("root calculation failed")
    return x0, numerator // q


def output_at_k(branch: str, p: int, a: int, k: int) -> tuple[int, int]:
    root = branch_root(branch, p, a)
    if root is None:
        raise ValueError("branch has no root class")
    _, c0 = root
    c = c0 + BRANCHES[branch]["slope"] * k
    return branch_value(branch, p**a, c), c


def restricted_word(value: int, p: int, digits: int) -> bool:
    if digits < 1:
        raise ValueError("require at least one digit")
    H = (p + 1) // 2
    work = value % (p**digits)
    for _ in range(digits):
        if work % p >= H:
            return False
        work //= p
    return True


def exact_obstruction(branch: str, p: int, a: int, k: int, digits: int) -> bool:
    value, c = output_at_k(branch, p, a, k)
    return c % p != 0 and restricted_word(value, p, digits)


def low_word_bound(p: int, r: int) -> int:
    if p < 5 or p % 2 == 0 or r < 1:
        raise ValueError("require odd p>=5 and r>=1")
    H = (p + 1) // 2
    return (H - 1) * H ** (r - 1)


def quadratic_identity_audit() -> dict[str, Any]:
    checks = 0
    for branch in BRANCHES.values():
        for p in (5, 7, 11):
            for a in (1, 2, 3):
                pa = p**a
                linear = pa * branch["u_multiplier"] * 2 + branch["linear_constant"]
                constant = branch["intercept"]
                P = p**3
                for u in range(-3, 4):
                    for v in range(-3, 4):
                        def quadratic(k: int) -> int:
                            return QUADRATIC_UNIT * pa * k * k + linear * k + constant

                        difference = (
                            quadratic(u + P * v)
                            - quadratic(u)
                            - P * v * (2 * QUADRATIC_UNIT * pa * u + linear)
                        )
                        expected = QUADRATIC_UNIT * pa * P * P * v * v
                        if difference != expected or difference % (P * P):
                            raise AssertionError("quadratic block identity failed")
                        checks += 1
    return {"signed_fixtures": checks, "all_exact": True}


def availability_and_deleted_digit_audit() -> dict[str, Any]:
    checked_primes = [prime for prime in primes_through(1000) if prime >= 5]
    availability_histogram = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
    digit_bridge_checks = 0
    unavailable: dict[int, list[str]] = {}
    for p in checked_primes:
        available = []
        for branch, data in BRANCHES.items():
            root = branch_root(branch, p, 1)
            if root is None:
                unavailable.setdefault(p, []).append(branch)
                continue
            available.append(branch)
            if gcd(data["linear_constant"], p) != 1:
                raise AssertionError("available branch lost p-adic unit")
            expected_forbidden = forbidden_digit(branch, p)
            for k in range(p):
                value, c = output_at_k(branch, p, 1, k)
                if (c % p == 0) != (value % p == expected_forbidden):
                    raise AssertionError("deleted output digit bridge failed")
                if expected_forbidden >= (p + 1) // 2:
                    raise AssertionError("deleted digit is outside restricted alphabet")
                digit_bridge_checks += 1
        availability_histogram[len(available)] += 1

    # Two and three are absent from every affine branch.  The fixed factor 3
    # is handled outside these four root classes.
    for p in (2, 3):
        if any(branch_root(branch, p, 1) is not None for branch in BRANCHES):
            raise AssertionError("small excluded prime unexpectedly has a branch root")

    if unavailable != {7: ["P", "R"], 41: list(BRANCHES), 43: list(BRANCHES)}:
        raise AssertionError(unavailable)
    return {
        "primes_5_through_997": len(checked_primes),
        "availability_histogram": availability_histogram,
        "unavailable_branches": unavailable,
        "deleted_digit_checks": digit_bridge_checks,
        "p2_p3_have_no_branch_roots": True,
    }


def aligned_block_audit() -> dict[str, Any]:
    cases = [
        ("P", 5, 1, 1),
        ("Q", 5, 2, 2),
        ("R", 5, 2, 2),
        ("S", 5, 2, 1),
        ("Q", 7, 2, 2),
        ("S", 7, 2, 1),
        ("P", 11, 2, 2),
        ("Q", 11, 2, 1),
        ("R", 11, 2, 2),
        ("S", 11, 2, 1),
    ]
    blocks = 0
    parameters = 0
    maximum_full_ratio = Fraction(0, 1)
    boundary_2_2 = False
    for branch, p, r, a in cases:
        if branch_root(branch, p, a) is None:
            raise AssertionError("aligned test selected unavailable branch")
        P = p**r
        expected = low_word_bound(p, r)
        for block_index in range(P):
            low_count = 0
            full_count = 0
            for u in range(P):
                k = u + P * block_index
                value, c = output_at_k(branch, p, a, k)
                exact = c % p != 0
                low_count += int(exact and restricted_word(value, p, r))
                full_count += int(exact and restricted_word(value, p, 2 * r))
            if low_count != expected or full_count > expected:
                raise AssertionError((branch, p, r, a, block_index, low_count, full_count))
            maximum_full_ratio = max(maximum_full_ratio, Fraction(full_count, expected))
            blocks += 1
            parameters += P
        boundary_2_2 |= a == r == 2
    return {
        "cases": len(cases),
        "aligned_blocks": blocks,
        "parameters": parameters,
        "every_low_count_exact": True,
        "every_full_count_at_most_low_bound": True,
        "maximum_full_to_low_bound": maximum_full_ratio,
        "a_eq_r_eq_2_included": boundary_2_2,
    }


def intersected_aligned_blocks(start: int, length: int, P: int) -> int:
    if length < 1 or P < 1:
        raise ValueError("require positive length and block")
    return (start + length - 1) // P - start // P + 1


def translated_interval_audit() -> dict[str, Any]:
    combinatorial_checks = 0
    maximum_extra_blocks = 0
    exact_alignment_fixture = None
    for P in (1, 5, 7, 25):
        for start in range(-2 * P, 2 * P + 1):
            for length in range(1, 4 * P + 2):
                blocks = intersected_aligned_blocks(start, length, P)
                envelope = length // P + 2
                if blocks > envelope:
                    raise AssertionError("translated block envelope failed")
                maximum_extra_blocks = max(maximum_extra_blocks, blocks - length // P)
                combinatorial_checks += 1
        aligned = intersected_aligned_blocks(P, 2 * P, P)
        if aligned != 2:
            raise AssertionError("exact alignment was overcounted geometrically")
        exact_alignment_fixture = {"P": P, "length": 2 * P, "actual_blocks": aligned}

    map_checks = 0
    maximum_cover_ratio = Fraction(0, 1)
    for branch, p, r, a in (("Q", 5, 2, 2), ("S", 7, 1, 1), ("R", 11, 1, 1)):
        P = p**r
        period = P * P
        mask = [int(exact_obstruction(branch, p, a, k, 2 * r)) for k in range(period)]
        extended = mask + mask
        prefix = [0]
        for value in extended:
            prefix.append(prefix[-1] + value)
        widths = sorted({1, P - 1, P, P + 1, 2 * P - 1, 2 * P, 2 * P + 1, 4 * P})
        M = low_word_bound(p, r)
        for width in widths:
            if width >= period:
                continue
            cover = M * (width // P + 2)
            for start in range(period):
                count = prefix[start + width] - prefix[start]
                if count > cover:
                    raise AssertionError("actual translated interval exceeded cover")
                if cover:
                    maximum_cover_ratio = max(maximum_cover_ratio, Fraction(count, cover))
                map_checks += 1
    return {
        "combinatorial_checks": combinatorial_checks,
        "actual_map_checks": map_checks,
        "maximum_boundary_blocks_beyond_floor": maximum_extra_blocks,
        "maximum_count_to_cover": maximum_cover_ratio,
        "exact_alignment_fixture": exact_alignment_fixture,
        "arbitrary_translation_envelope_holds": True,
    }


def root_class_interval(
    branch: str, p: int, a: int, X: int
) -> dict[str, int] | None:
    if X < 1:
        raise ValueError("require X>=1")
    root = branch_root(branch, p, a)
    if root is None:
        return None
    x0, c0 = root
    q = p**a
    first = x0 if x0 >= 1 else q
    if first > X:
        return {
            "q": q,
            "x0": x0,
            "c0": c0,
            "N": 0,
            "first_x": first,
            "last_x": first - q,
            "first_k": (first - x0) // q,
            "last_k": (first - x0) // q - 1,
        }
    N = 1 + (X - first) // q
    last = first + (N - 1) * q
    return {
        "q": q,
        "x0": x0,
        "c0": c0,
        "N": N,
        "first_x": first,
        "last_x": last,
        "first_k": (first - x0) // q,
        "last_k": (last - x0) // q,
    }


def atanh_log_interval(z: Fraction, terms: int = 36) -> tuple[Fraction, Fraction]:
    if not Fraction(0, 1) <= z < 1 or terms < 1:
        raise ValueError("invalid atanh input")
    partial = sum(
        (2 * z ** (2 * index + 1) / (2 * index + 1) for index in range(terms)),
        Fraction(0, 1),
    )
    tail = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return partial, partial + tail


@cache
def log_interval(integer: int) -> tuple[Fraction, Fraction]:
    if integer < 1:
        raise ValueError("require positive integer")
    if integer == 1:
        return Fraction(), Fraction()
    exponent = integer.bit_length() - 1
    power = 1 << exponent
    ln2_low, ln2_high = atanh_log_interval(Fraction(1, 3))
    residual_low, residual_high = atanh_log_interval(
        Fraction(integer - power, integer + power)
    )
    return exponent * ln2_low + residual_low, exponent * ln2_high + residual_high


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


@cache
def critical_length(p: int, r: int) -> int:
    if p < 2 or r < 1:
        raise ValueError("require p>=2 and r>=1")
    lower_log, upper_log = log_interval(p)
    scale = p**r * r * r
    lower = scale * lower_log * lower_log
    upper = scale * upper_log * upper_log
    candidate = ceil_fraction(upper)
    if not Fraction(candidate - 1, 1) < lower <= upper <= candidate:
        raise AssertionError("log interval did not isolate the critical ceiling")
    return candidate


def maximal_r(p: int, N: int) -> int | None:
    if N < 0:
        raise ValueError("require N>=0")
    if N < critical_length(p, 1):
        return None
    r = 1
    while critical_length(p, r + 1) <= N:
        r += 1
        if r > 128:
            raise AssertionError("unexpected maximal-r search depth")
    if not critical_length(p, r) <= N < critical_length(p, r + 1):
        raise AssertionError("maximal-r bracket failed")
    return r


def root_and_normalization_audit() -> dict[str, Any]:
    root_checks = 0
    empty_classes = 0
    for branch in BRANCHES:
        for p in (5, 7, 11, 13, 17, 19, 41, 43):
            for a in (1, 2, 3):
                q = p**a
                for X in (1, q - 1, q, q + 1, 3 * q + 2, 10_000):
                    record = root_class_interval(branch, p, a, X)
                    brute = [
                        x
                        for x in range(1, X + 1)
                        if (BRANCHES[branch]["slope"] * x + BRANCHES[branch]["intercept"]) % q == 0
                    ]
                    if record is None:
                        if brute:
                            raise AssertionError("unavailable branch had roots")
                        continue
                    if record["N"] != len(brute):
                        raise AssertionError("root-class length mismatch")
                    if brute and (record["first_x"], record["last_x"]) != (brute[0], brute[-1]):
                        raise AssertionError("root-class endpoints mismatch")
                    if record["N"] == 0:
                        empty_classes += 1
                    else:
                        if record["q"] * (record["N"] - 1) > X:
                            raise AssertionError("q(N-1)<=X has wrong orientation")
                        if record["last_x"] - record["first_x"] != record["q"] * (record["N"] - 1):
                            raise AssertionError("root-class spacing failed")
                    root_checks += 1

    monotonic_checks = 0
    for p in (5, 7, 11, 101):
        previous = 0
        for r in range(1, 9):
            current = critical_length(p, r)
            if current <= previous:
                raise AssertionError("critical lengths are not strictly increasing")
            previous = current
            monotonic_checks += 1
    if not log_interval(5)[0] > 1:
        raise AssertionError("independent log(5)>1 certificate failed")

    normalization_rows = []
    for branch, p, a, X, expected_r in (
        ("Q", 5, 2, 12_500, 2),
        ("R", 5, 3, 500_000, 3),
        ("P", 5, 2, 1_000_000, 4),
        ("Q", 7, 2, 49_000, 2),
    ):
        record = root_class_interval(branch, p, a, X)
        if record is None or record["N"] == 0:
            raise AssertionError("normalization case has no root class")
        N = record["N"]
        r = maximal_r(p, N)
        if r != expected_r or not (2 <= a <= r):
            raise AssertionError((branch, p, a, X, N, r))
        P = p**r
        M = low_word_bound(p, r)
        C = sum(
            exact_obstruction(branch, p, a, k, 2 * r)
            for k in range(record["first_k"], record["last_k"] + 1)
        )
        premises = {
            "critical": 4 * P <= N,
            "class_orientation": p**a * (N - 1) <= X,
            "block_cover": C * P <= M * (N + 2 * P),
        }
        if not all(premises.values()):
            raise AssertionError((branch, p, a, X, premises))
        if C * p**a * P > 2 * M * X:
            raise AssertionError("normalized cross inequality failed")
        normalization_rows.append(
            {
                "branch": branch,
                "p": p,
                "a": a,
                "r": r,
                "X": X,
                "N": N,
                "C": C,
                "P": P,
                "M": M,
                "qN_minus_one": p**a * (N - 1),
                "normalized_cross_margin": 2 * M * X - C * p**a * P,
            }
        )

    boundary = next(row for row in normalization_rows if row["a"] == row["r"] == 2)
    return {
        "root_class_checks": root_checks,
        "empty_root_classes": empty_classes,
        "critical_monotonic_checks": monotonic_checks,
        "log5_lower_gt_one": True,
        "normalization_rows": normalization_rows,
        "a_eq_r_eq_2_row": boundary,
        "qN_minus_one_orientation": "q*(N-1)<=X",
        "maximal_r_unique_when_present": True,
    }


def exponent_partition_audit() -> dict[str, Any]:
    counts = {"strict": 0, "unit": 0, "first_power": 0}
    checks = 0
    for a in range(1, 257):
        for r in range(1, 257):
            s = max(2 * r - a, 0)
            strict = s < r
            unit = 2 <= a <= r
            first = a == 1
            if strict != (r + 1 <= a):
                raise AssertionError("strict-band equivalence failed")
            if (s >= r) != (a <= r):
                raise AssertionError("unit-range complement failed")
            if sum((strict, unit, first)) != 1:
                raise AssertionError("long-class exponent partition overlaps or misses")
            counts["strict" if strict else "unit" if unit else "first_power"] += 1
            checks += 1

    actual_assignments = {"short": 0, "strict": 0, "unit": 0, "first_power": 0}
    for branch in BRANCHES:
        for p in (5, 7, 11, 13):
            for a in range(1, 6):
                for X in (10, 100, 1_000, 10_000, 100_000, 1_000_000):
                    record = root_class_interval(branch, p, a, X)
                    if record is None:
                        continue
                    r = maximal_r(p, record["N"])
                    if r is None:
                        actual_assignments["short"] += 1
                    elif a >= r + 1:
                        actual_assignments["strict"] += 1
                    elif 2 <= a <= r:
                        actual_assignments["unit"] += 1
                    elif a == 1:
                        actual_assignments["first_power"] += 1
                    else:
                        raise AssertionError("actual assignment missed partition")
    return {
        "abstract_checks": checks,
        "abstract_counts": counts,
        "actual_assignment_counts": actual_assignments,
        "strict_and_unit_disjoint": True,
        "a_eq_r_is_unit": True,
        "a_eq_r_plus_one_is_strict": True,
        "short_is_no_maximal_r": True,
        "top_range_definition_in_candidate": False,
        "overlap_effect": "none in 58/125; future overlapping upper bounds would be conservative",
    }


def rho(p: int, r: int) -> Fraction:
    H = (p + 1) // 2
    return Fraction((H - 1) * H ** (r - 1), p**r)


def series_at_prime(p: int) -> Fraction:
    if p < 5 or p % 2 == 0:
        raise ValueError("require odd p>=5")
    return Fraction(p + 1, p * (p - 1) * (2 * p + 1))


def geometric_series_audit() -> dict[str, Any]:
    rows = []
    for p in (5, 7, 11, 101):
        H = (p + 1) // 2
        ratio = Fraction(H, p * p)
        derived = Fraction(2 * p, p + 1) * ratio**2 / (1 - ratio)
        closed = series_at_prime(p)
        if derived != closed:
            raise AssertionError("closed geometric formula failed")
        finite = sum(
            (
                Fraction(1, p**a) * rho(p, r)
                for a in range(2, 13)
                for r in range(a, 25)
            ),
            Fraction(),
        )
        if not Fraction() < finite < closed:
            raise AssertionError("finite double sum does not approach from below")
        rows.append(
            {
                "p": p,
                "closed": closed,
                "finite_a_le_12_r_lt_25": finite,
                "positive_remainder": closed - finite,
            }
        )
    return {"rows": rows, "formula_exact": True}


def prime_sum_audit() -> dict[str, Any]:
    primes = [prime for prime in primes_through(1000) if prime >= 5]
    partial = sum((series_at_prime(prime) for prime in primes), Fraction())
    partial_margin = Fraction(57, 1000) - partial
    if len(primes) != 166 or primes[-1] != 997 or partial_margin <= 0:
        raise AssertionError("finite prime certificate failed")

    # For every p>1000, S_p<1/(p(p-1)); all-integer telescoping starts at 1001.
    for p in (1009, 1013, 2003, 10007):
        if not series_at_prime(p) < Fraction(1, p * (p - 1)):
            raise AssertionError("pointwise tail comparison failed")
    finite_telescoping = sum(
        (Fraction(1, n * (n - 1)) for n in range(1001, 5001)), Fraction()
    )
    if finite_telescoping != Fraction(1, 1000) - Fraction(1, 5000):
        raise AssertionError("telescoping identity failed")
    tail = Fraction(1, 1000)
    single_branch_without_endpoint_factor = partial + tail
    four_branch_with_endpoint_factor = 8 * single_branch_without_endpoint_factor
    if not single_branch_without_endpoint_factor < Fraction(29, 500):
        raise AssertionError("single-branch ceiling failed")
    if not four_branch_with_endpoint_factor < Fraction(58, 125) < Fraction(1, 2):
        raise AssertionError("four-branch payment failed")
    return {
        "prime_count": len(primes),
        "largest_prime": primes[-1],
        "partial": partial,
        "partial_below_57_over_1000_margin": partial_margin,
        "tail_pointwise_strict": True,
        "integer_tail_start": 1001,
        "integer_tail": tail,
        "finite_telescoping_check": finite_telescoping,
        "single_branch_without_endpoint_factor": single_branch_without_endpoint_factor,
        "endpoint_cover_factor": 2,
        "branch_union_factor": 4,
        "four_branch_bound": four_branch_with_endpoint_factor,
        "margin_below_58_over_125": Fraction(58, 125) - four_branch_with_endpoint_factor,
        "margin_below_half": Fraction(1, 2) - four_branch_with_endpoint_factor,
    }


def report() -> dict[str, Any]:
    return {
        "quadratic_identity": quadratic_identity_audit(),
        "availability_and_deleted_digit": availability_and_deleted_digit_audit(),
        "aligned_blocks": aligned_block_audit(),
        "translated_intervals": translated_interval_audit(),
        "root_classes_and_normalization": root_and_normalization_audit(),
        "exponent_partition": exponent_partition_audit(),
        "geometric_double_sum": geometric_series_audit(),
        "prime_sum": prime_sum_audit(),
        "scope": {
            "paper_exact_payment": "long classes with maximal r and 2<=a<=r",
            "kernel_expanded_payment": False,
            "remaining_gate": (
                "for every X>=2^57, bound the normalized maximal-r a=1 contribution "
                "plus the separately defined short/top contribution by "
                "263/500-delta for one explicit delta>0"
            ),
        },
    }


def json_ready(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, dict):
        return {str(key): json_ready(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_ready(item) for item in value]
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(json_ready(report()), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
