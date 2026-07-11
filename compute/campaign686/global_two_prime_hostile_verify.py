#!/usr/bin/env python3
"""Independent exact verifier for the Erdős 686 global two-prime closure.

This file deliberately imports nothing from the producer verifier.  It
recomputes the local Taylor coefficients from the defining finite product,
parses the Lean certificate tables only for comparison, and uses Python exact
integers/Fraction throughout.
"""

from __future__ import annotations

import hashlib
import json
import re
from fractions import Fraction
from math import factorial, isqrt, prod
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
ROWS = (5, 7, 9, 11, 13, 15)
ROW_A = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
TARGET = 10**120
COEFFICIENT_BOUND = 10**12
SECOND_OBSTRUCTION_BOUND = 10**30
PRIME_LOSS_BOUND = 59_049
TWO_PRIME_LOSS_BOUND = PRIME_LOSS_BOUND**2

CONCENTRATION_SOURCE = ROOT / "ErdosProblems/Erdos686GlobalResidualConcentration.lean"
TWO_PRIME_SOURCE = ROOT / "ErdosProblems/Erdos686GlobalResidualTwoPrime.lean"
SECOND_LIFT_SOURCE = ROOT / "ErdosProblems/Erdos686TwoPrimeSecondLift.lean"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    return all(value % divisor for divisor in range(2, isqrt(value) + 1))


def primes_through(bound: int) -> list[int]:
    return [value for value in range(2, bound + 1) if is_prime(value)]


def factorization(value: int) -> dict[int, int]:
    if value <= 0:
        raise ValueError("factorization requires a positive integer")
    result: dict[int, int] = {}
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        while remaining % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            remaining //= divisor
        divisor += 1
    if remaining > 1:
        result[remaining] = result.get(remaining, 0) + 1
    return result


def valuation(value: int, prime: int) -> int:
    if value <= 0 or not is_prime(prime):
        raise ValueError("valuation requires a positive integer and a prime")
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def factorial_valuation(k: int, prime: int) -> int:
    """Legendre's formula, independently of factorial construction."""

    total = 0
    power = prime
    while power <= k:
        total += k // power
        power *= prime
    return total


def loss_exponent(prime: int, k: int) -> int:
    value = factorial_valuation(k - 1, prime)
    return (k + value) // 2 if prime == 3 else (value + 1) // 2


def clean_exponent(prime: int, exponent: int, k: int) -> int:
    return max(exponent - loss_exponent(prime, k), 0)


def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
    """Coefficients 0,1,2 of product_{j != owner}(X+j-owner)."""

    if not 1 <= owner <= k:
        raise ValueError("owner outside row")
    coefficients = [1]
    for index in range(1, k + 1):
        if index == owner:
            continue
        offset = index - owner
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return coefficients[0], coefficients[1], coefficients[2]


def local_cofactor(k: int, owner: int, value: int) -> int:
    return prod(
        value + index - owner
        for index in range(1, k + 1)
        if index != owner
    )


def parse_second_table() -> dict[tuple[int, int], tuple[int, int]]:
    text = SECOND_LIFT_SOURCE.read_text()
    section = text.split("def secondCoefficientTable", 1)[1].split("| _, _ =>", 1)[0]
    pattern = re.compile(
        r"\|\s*(\d+)\s*,\s*(\d+)\s*=>\s*\((-?[\d_]+),\s*(-?[\d_]+)\)"
    )
    return {
        (int(k), int(i)): (int(c.replace("_", "")), int(d.replace("_", "")))
        for k, i, c, d in pattern.findall(section)
    }


def parse_third_table() -> dict[tuple[int, int], int]:
    text = TWO_PRIME_SOURCE.read_text()
    section = text.split("def thirdCoefficientTable", 1)[1].split("| _, _ =>", 1)[0]
    pattern = re.compile(r"\|\s*(\d+)\s*,\s*(\d+)\s*=>\s*(-?[\d_]+)")
    return {
        (int(k), int(i)): int(value.replace("_", ""))
        for k, i, value in pattern.findall(section)
    }


def parse_third_index_table() -> dict[tuple[int, int], tuple[int, ...]]:
    text = TWO_PRIME_SOURCE.read_text()
    section = text.split("def thirdIndexTable", 1)[1].split("| _, _ =>", 1)[0]
    pattern = re.compile(r"\|\s*(\d+)\s*,\s*(\d+)\s*=>\s*\{([^}]*)\}")
    result: dict[tuple[int, int], tuple[int, ...]] = {}
    for k, i, body in pattern.findall(section):
        values = tuple(int(value.strip()) for value in body.split(",") if value.strip())
        result[(int(k), int(i))] = values
    return result


def coefficient_certificate() -> dict[str, Any]:
    second_table = parse_second_table()
    third_table = parse_third_table()
    index_table = parse_third_index_table()
    expected_keys = {(k, i) for k in ROWS for i in range(1, k + 1)}
    if set(second_table) != expected_keys:
        raise AssertionError("second coefficient table does not cover exactly 60 owners")
    if set(third_table) != expected_keys:
        raise AssertionError("third coefficient table does not cover exactly 60 owners")
    if set(index_table) != expected_keys:
        raise AssertionError("third index table does not cover exactly 60 owners")

    triples: dict[tuple[int, int], tuple[int, int, int]] = {}
    for key in sorted(expected_keys):
        k, owner = key
        independent = local_coefficients(k, owner)
        if independent[:2] != second_table[key]:
            raise AssertionError(f"second coefficient mismatch at {key}")
        if independent[2] != third_table[key]:
            raise AssertionError(f"third coefficient mismatch at {key}")
        expected_indices = tuple(index for index in range(1, k + 1) if index != owner)
        if index_table[key] != expected_indices:
            raise AssertionError(f"index table mismatch at {key}")
        triples[key] = independent

    max_constant = max((abs(c), key, c) for key, (c, _, _) in triples.items())
    max_linear = max((abs(d), key, d) for key, (_, d, _) in triples.items())
    max_quadratic = max((abs(e), key, e) for key, (_, _, e) in triples.items())
    if max(max_constant[0], max_linear[0], max_quadratic[0]) >= COEFFICIENT_BOUND:
        raise AssertionError("coefficient bound fails")
    if any(e == 0 for _, _, e in triples.values()):
        raise AssertionError("a target quadratic coefficient vanishes")

    canonical = json.dumps(
        [[k, i, *triples[(k, i)]] for k, i in sorted(triples)], separators=(",", ":")
    ).encode()
    return {
        "owner_count": len(triples),
        "second_table_exact": True,
        "third_table_exact": True,
        "index_table_exact": True,
        "all_quadratics_nonzero": True,
        "max_abs_constant": max_constant,
        "max_abs_linear": max_linear,
        "max_abs_quadratic": max_quadratic,
        "canonical_triples_sha256": hashlib.sha256(canonical).hexdigest(),
    }


def owner_pair_certificate() -> dict[str, Any]:
    same_owner = 0
    distinct_owner = 0
    center_touching_distinct = 0
    simultaneous_zero = 0
    generic_determinant = 0
    simultaneous_witnesses: list[dict[str, int]] = []
    for k in ROWS:
        center = (k + 1) // 2
        for i in range(1, k + 1):
            ci, di, _ = local_coefficients(k, i)
            for j in range(1, k + 1):
                if i == j:
                    same_owner += 1
                    continue
                distinct_owner += 1
                if i == center or j == center:
                    center_touching_distinct += 1
                cj, dj, _ = local_coefficients(k, j)
                determinant = cj * di + ci * dj
                if determinant:
                    generic_determinant += 1
                    continue
                simultaneous_zero += 1
                if j != k + 1 - i:
                    raise AssertionError("non-reflected simultaneous-zero pair")
                delta = i - j
                slope = Fraction(-4 * di * delta, ci)
                if slope <= 0:
                    raise AssertionError("simultaneous-zero slope is not positive")
                # slope = ab/g^2.  Choosing g=denominator and ab=num*den
                # gives an exact positive integral witness for both zeros.
                g = slope.denominator
                ab = slope.numerator * slope.denominator
                left = ci * ab + 4 * di * g * g * delta
                right = cj * ab - 4 * dj * g * g * delta
                if left != 0 or right != 0:
                    raise AssertionError("constructed simultaneous-zero witness failed")
                simultaneous_witnesses.append(
                    {"k": k, "i": i, "j": j, "g": g, "ab": ab}
                )
    if same_owner != 60 or distinct_owner != 610:
        raise AssertionError("owner partition count changed")
    if center_touching_distinct != 108:
        raise AssertionError("center branch count changed")
    if simultaneous_zero != 54 or generic_determinant != 556:
        raise AssertionError("simultaneous-zero partition count changed")
    return {
        "same_owner_cases": same_owner,
        "ordered_distinct_owner_cases": distinct_owner,
        "center_touching_distinct_cases": center_touching_distinct,
        "generic_determinant_cases": generic_determinant,
        "simultaneous_zero_cases": simultaneous_zero,
        "all_simultaneous_zero_pairs_reflected": True,
        "all_simultaneous_zero_witnesses_exact": True,
        "maximum_simultaneous_witness_ab": max(item["ab"] for item in simultaneous_witnesses),
        "maximum_simultaneous_witness_g": max(item["g"] for item in simultaneous_witnesses),
    }


def paper_pair_bound_certificate() -> dict[str, Any]:
    """Reproduce the sharper pair-by-pair bounds claimed in the findings.

    These bounds are not needed by the final Lean wrapper, which deliberately
    uses looser uniform constants, but they are computational claims in the
    producer report and therefore belong in the hostile reproduction.
    """

    second_records: list[tuple[int, int, int, int]] = []
    nondegenerate_records: list[tuple[int, int, int, int]] = []
    reflected_records: list[tuple[int, int, int, int]] = []
    row_reports: dict[int, dict[str, int]] = {}
    for k in ROWS:
        A = ROW_A[k]
        G = prod(
            prime ** loss_exponent(prime, k) for prime in primes_through(k - 1)
        )
        row_second: list[int] = []
        row_nondegenerate: list[int] = []
        row_reflected: list[int] = []
        for i in range(1, k + 1):
            ci, di, ei = local_coefficients(k, i)
            for j in range(1, k + 1):
                if i == j:
                    continue
                cj, dj, ej = local_coefficients(k, j)
                delta = i - j
                determinant = cj * di + ci * dj
                # This bound applies to every pair whenever at least one
                # second obstruction is nonzero.  A determinant-zero pair is
                # still eligible away from its exact simultaneous-zero locus.
                majorant = max(
                    3 * (abs(ci) * A**2 + 4 * abs(di) * abs(delta)),
                    3 * (abs(cj) * A**2 + 4 * abs(dj) * abs(delta)),
                )
                bound = A * majorant**2 * G**6
                second_records.append((bound, k, i, j))
                row_second.append(bound)
                if determinant:
                    nondegenerate_records.append((bound, k, i, j))
                    row_nondegenerate.append(bound)
                elif i < j:
                    bound = 3600 * abs(delta) ** 2 * abs(ei * ej) * G**7
                    reflected_records.append((bound, k, i, j))
                    row_reflected.append(bound)
        row_reports[k] = {
            "second_bound_pair_count": len(row_second),
            "nondegenerate_pair_count": len(row_nondegenerate),
            "reflected_unordered_count": len(row_reflected),
            "maximum_second_bound": max(row_second),
            "maximum_nondegenerate_bound": max(row_nondegenerate),
            "maximum_reflected_third_bound": max(row_reflected),
        }
    maximum_second = max(second_records)
    maximum_nondegenerate = max(nondegenerate_records)
    maximum_reflected = max(reflected_records)
    if maximum_second[0] >= TARGET or maximum_reflected[0] >= TARGET:
        raise AssertionError("a sharper paper pair bound reaches the cutoff")
    return {
        "ordered_second_bound_pairs": len(second_records),
        "ordered_nondegenerate_pairs": len(nondegenerate_records),
        "unordered_reflected_pairs": len(reflected_records),
        "maximum_second": maximum_second,
        "maximum_nondegenerate": maximum_nondegenerate,
        "maximum_reflected_third": maximum_reflected,
        "rows": row_reports,
        "all_below_target": True,
    }


def loss_certificate() -> dict[str, Any]:
    candidate_primes = primes_through(43)
    rows: dict[int, dict[str, Any]] = {}
    for k in ROWS:
        factors = {prime: prime ** loss_exponent(prime, k) for prime in candidate_primes}
        active = {prime: value for prime, value in factors.items() if value != 1}
        if factors[2] > 64:
            raise AssertionError("p=2 exceeds non-three bound")
        if factors[3] > PRIME_LOSS_BOUND:
            raise AssertionError("p=3 exceeds three bound")
        if any(value > 64 for prime, value in factors.items() if prime != 3):
            raise AssertionError("non-three prime loss exceeds 64")
        aggregate = prod(active.values())
        distinct_pair_max = max(
            factors[p] * factors[q]
            for p in candidate_primes
            for q in candidate_primes
            if p != q
        )
        if distinct_pair_max > TWO_PRIME_LOSS_BOUND:
            raise AssertionError("two-prime loss exceeds Lean uniform bound")
        rows[k] = {
            "active_loss_factors": active,
            "aggregate_all_small_primes": aggregate,
            "max_distinct_pair_loss": distinct_pair_max,
            "p2_loss": factors[2],
            "p3_loss": factors[3],
        }
    return {
        "rows": rows,
        "uniform_prime_loss_bound": PRIME_LOSS_BOUND,
        "uniform_two_prime_loss_bound": TWO_PRIME_LOSS_BOUND,
        "all_nonthree_losses_at_most_64": True,
        "all_three_losses_at_most_59049": True,
        "all_primes_above_15_have_unit_loss": all(
            loss_exponent(prime, k) == 0
            for prime in candidate_primes
            if prime > 15
            for k in ROWS
        ),
    }


def residuals(k: int, n: int, d: int) -> list[int]:
    return [3 * (n + i) - d for i in range(1, k + 1)]


def concentration_owner(k: int, n: int, d: int, prime: int) -> int:
    values = residuals(k, n, d)
    if prime == 3:
        if d % 3:
            raise ValueError("p=3 owner requires 3|d")
        reduced = [n - d // 3 + i for i in range(1, k + 1)]
        return max(range(1, k + 1), key=lambda i: valuation(reduced[i - 1], prime))
    return max(range(1, k + 1), key=lambda i: valuation(values[i - 1], prime))


def check_clean_component(k: int, n: int, d: int, prime: int, exponent: int) -> int:
    owner = concentration_owner(k, n, d, prime)
    retained = clean_exponent(prime, exponent, k)
    clean = prime**retained
    residual = 3 * (n + owner) - d
    assert d % clean == 0
    assert (n + owner) % clean == 0
    assert residual % (clean * clean) == 0
    assert prime**exponent <= prime ** loss_exponent(prime, k) * clean
    return owner


def concentration_certificate() -> dict[str, Any]:
    """Independent finite stress test with ranges different from producer's."""

    premise_count = 0
    component_count = 0
    p2_count = 0
    p3_count = 0
    p2_p3_same_owner = 0
    p2_p3_distinct_owner = 0
    center_owner_count = 0
    # `n>2d` is a proved consequence of the equation in the large-gap branch.
    for k in ROWS:
        for d in range(k, 97):
            for n in range(2 * d + 1, 241):
                values = residuals(k, n, d)
                if min(values) <= 0 or prod(values) % (d * d):
                    continue
                premise_count += 1
                owners: dict[int, int] = {}
                for prime, exponent in factorization(d).items():
                    owner = check_clean_component(k, n, d, prime, exponent)
                    owners[prime] = owner
                    component_count += 1
                    if owner == (k + 1) // 2:
                        center_owner_count += 1
                    if prime == 2:
                        p2_count += 1
                    if prime == 3:
                        p3_count += 1
                if 2 in owners and 3 in owners:
                    if owners[2] == owners[3]:
                        p2_p3_same_owner += 1
                    else:
                        p2_p3_distinct_owner += 1
    if not all(
        value > 0
        for value in (
            premise_count,
            component_count,
            p2_count,
            p3_count,
            p2_p3_same_owner,
            p2_p3_distinct_owner,
            center_owner_count,
        )
    ):
        raise AssertionError("finite concentration stress test missed a required branch")
    return {
        "range": {"d_min": "k", "d_max": 96, "n_min": "2*d+1", "n_max": 240},
        "global_square_premises": premise_count,
        "clean_components_checked": component_count,
        "p2_components_checked": p2_count,
        "p3_components_checked": p3_count,
        "p2_p3_same_owner_cases": p2_p3_same_owner,
        "p2_p3_distinct_owner_cases": p2_p3_distinct_owner,
        "center_owner_components": center_owner_count,
    }


def two_three_decomposition_certificate() -> dict[str, Any]:
    checked = 0
    clean_unit_p = 0
    clean_unit_q = 0
    for k in ROWS:
        for p, q in ((2, 3), (3, 2)):
            for e in range(1, loss_exponent(p, k) + 5):
                for f in range(1, loss_exponent(q, k) + 5):
                    tp = clean_exponent(p, e, k)
                    tq = clean_exponent(q, f, k)
                    P, Q = p**tp, q**tq
                    lp, lq = p ** (e - tp), q ** (f - tq)
                    g = lp * lq
                    d = p**e * q**f
                    assert d == g * P * Q
                    assert g <= TWO_PRIME_LOSS_BOUND
                    assert P > 0 and Q > 0
                    assert all(P % divisor or Q % divisor for divisor in range(2, min(P, Q) + 1))
                    clean_unit_p += P == 1
                    clean_unit_q += Q == 1
                    checked += 1
    return {
        "ordered_p2_p3_exponent_cases": checked,
        "first_clean_component_unit_cases": clean_unit_p,
        "second_clean_component_unit_cases": clean_unit_q,
        "all_exact_decompositions": True,
        "all_cofactors_within_uniform_bound": True,
    }


def taylor_remainder_certificate() -> dict[str, Any]:
    checks = 0
    third_algebra_checks = 0
    for k in ROWS:
        for owner in range(1, k + 1):
            c, d, e = local_coefficients(k, owner)
            for value in range(-17, 18):
                remainder = local_cofactor(k, owner, value) - c - d * value - e * value**2
                if value == 0:
                    assert remainder == 0
                else:
                    assert remainder % value**3 == 0
                checks += 1
            # Independently check the exact polynomial congruence behind the
            # coefficient 20 over a broad signed box.
            for h in (1, 2, 3, 5, 7):
                for x in range(-5, 6):
                    for m in range(-5, 6):
                        if (3 * x - m) % h:
                            continue
                        a = (3 * x - m) // h
                        t = -c * a + d * ((x + m) ** 2 - 4 * x**2) + h * e * (
                            (x + m) ** 3 - 4 * x**3
                        )
                        obstruction = -3 * (3 * c * a - 4 * d * m**2) + 20 * e * h * m**3
                        assert (9 * t - obstruction) % (h * h) == 0
                        third_algebra_checks += 1
    return {
        "third_order_remainder_checks": checks,
        "third_algebra_congruence_checks": third_algebra_checks,
        "signed_values_included": True,
    }


def numeric_cutoff_certificate() -> dict[str, Any]:
    second_inside_coefficient = 3 * (
        COEFFICIENT_BOUND * 35**2 + 4 * COEFFICIENT_BOUND * 15
    )
    same_owner = 35 * TWO_PRIME_LOSS_BOUND**2
    generic = 35 * SECOND_OBSTRUCTION_BOUND**2 * TWO_PRIME_LOSS_BOUND**6
    third = 400 * COEFFICIENT_BOUND**2 * 35**2 * TWO_PRIME_LOSS_BOUND**9
    if not second_inside_coefficient < SECOND_OBSTRUCTION_BOUND:
        raise AssertionError("second obstruction coefficient does not fit")
    if not same_owner < TARGET or not generic < TARGET or not third < TARGET:
        raise AssertionError("one of the uniform numeric cutoffs fails")
    return {
        "second_obstruction_coefficient": second_inside_coefficient,
        "second_obstruction_coefficient_margin": SECOND_OBSTRUCTION_BOUND
        - second_inside_coefficient,
        "same_owner_bound": same_owner,
        "generic_nonzero_second_bound": generic,
        "simultaneous_zero_third_bound": third,
        "target": TARGET,
        "same_owner_slack": TARGET - same_owner,
        "generic_slack": TARGET - generic,
        "third_slack": TARGET - third,
        "all_strict": True,
    }


def forbidden_tokens() -> dict[str, list[int]]:
    """Find actual code tokens after removing comments and strings coarsely."""

    result: dict[str, list[int]] = {}
    patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "axiom": re.compile(r"^\s*axiom\b"),
        "unsafe": re.compile(r"^\s*unsafe\b"),
    }
    for path in (CONCENTRATION_SOURCE, TWO_PRIME_SOURCE, SECOND_LIFT_SOURCE):
        lines = path.read_text().splitlines()
        in_block = False
        sanitized: list[tuple[int, str]] = []
        for number, original in enumerate(lines, 1):
            line = original
            # Sufficient for these sources: block-comment delimiters are not
            # nested on code lines, and forbidden words in prose must not count.
            if in_block:
                if "-/" in line:
                    line = line.split("-/", 1)[1]
                    in_block = False
                else:
                    continue
            while "/-" in line:
                before, after = line.split("/-", 1)
                if "-/" in after:
                    line = before + after.split("-/", 1)[1]
                else:
                    line = before
                    in_block = True
                    break
            line = line.split("--", 1)[0]
            line = re.sub(r'"(?:\\.|[^"\\])*"', '""', line)
            sanitized.append((number, line))
        for name, pattern in patterns.items():
            hits = [number for number, line in sanitized if pattern.search(line)]
            if hits:
                result[f"{path.name}:{name}"] = hits
    return result


def report() -> dict[str, Any]:
    forbidden = forbidden_tokens()
    if forbidden:
        raise AssertionError(f"forbidden code tokens found: {forbidden}")
    return {
        "source_sha256": {
            CONCENTRATION_SOURCE.name: sha256(CONCENTRATION_SOURCE),
            TWO_PRIME_SOURCE.name: sha256(TWO_PRIME_SOURCE),
            SECOND_LIFT_SOURCE.name: sha256(SECOND_LIFT_SOURCE),
        },
        "forbidden_code_tokens": forbidden,
        "coefficients": coefficient_certificate(),
        "owner_pairs": owner_pair_certificate(),
        "paper_pair_bounds": paper_pair_bound_certificate(),
        "losses": loss_certificate(),
        "concentration_stress": concentration_certificate(),
        "p2_p3_decompositions": two_three_decomposition_certificate(),
        "taylor": taylor_remainder_certificate(),
        "cutoffs": numeric_cutoff_certificate(),
    }


def main() -> None:
    print(json.dumps(report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
