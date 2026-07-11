#!/usr/bin/env python3
"""Independent exact verifier for the Erdős 686 two-owner aggregate module.

Nothing is imported from the producer verifier.  All calculations use exact
Python integers, and the boundary checks include zero moduli/factors wherever
the corresponding public Lean theorem permits them.
"""

from __future__ import annotations

import hashlib
import json
import re
from itertools import product
from math import gcd, isqrt
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "ErdosProblems/Erdos686TwoOwnerAggregate.lean"
ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
TARGET = 10**120
SECOND_BOUND = 10**16
COEFFICIENT_BOUND = 10**12
DISTANCE_BOUND = 15


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


def primes_below(bound: int) -> list[int]:
    return [value for value in range(2, bound) if is_prime(value)]


def factorial_valuation(n: int, prime: int) -> int:
    total = 0
    power = prime
    while power <= n:
        total += n // power
        power *= prime
    return total


def loss_exponent(prime: int, k: int) -> int:
    value = factorial_valuation(k - 1, prime)
    return (k + value) // 2 if prime == 3 else (value + 1) // 2


def aggregate_loss(k: int) -> int:
    result = 1
    for prime in primes_below(k):
        result *= prime ** loss_exponent(prime, k)
    return result


def parse_lean_loss_table() -> dict[int, int]:
    text = SOURCE.read_text()
    section = text.split("def targetAggregateLoss", 1)[1].split("| _ =>", 1)[0]
    return {
        int(k): int(value.replace("_", ""))
        for k, value in re.findall(r"\|\s*(\d+)\s*=>\s*([\d_]+)", section)
    }


def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
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


def row_pair_certificate() -> dict[str, Any]:
    rows: dict[int, dict[str, Any]] = {}
    all_second: list[tuple[int, int, int, int]] = []
    all_exact_generic: list[tuple[int, int, int, int]] = []
    all_exact_cubic: list[tuple[int, int, int, int]] = []
    for k, A in ROWS.items():
        G = aggregate_loss(k)
        second: list[tuple[int, int, int]] = []
        exact_generic: list[tuple[int, int, int]] = []
        exact_cubic: list[tuple[int, int, int]] = []
        for i in range(1, k + 1):
            ci, di, ei = local_coefficients(k, i)
            for j in range(1, k + 1):
                if i == j:
                    continue
                cj, dj, ej = local_coefficients(k, j)
                delta = abs(i - j)
                majorant = max(
                    3 * (abs(ci) * A**2 + 4 * abs(di) * delta),
                    3 * (abs(cj) * A**2 + 4 * abs(dj) * delta),
                )
                generic = A * majorant**2 * G**6
                cubic = 3600 * delta**2 * abs(ei * ej) * G**7
                second.append((majorant, i, j))
                exact_generic.append((generic, i, j))
                exact_cubic.append((cubic, i, j))
                all_second.append((majorant, k, i, j))
                all_exact_generic.append((generic, k, i, j))
                all_exact_cubic.append((cubic, k, i, j))
        one_owner = 35 * G**2
        uniform_generic = 35 * SECOND_BOUND**2 * G**6
        uniform_cubic = 3600 * DISTANCE_BOUND**2 * COEFFICIENT_BOUND**2 * G**7
        if not all(value < TARGET for value in (one_owner, uniform_generic, uniform_cubic)):
            raise AssertionError(f"uniform cutoff failed in row {k}")
        if max(exact_generic)[0] >= TARGET or max(exact_cubic)[0] >= TARGET:
            raise AssertionError(f"exact pair cutoff failed in row {k}")
        rows[k] = {
            "A": A,
            "aggregate_loss": G,
            "ordered_pair_count": len(second),
            "maximum_second_majorant": max(second),
            "maximum_exact_generic": max(exact_generic),
            "maximum_exact_cubic": max(exact_cubic),
            "one_owner_cutoff": one_owner,
            "uniform_generic_cutoff": uniform_generic,
            "uniform_cubic_cutoff": uniform_cubic,
        }
    if sum(row["ordered_pair_count"] for row in rows.values()) != 610:
        raise AssertionError("ordered owner-pair count changed")
    return {
        "rows": rows,
        "ordered_pair_count": 610,
        "global_maximum_second_majorant": max(all_second),
        "global_maximum_exact_generic": max(all_exact_generic),
        "global_maximum_exact_cubic": max(all_exact_cubic),
    }


def coarse_obstruction_certificate() -> dict[str, int | bool]:
    coefficient = 3 * (
        COEFFICIENT_BOUND * 35**2
        + 4 * COEFFICIENT_BOUND * DISTANCE_BOUND
    )
    return {
        "coarse_coefficient": coefficient,
        "bound": SECOND_BOUND,
        "margin": SECOND_BOUND - coefficient,
        "strict": coefficient < SECOND_BOUND,
    }


def nat_divides(divisor: int, value: int) -> bool:
    if divisor < 0 or value < 0:
        raise ValueError("natural divisibility expects nonnegative inputs")
    return value == 0 if divisor == 0 else value % divisor == 0


def cancellation_boundary_certificate(limit: int = 20) -> dict[str, Any]:
    checked = 0
    categories = {name: 0 for name in ("m_zero", "b_zero", "K_zero", "D_zero")}
    for m, b, K, D in product(range(limit + 1), repeat=4):
        if not nat_divides(m, K * b):
            continue
        if not nat_divides(gcd(m, b), D):
            continue
        checked += 1
        if not nat_divides(m, K * D):
            raise AssertionError((m, b, K, D))
        categories["m_zero"] += m == 0
        categories["b_zero"] += b == 0
        categories["K_zero"] += K == 0
        categories["D_zero"] += D == 0
    if not all(categories.values()):
        raise AssertionError("a zero cancellation boundary was not exercised")
    return {"limit": limit, "premise_cases": checked, **categories}


def pell_gcd_boundary_certificate(limit: int = 12) -> dict[str, Any]:
    checked = 0
    signs = {"negative_delta": 0, "zero_delta": 0, "positive_delta": 0}
    zero_fields = {name: 0 for name in ("P_zero", "Q_zero", "a_zero", "b_zero")}
    for a, b, P, Q in product(range(limit + 1), repeat=4):
        difference = a * P**2 - b * Q**2
        if difference % 3:
            continue
        delta = difference // 3
        scale = 3 * abs(delta)
        if not nat_divides(gcd(P, b), scale):
            raise AssertionError(("left", a, b, P, Q, delta))
        if not nat_divides(gcd(Q, a), scale):
            raise AssertionError(("right", a, b, P, Q, delta))
        checked += 1
        signs["negative_delta"] += delta < 0
        signs["zero_delta"] += delta == 0
        signs["positive_delta"] += delta > 0
        zero_fields["P_zero"] += P == 0
        zero_fields["Q_zero"] += Q == 0
        zero_fields["a_zero"] += a == 0
        zero_fields["b_zero"] += b == 0
    if not all((*signs.values(), *zero_fields.values())):
        raise AssertionError("a Pell boundary was not exercised")
    return {"limit": limit, "pell_cases": checked, **signs, **zero_fields}


def refined_cubic_boundary_certificate() -> dict[str, Any]:
    checked = 0
    categories = {
        name: 0
        for name in (
            "negative_E",
            "zero_E",
            "positive_E",
            "negative_delta",
            "zero_delta",
            "positive_delta",
            "P_one",
            "Q_zero",
            "a_zero",
        )
    }
    factor_three_needed: tuple[int, ...] | None = None
    for a in range(0, 11):
        for b in range(1, 11):
            for P in range(1, 11):
                for Q in range(0, 11):
                    if gcd(P, Q) != 1:
                        continue
                    difference = a * P**2 - b * Q**2
                    if difference % 3:
                        continue
                    delta = difference // 3
                    for g in range(1, 6):
                        for E in range(-5, 6):
                            raw = 20 * abs(E) * b * g**3
                            if not nat_divides(P, raw):
                                continue
                            refined = 60 * abs(delta) * abs(E) * g**3
                            if not nat_divides(P, refined):
                                raise AssertionError((a, b, P, Q, delta, g, E))
                            checked += 1
                            categories["negative_E"] += E < 0
                            categories["zero_E"] += E == 0
                            categories["positive_E"] += E > 0
                            categories["negative_delta"] += delta < 0
                            categories["zero_delta"] += delta == 0
                            categories["positive_delta"] += delta > 0
                            categories["P_one"] += P == 1
                            categories["Q_zero"] += Q == 0
                            categories["a_zero"] += a == 0
                            missing_three = 20 * abs(delta) * abs(E) * g**3
                            if factor_three_needed is None and not nat_divides(P, missing_three):
                                factor_three_needed = (a, b, P, Q, delta, g, E)
    if not all(categories.values()):
        raise AssertionError("a refined-cubic sign/zero boundary was not exercised")
    if factor_three_needed is None:
        raise AssertionError("no witness shows the factor three is load-bearing")
    return {
        "refined_cases": checked,
        "factor_three_needed_witness": factor_three_needed,
        **categories,
    }


def same_owner_boundary_certificate() -> dict[str, Any]:
    checked = 0
    p_one = q_one = both_one = 0
    for k, A in ROWS.items():
        for g in range(1, 21):
            for P in range(1, 13):
                for Q in range(1, 13):
                    if gcd(P, Q) != 1:
                        continue
                    d = g * P * Q
                    for multiplier in range(1, 11):
                        residual = multiplier * (P * Q) ** 2
                        if not residual < A * d:
                            continue
                        if not d < A * g**2:
                            raise AssertionError((k, A, g, P, Q, residual))
                        checked += 1
                        p_one += P == 1
                        q_one += Q == 1
                        both_one += P == Q == 1
    if min(checked, p_one, q_one, both_one) <= 0:
        raise AssertionError("same-owner unit boundaries not reached")
    return {
        "premise_cases": checked,
        "P_one_cases": p_one,
        "Q_one_cases": q_one,
        "both_one_cases": both_one,
    }


def zdivides(divisor: int, value: int) -> bool:
    divisor = abs(divisor)
    return value == 0 if divisor == 0 else value % divisor == 0


def abstract_premises_hold(
    k: int, A: int, g: int, P: int, Q: int, i: int, j: int, a: int, b: int
) -> bool:
    if min(g, P, Q, a, b) <= 0 or gcd(P, Q) != 1 or i == j:
        return False
    delta = i - j
    if a * P**2 - b * Q**2 != 3 * delta:
        return False
    if not (a * P < A * g * Q and b * Q < A * g * P and a * b < A**2 * g**2):
        return False
    ci, di, ei = local_coefficients(k, i)
    cj, dj, ej = local_coefficients(k, j)
    p_second = 3 * ci * a - 4 * di * (g * Q) ** 2
    q_second = 3 * cj * b - 4 * dj * (g * P) ** 2
    p_third = -3 * p_second + 20 * ei * P * (g * Q) ** 3
    q_third = -3 * q_second + 20 * ej * Q * (g * P) ** 3
    return (
        zdivides(P, p_second)
        and zdivides(Q, q_second)
        and zdivides(P**2, p_third)
        and zdivides(Q**2, q_third)
    )


def unit_bucket_abstract_certificate() -> dict[str, Any]:
    both_unit = p_unit = q_unit = 0
    delta_signs = {"negative": 0, "positive": 0}
    # P=Q=1: the local divisibilities are automatic; choose exact Pell data.
    for k, A in ROWS.items():
        for i in range(1, k + 1):
            for j in range(1, k + 1):
                if i == j:
                    continue
                delta = i - j
                for g in range(1, 6):
                    for b in range(1, 21):
                        a = b + 3 * delta
                        if a <= 0:
                            continue
                        if abstract_premises_hold(k, A, g, 1, 1, i, j, a, b):
                            both_unit += 1
                            delta_signs["negative"] += delta < 0
                            delta_signs["positive"] += delta > 0
    # One unit bucket: search exact abstract fixtures in the k=5 row.
    k, A = 5, ROWS[5]
    for i in range(1, k + 1):
        for j in range(1, k + 1):
            if i == j:
                continue
            delta = i - j
            for g in range(1, 13):
                for other in range(2, 21):
                    for b in range(1, 81):
                        a = b * other**2 + 3 * delta
                        if a > 0 and abstract_premises_hold(k, A, g, 1, other, i, j, a, b):
                            p_unit += 1
                    for a in range(1, 81):
                        b = a * other**2 - 3 * delta
                        if b > 0 and abstract_premises_hold(k, A, g, other, 1, i, j, a, b):
                            q_unit += 1
    if min(both_unit, p_unit, q_unit, *delta_signs.values()) <= 0:
        raise AssertionError("an abstract unit-bucket boundary was not exercised")
    return {
        "both_unit_fixtures": both_unit,
        "P_unit_only_fixtures": p_unit,
        "Q_unit_only_fixtures": q_unit,
        "both_unit_negative_delta": delta_signs["negative"],
        "both_unit_positive_delta": delta_signs["positive"],
    }


def factorization(value: int) -> dict[int, int]:
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


def finite_grouping_arithmetic_certificate(max_d: int = 2000) -> dict[str, Any]:
    checked = 0
    empty_clean_buckets = 0
    unit_left = unit_right = 0
    for k in ROWS:
        G = aggregate_loss(k)
        for d in range(1, max_d + 1):
            factors = list(factorization(d).items())
            for assignment in product((0, 1), repeat=len(factors)):
                g = P = Q = 1
                for (prime, exponent), side in zip(factors, assignment):
                    retained = max(exponent - loss_exponent(prime, k), 0)
                    g *= prime ** (exponent - retained)
                    if side == 0:
                        P *= prime**retained
                    else:
                        Q *= prime**retained
                if d != g * P * Q or gcd(P, Q) != 1 or g > G:
                    raise AssertionError((k, d, assignment, g, P, Q, G))
                checked += 1
                empty_clean_buckets += P == Q == 1
                unit_left += P == 1
                unit_right += Q == 1
    return {
        "max_d": max_d,
        "assignment_cases": checked,
        "both_clean_buckets_unit": empty_clean_buckets,
        "left_bucket_unit": unit_left,
        "right_bucket_unit": unit_right,
    }


def strip_lean_comments_and_strings(text: str) -> str:
    output: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            char = text[i]
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                output.append(" ")
                i += 1
        elif text.startswith("/-", i):
            block_depth = 1
            output.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            output.append(text[i])
            i += 1
    return "".join(output)


def source_gate_certificate() -> dict[str, Any]:
    code = strip_lean_comments_and_strings(SOURCE.read_text())
    forbidden = {}
    for token, pattern in {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "axiom": r"^\s*axiom\b",
        "unsafe": r"^\s*unsafe\b",
    }.items():
        lines = [
            number
            for number, line in enumerate(code.splitlines(), 1)
            if re.search(pattern, line)
        ]
        if lines:
            forbidden[token] = lines
    public_theorems = re.findall(r"(?m)^theorem\s+([A-Za-z0-9_']+)", code)
    private_declarations = re.findall(
        r"(?m)^private\s+(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)", code
    )
    return {
        "source_sha256": sha256(SOURCE),
        "forbidden": forbidden,
        "public_theorems": public_theorems,
        "public_theorem_count": len(public_theorems),
        "private_declarations": private_declarations,
    }


def report() -> dict[str, Any]:
    lean_table = parse_lean_loss_table()
    recomputed = {k: aggregate_loss(k) for k in ROWS}
    if lean_table != recomputed:
        raise AssertionError((lean_table, recomputed))
    source = source_gate_certificate()
    if source["forbidden"] or source["public_theorem_count"] != 9:
        raise AssertionError(source)
    return {
        "source": source,
        "loss_table": {"lean": lean_table, "recomputed": recomputed},
        "coarse_obstruction": coarse_obstruction_certificate(),
        "pairs": row_pair_certificate(),
        "generic_cancellation": cancellation_boundary_certificate(),
        "pell_gcd": pell_gcd_boundary_certificate(),
        "refined_cubic": refined_cubic_boundary_certificate(),
        "same_owner": same_owner_boundary_certificate(),
        "unit_buckets": unit_bucket_abstract_certificate(),
        "finite_grouping_arithmetic": finite_grouping_arithmetic_certificate(),
    }


def main() -> None:
    print(json.dumps(report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
