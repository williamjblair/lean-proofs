#!/usr/bin/env python3
"""Independent hostile verifier for the frozen two-owner grouping bridge.

This file intentionally does not import the producer verifier.  It rederives
the exponent split, aggregate row losses, finite owner cover, and grouped
divisibility arithmetic with Python integers.  It also checks the frozen Lean
surface and the exact scoping of the final existential/universal statement.
"""

from __future__ import annotations

import hashlib
import json
import math
import random
import re
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / "ErdosProblems/Erdos686TwoOwnerGrouping.lean"
AGGREGATE = ROOT / "ErdosProblems/Erdos686TwoOwnerAggregate.lean"
CONCENTRATION = ROOT / "ErdosProblems/Erdos686GlobalResidualConcentration.lean"
AUDIT_LEAN = ROOT / "ErdosProblems/Erdos686TwoOwnerGroupingAudit.lean"

EXPECTED_CANDIDATE_SHA256 = (
    "63799ee4a2cc6fc0632776c231ac0961ddc038d60348c1b2fc43def3803797ef"
)
EXPECTED_AGGREGATE_SHA256 = (
    "35959fee7b3080b2d0a91885a7a465455fcbed4ead9ecc1d652024ec7eabe009"
)
EXPECTED_CONCENTRATION_SHA256 = (
    "495981605282c4a1963f95bdce0788b4baba6cfa05c8be00b8c57154f49f9e24"
)
ROWS = (5, 7, 9, 11, 13, 15)
EXPECTED_ROW_LOSSES = {
    5: 108,
    7: 1_620,
    9: 136_080,
    11: 1_224_720,
    13: 242_494_560,
    15: 18_914_575_680,
}
EXPECTED_PUBLIC_THEOREMS = (
    "globalResidualGroupedLossFactor_mul_clean",
    "globalResidualGroupedLossFactor_dvd_targetAggregateLoss",
    "globalResidualGroupedLoss_le_targetAggregateLoss",
    "globalResidualGrouped_decomposition",
    "globalResidualGroupedLeft_coprime_right",
    "globalResidualGroupedLeft_dvd_factor",
    "globalResidualGroupedRight_dvd_factor",
    "globalResidualGroupedLeft_square_dvd_residual",
    "globalResidualGroupedRight_square_dvd_residual",
    "hasAtMostTwoGlobalResidualOwners_of_assignment",
    "exists_globalResidualOwnerAssignment",
    "two_owner_range_equation_below_cutoff",
    "exists_globalResidualOwnerAssignment_not_two_cover",
)


class OutsideCover(ValueError):
    """A nonzero cleaned component has an owner outside the proposed cover."""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_prime(value: int) -> bool:
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


def primes_up_to(bound: int) -> list[int]:
    return [value for value in range(2, bound + 1) if is_prime(value)]


@lru_cache(maxsize=None)
def factorization(value: int) -> tuple[tuple[int, int], ...]:
    if value <= 0:
        raise ValueError("positive factorization only")
    factors: list[tuple[int, int]] = []
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        if exponent:
            factors.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        factors.append((remaining, 1))
    return tuple(factors)


def factorial_valuation(n: int, prime: int) -> int:
    if not is_prime(prime):
        raise ValueError(f"not prime: {prime}")
    total = 0
    power = prime
    while power <= n:
        total += n // power
        power *= prime
    return total


def loss_exponent(prime: int, k: int) -> int:
    valuation = factorial_valuation(k - 1, prime)
    if prime == 3:
        return (k + valuation) // 2
    return (valuation + 1) // 2


def clean_exponent(prime: int, exponent: int, k: int) -> int:
    return max(exponent - loss_exponent(prime, k), 0)


def grouped_loss_exponent(prime: int, exponent: int, k: int) -> int:
    return exponent - clean_exponent(prime, exponent, k)


def aggregate_loss(k: int) -> int:
    answer = 1
    for prime in primes_up_to(k - 1):
        answer *= prime ** loss_exponent(prime, k)
    return answer


def parse_target_loss_table() -> dict[int, int]:
    text = AGGREGATE.read_text()
    body = text.split("def targetAggregateLoss", 1)[1].split("| _ =>", 1)[0]
    return {
        int(row): int(value.replace("_", ""))
        for row, value in re.findall(r"\|\s*(\d+)\s*=>\s*([\d_]+)", body)
    }


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank nested comments, line comments, and strings while preserving lines."""

    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
            continue
        if in_string:
            char = text[index]
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
        elif text.startswith("/-", index):
            depth = 1
            output.extend("  ")
            index += 2
        elif text[index] == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(text[index])
            index += 1
    if depth or in_string:
        raise AssertionError("unterminated Lean comment or string")
    return "".join(output)


def public_theorem_headers(code: str) -> dict[str, str]:
    matches = list(re.finditer(r"(?m)^theorem\s+([A-Za-z0-9_']+)", code))
    headers: dict[str, str] = {}
    for match in matches:
        proof = code.find(":= by", match.end())
        if proof < 0:
            raise AssertionError(f"no proof marker for {match.group(1)}")
        headers[match.group(1)] = code[match.start() : proof]
    return headers


def source_surface_certificate() -> dict[str, Any]:
    raw = CANDIDATE.read_text()
    code = strip_lean_comments_and_strings(raw)
    forbidden: dict[str, list[int]] = {}
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "axiom": r"^\s*axiom\b",
        "unsafe": r"^\s*unsafe\b",
        "opaque": r"^\s*opaque\b",
    }
    for label, pattern in patterns.items():
        lines = [
            number
            for number, line in enumerate(code.splitlines(), 1)
            if re.search(pattern, line)
        ]
        if lines:
            forbidden[label] = lines

    public = tuple(re.findall(r"(?m)^theorem\s+([A-Za-z0-9_']+)", code))
    private = tuple(
        re.findall(
            r"(?m)^private\s+(?:lemma|theorem|def)\s+([A-Za-z0-9_']+)", code
        )
    )
    headers = public_theorem_headers(code)
    private_header_leaks = {
        theorem: tuple(
            name
            for name in private
            if re.search(rf"\b{re.escape(name)}\b", header)
        )
        for theorem, header in headers.items()
    }
    private_header_leaks = {
        theorem: leaks for theorem, leaks in private_header_leaks.items() if leaks
    }

    final_header = headers["exists_globalResidualOwnerAssignment_not_two_cover"]
    quantifier_markers = {
        "existential_owner": "∃ owner : ℕ → ℕ" in final_header,
        "assignment_conjunct": "GlobalResidualOwnerAssignment k n d owner ∧" in final_header,
        "universal_pair": "∀ i j : ℕ" in final_header,
        "same_owner_in_range": "GlobalResidualOwnerRangeAtMostTwo k d owner i j" in final_header,
    }

    audit_code = strip_lean_comments_and_strings(AUDIT_LEAN.read_text())
    audit_forbidden = {
        label: [
            number
            for number, line in enumerate(audit_code.splitlines(), 1)
            if re.search(pattern, line)
        ]
        for label, pattern in patterns.items()
    }
    audit_forbidden = {
        label: lines for label, lines in audit_forbidden.items() if lines
    }
    hostile_python = Path(__file__).read_text()
    imports_producer_verifier = bool(
        re.search(
            r"(?:from|import)\s+compute\.campaign686\.two_owner_grouping_verify",
            hostile_python,
        )
    )

    return {
        "candidate_sha256": sha256(CANDIDATE),
        "aggregate_sha256": sha256(AGGREGATE),
        "concentration_sha256": sha256(CONCENTRATION),
        "audit_lean_sha256": sha256(AUDIT_LEAN),
        "imports": tuple(re.findall(r"(?m)^import\s+([^\s]+)", code)),
        "public_theorems": public,
        "public_theorem_count": len(public),
        "private_declarations": private,
        "private_header_leaks": private_header_leaks,
        "forbidden": forbidden,
        "audit_forbidden": audit_forbidden,
        "imports_producer_verifier": imports_producer_verifier,
        "final_quantifier_markers": quantifier_markers,
    }


def owner_range_at_most_two(
    factors: Sequence[tuple[int, int]],
    owners: Mapping[int, int],
    k: int,
    left_owner: int,
    right_owner: int,
) -> bool:
    if not (1 <= left_owner <= k and 1 <= right_owner <= k):
        return False
    return all(
        clean_exponent(prime, exponent, k) == 0
        or owners[prime] == left_owner
        or owners[prime] == right_owner
        for prime, exponent in factors
    )


def assemble_from_factors(
    k: int,
    factors: Sequence[tuple[int, int]],
    owners: Mapping[int, int],
    left_owner: int,
    right_owner: int,
) -> tuple[int, int, int, tuple[dict[str, int], ...]]:
    loss = left = right = 1
    rows: list[dict[str, int]] = []
    for prime, exponent in factors:
        clean = clean_exponent(prime, exponent, k)
        lost = grouped_loss_exponent(prime, exponent, k)
        owner = owners[prime]
        if clean and owner not in (left_owner, right_owner):
            raise OutsideCover((prime, exponent, clean, owner, left_owner, right_owner))
        loss_factor = prime**lost
        clean_factor = prime**clean
        left_factor = clean_factor if owner == left_owner else 1
        # This is the exact first-owner precedence in the Lean definition.
        right_factor = (
            clean_factor if owner != left_owner and owner == right_owner else 1
        )
        if loss_factor * left_factor * right_factor != prime**exponent:
            raise AssertionError("per-prime exponent split failed")
        loss *= loss_factor
        left *= left_factor
        right *= right_factor
        rows.append(
            {
                "prime": prime,
                "exponent": exponent,
                "clean_exponent": clean,
                "loss_exponent": lost,
                "owner": owner,
                "loss_factor": loss_factor,
                "left_factor": left_factor,
                "right_factor": right_factor,
            }
        )
    return loss, left, right, tuple(rows)


def product_of_factors(factors: Sequence[tuple[int, int]]) -> int:
    answer = 1
    for prime, exponent in factors:
        answer *= prime**exponent
    return answer


def check_pairwise_product_divisibility(
    rows: Sequence[Mapping[str, int]], left: int, right: int
) -> None:
    left_parts = [row["left_factor"] for row in rows if row["left_factor"] > 1]
    right_parts = [row["right_factor"] for row in rows if row["right_factor"] > 1]
    for parts, aggregate, salt in ((left_parts, left, 37), (right_parts, right, 41)):
        for index, first in enumerate(parts):
            for second in parts[index + 1 :]:
                if math.gcd(first, second) != 1:
                    raise AssertionError(("same-bucket noncoprime", first, second))
        lcm = math.lcm(*parts) if parts else 1
        if lcm != aggregate:
            raise AssertionError(("lcm/product mismatch", parts, lcm, aggregate))
        target = lcm * salt
        square_target = lcm**2 * (salt + 2)
        if any(target % part for part in parts):
            raise AssertionError("component factor divisibility fixture failed")
        if any(square_target % (part**2) for part in parts):
            raise AssertionError("component square divisibility fixture failed")
        if target % aggregate or square_target % (aggregate**2):
            raise AssertionError("aggregate divisibility fixture failed")


def validate_covered_fixture(
    k: int,
    factors: Sequence[tuple[int, int]],
    owners: Mapping[int, int],
    left_owner: int,
    right_owner: int,
) -> tuple[int, int, int, tuple[dict[str, int], ...]]:
    loss, left, right, rows = assemble_from_factors(
        k, factors, owners, left_owner, right_owner
    )
    d = product_of_factors(factors)
    row_loss = aggregate_loss(k)
    if d != loss * left * right:
        raise AssertionError(("global decomposition", k, d, loss, left, right))
    if math.gcd(left, right) != 1:
        raise AssertionError(("cross-bucket coprimality", k, d, left, right))
    if row_loss % loss or loss > row_loss:
        raise AssertionError(("aggregate loss", k, d, loss, row_loss))
    for row in rows:
        if row_loss % row["loss_factor"]:
            raise AssertionError(("component loss", k, d, row, row_loss))
        if row["loss_exponent"] != min(
            row["exponent"], loss_exponent(row["prime"], k)
        ):
            raise AssertionError(("truncated exponent split", k, d, row))
        if row["prime"] >= k and row["loss_exponent"] != 0:
            raise AssertionError(("prime-at-least-k loss", k, d, row))
    check_pairwise_product_divisibility(rows, left, right)
    return loss, left, right, rows


def no_two_cover_equivalence_certificate() -> dict[str, int]:
    checked = no_cover = coverable = 0
    primes = (2, 3, 5, 7, 11)
    # Exponents straddle zero/nonzero cleaning in every target row.
    for k in ROWS:
        exponents = tuple(
            loss_exponent(prime, k) if index == 0
            else loss_exponent(prime, k) + 1
            for index, prime in enumerate(primes)
        )
        factors = tuple(zip(primes, exponents))
        for values in product((1, 2, 3, 4), repeat=len(primes)):
            owners = dict(zip(primes, values))
            active = {
                owners[prime]
                for prime, exponent in factors
                if clean_exponent(prime, exponent, k) > 0
            }
            has_cover = any(
                owner_range_at_most_two(factors, owners, k, i, j)
                for i in range(1, k + 1)
                for j in range(1, k + 1)
            )
            if has_cover != (len(active) <= 2):
                raise AssertionError((k, factors, owners, active, has_cover))
            checked += 1
            coverable += has_cover
            no_cover += not has_cover
    if min(checked, coverable, no_cover) <= 0:
        raise AssertionError("quantifier boundary coverage missing")
    return {
        "finite_assignments_checked": checked,
        "coverable_assignments": coverable,
        "not_two_cover_assignments": no_cover,
    }


@lru_cache(maxsize=None)
def exhaustive_small_certificate(max_d: int = 1_500) -> dict[str, Any]:
    counts = {
        "gaps": 0,
        "three_value_maps": 0,
        "covered_maps": 0,
        "rejected_maps": 0,
        "same_owner_maps": 0,
        "same_owner_covered": 0,
        "same_owner_rejected": 0,
        "empty_support": 0,
        "one_prime_support": 0,
        "zero_clean_components": 0,
        "zero_clean_outside_cover": 0,
        "p2_components": 0,
        "p3_components": 0,
        "prime_at_least_k_components": 0,
        "both_buckets_unit": 0,
        "left_bucket_unit": 0,
        "right_bucket_unit": 0,
    }
    max_loss = (0, 1, 0, 0)

    for k in ROWS:
        for d in range(1, max_d + 1):
            factors = factorization(d)
            counts["gaps"] += 1
            counts["empty_support"] += not factors
            counts["one_prime_support"] += len(factors) == 1

            # Every owner value is a legal assignment value because 1,2,3 lie
            # in Icc 1 k for all six rows.  Value 3 is outside the tested cover.
            for values in product((1, 2, 3), repeat=len(factors)):
                counts["three_value_maps"] += 1
                owners = dict(zip((prime for prime, _ in factors), values))
                covered = owner_range_at_most_two(factors, owners, k, 1, 2)
                if not covered:
                    counts["rejected_maps"] += 1
                    try:
                        assemble_from_factors(k, factors, owners, 1, 2)
                    except OutsideCover:
                        pass
                    else:
                        raise AssertionError("nontrivial outside owner was accepted")
                    continue

                counts["covered_maps"] += 1
                loss, left, right, rows = validate_covered_fixture(
                    k, factors, owners, 1, 2
                )
                counts["both_buckets_unit"] += left == right == 1
                counts["left_bucket_unit"] += left == 1
                counts["right_bucket_unit"] += right == 1
                max_loss = max(max_loss, (loss, aggregate_loss(k), k, d))
                for row in rows:
                    counts["zero_clean_components"] += row["clean_exponent"] == 0
                    counts["zero_clean_outside_cover"] += (
                        row["clean_exponent"] == 0 and row["owner"] == 3
                    )
                    counts["p2_components"] += row["prime"] == 2
                    counts["p3_components"] += row["prime"] == 3
                    counts["prime_at_least_k_components"] += row["prime"] >= k

            # Coincident owners force every retained component into the left
            # bucket; zero-clean components may still use another legal owner.
            for values in product((1, 3), repeat=len(factors)):
                counts["same_owner_maps"] += 1
                owners = dict(zip((prime for prime, _ in factors), values))
                covered = owner_range_at_most_two(factors, owners, k, 1, 1)
                if not covered:
                    counts["same_owner_rejected"] += 1
                    try:
                        assemble_from_factors(k, factors, owners, 1, 1)
                    except OutsideCover:
                        pass
                    else:
                        raise AssertionError("same-owner outside component accepted")
                    continue
                counts["same_owner_covered"] += 1
                _loss, _left, right, _rows = validate_covered_fixture(
                    k, factors, owners, 1, 1
                )
                if right != 1:
                    raise AssertionError(("first-owner precedence", k, d, owners, right))

    required = (
        "empty_support",
        "one_prime_support",
        "covered_maps",
        "rejected_maps",
        "same_owner_covered",
        "same_owner_rejected",
        "zero_clean_components",
        "zero_clean_outside_cover",
        "p2_components",
        "p3_components",
        "prime_at_least_k_components",
        "both_buckets_unit",
        "left_bucket_unit",
        "right_bucket_unit",
    )
    if any(counts[key] <= 0 for key in required):
        raise AssertionError({key: counts[key] for key in required})
    return {"max_d": max_d, **counts, "maximum_loss_fixture": max_loss}


@lru_cache(maxsize=None)
def random_large_certificate(cases: int = 5_000, seed: int = 686_20260710) -> dict[str, Any]:
    rng = random.Random(seed)
    prime_pool = tuple(primes_up_to(131))
    max_digits = 0
    p2 = p3 = large_prime = zero_clean = same_owner = 0
    for case in range(cases):
        k = ROWS[case % len(ROWS)]
        support_size = rng.randint(0, min(9, len(prime_pool)))
        support = sorted(rng.sample(prime_pool, support_size))
        factors = tuple((prime, rng.randint(1, 40)) for prime in support)
        if case % 23 == 0 and 2 not in support:
            factors = ((2, rng.randint(1, 40)),) + factors
        if case % 29 == 0 and 3 not in {prime for prime, _ in factors}:
            factors = ((3, rng.randint(1, 40)),) + factors
        factors = tuple(sorted(dict(factors).items()))
        if case % 11 == 0:
            left_owner = right_owner = 1
            owners = {prime: 1 for prime, _ in factors}
            same_owner += 1
        else:
            left_owner, right_owner = 1, 2
            owners = {prime: rng.choice((1, 2)) for prime, _ in factors}
        loss, left, right, rows = validate_covered_fixture(
            k, factors, owners, left_owner, right_owner
        )
        d = product_of_factors(factors)
        max_digits = max(max_digits, len(str(d)))
        if d != loss * left * right:
            raise AssertionError("random decomposition")
        p2 += any(row["prime"] == 2 for row in rows)
        p3 += any(row["prime"] == 3 for row in rows)
        large_prime += any(row["prime"] >= k for row in rows)
        zero_clean += any(row["clean_exponent"] == 0 for row in rows)
    if min(p2, p3, large_prime, zero_clean, same_owner) <= 0:
        raise AssertionError("random boundary coverage missing")
    return {
        "seed": seed,
        "cases": cases,
        "maximum_gap_digits": max_digits,
        "cases_with_p2": p2,
        "cases_with_p3": p3,
        "cases_with_prime_at_least_k": large_prime,
        "cases_with_zero_clean_component": zero_clean,
        "same_owner_cases": same_owner,
    }


def chooser_composition_certificate() -> dict[str, int]:
    """Finite-choice model, including empty support and arbitrary defaults."""

    supports = (
        (),
        ((2, 1),),
        ((3, 1),),
        ((2, 8), (3, 12), (17, 3)),
        ((5, 1), (7, 9), (11, 2), (13, 20)),
    )
    checked_primes = empty = zero_clean = 0
    for k in ROWS:
        for factors in supports:
            # Model the local theorem's nonempty witness set.  Values away
            # from support receive the irrelevant total-function default 1.
            witness_options = {
                prime: tuple(range(1, k + 1)) for prime, _ in factors
            }
            owner = lambda prime: witness_options.get(prime, (1,))[0]
            if not factors:
                empty += 1
            for prime, exponent in factors:
                selected = owner(prime)
                if not (1 <= selected <= k) or selected not in witness_options[prime]:
                    raise AssertionError((k, prime, selected))
                checked_primes += 1
                zero_clean += clean_exponent(prime, exponent, k) == 0
            if owner(997) != 1:
                raise AssertionError("off-support chooser value matters")
    if min(checked_primes, empty, zero_clean) <= 0:
        raise AssertionError("chooser boundary coverage missing")
    return {
        "support_families": len(supports) * len(ROWS),
        "selected_support_primes": checked_primes,
        "empty_supports": empty,
        "zero_clean_selected_components": zero_clean,
    }


def exact_row_boundary_certificate() -> dict[str, Any]:
    """Hit the exact aggregate loss and the zero-loss large-prime edge."""

    exact_loss_rows = 0
    large_prime_rows = 0
    p2_rows = p3_rows = 0
    fixtures: dict[int, dict[str, int]] = {}
    for k in ROWS:
        loss_factors = tuple(
            (prime, loss_exponent(prime, k))
            for prime in primes_up_to(k - 1)
            if loss_exponent(prime, k) > 0
        )
        owners = {prime: 3 for prime, _ in loss_factors}
        loss, left, right, rows = validate_covered_fixture(
            k, loss_factors, owners, 1, 2
        )
        if (loss, left, right) != (aggregate_loss(k), 1, 1):
            raise AssertionError(("exact row loss", k, loss, left, right))
        if any(row["clean_exponent"] != 0 for row in rows):
            raise AssertionError(("exact loss fixture retained mass", k, rows))
        exact_loss_rows += 1
        p2_rows += any(row["prime"] == 2 for row in rows)
        p3_rows += any(row["prime"] == 3 for row in rows)

        prime = next(value for value in range(k, 2 * k + 20) if is_prime(value))
        loss2, left2, right2, rows2 = validate_covered_fixture(
            k, ((prime, 1),), {prime: 1}, 1, 2
        )
        if (loss2, left2, right2) != (1, prime, 1):
            raise AssertionError(("zero-loss large prime", k, prime, loss2, left2, right2))
        if rows2[0]["loss_exponent"] != 0:
            raise AssertionError(("large-prime exponent", k, rows2))
        large_prime_rows += 1
        fixtures[k] = {
            "aggregate_loss": loss,
            "large_prime": prime,
            "large_prime_loss": loss2,
        }
    if (exact_loss_rows, large_prime_rows, p2_rows, p3_rows) != (6, 6, 6, 6):
        raise AssertionError((exact_loss_rows, large_prime_rows, p2_rows, p3_rows))
    return {
        "exact_loss_rows": exact_loss_rows,
        "large_prime_zero_loss_rows": large_prime_rows,
        "p2_rows": p2_rows,
        "p3_rows": p3_rows,
        "fixtures": fixtures,
    }


@lru_cache(maxsize=None)
def report(max_d: int = 1_500, random_cases: int = 5_000) -> dict[str, Any]:
    source = source_surface_certificate()
    if source["candidate_sha256"] != EXPECTED_CANDIDATE_SHA256:
        raise AssertionError(source["candidate_sha256"])
    if source["aggregate_sha256"] != EXPECTED_AGGREGATE_SHA256:
        raise AssertionError(source["aggregate_sha256"])
    if source["concentration_sha256"] != EXPECTED_CONCENTRATION_SHA256:
        raise AssertionError(source["concentration_sha256"])
    if source["imports"] != ("ErdosProblems.Erdos686TwoOwnerAggregate",):
        raise AssertionError(source["imports"])
    if source["public_theorems"] != EXPECTED_PUBLIC_THEOREMS:
        raise AssertionError(source["public_theorems"])
    if (
        source["forbidden"]
        or source["audit_forbidden"]
        or source["private_header_leaks"]
        or source["imports_producer_verifier"]
    ):
        raise AssertionError(
            (
                source["forbidden"],
                source["audit_forbidden"],
                source["private_header_leaks"],
                source["imports_producer_verifier"],
            )
        )
    if not all(source["final_quantifier_markers"].values()):
        raise AssertionError(source["final_quantifier_markers"])

    recomputed = {k: aggregate_loss(k) for k in ROWS}
    parsed = parse_target_loss_table()
    if recomputed != EXPECTED_ROW_LOSSES or parsed != EXPECTED_ROW_LOSSES:
        raise AssertionError((recomputed, parsed))
    for k in ROWS:
        for prime in primes_up_to(131):
            if prime >= k and loss_exponent(prime, k) != 0:
                raise AssertionError(("large-prime loss", k, prime))

    return {
        "source": source,
        "row_losses": {"recomputed": recomputed, "lean_table": parsed},
        "row_boundaries": exact_row_boundary_certificate(),
        "small_exhaustive": exhaustive_small_certificate(max_d),
        "large_random": random_large_certificate(random_cases),
        "cover_quantifiers": no_two_cover_equivalence_certificate(),
        "chooser": chooser_composition_certificate(),
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
