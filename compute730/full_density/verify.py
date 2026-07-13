#!/usr/bin/env python3
"""Independent exact certificates for the submitted Erdős #730 proof.

This module intentionally uses only the Python standard library.  Every
quantity which enters a verdict is an ``int`` or ``fractions.Fraction``;
there is no floating-point arithmetic and no numerical approximation to a
logarithm.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path


SOURCE_SHA256 = "3df2e48ca62e35dbfbd25406badf37574d910efb2ab39360ab3458f3a31c4292"
SOURCE_LINES = 2_818
SOURCE_BYTES = 39_992

T = 3 * 41 * 43

# A linear form is represented by (slope, constant).
FORMS: dict[str, tuple[int, int]] = {
    "P": (42 * T, 11),
    "Q": (72 * T, 13),
    "R": (28 * T, 5),
    "S": (72 * T, 19),
}

EXPECTED_IDENTITIES: dict[str, tuple[int, int]] = {
    "12P-7Q": (0, 41),
    "18R-7S": (0, -43),
    "12P-7S": (0, -1),
    "7Q-18R": (0, 1),
    "2P-3R": (0, 7),
    "S-Q": (0, 6),
}

EXPECTED_LOG_UPPERS: tuple[Fraction, ...] = (
    Fraction(3041, 7500),
    Fraction(3947, 13720),
    Fraction(97603, 437400),
    Fraction(24267, 133100),
    Fraction(142241, 922740),
    Fraction(757123, 5670000),
)


def source_digest(path: Path) -> tuple[str, int, int]:
    """Return SHA-256, line count, and byte count for a source artifact."""

    data = path.read_bytes()
    return sha256(data).hexdigest(), len(data.splitlines()), len(data)


def scale_linear(scale: int, form: tuple[int, int]) -> tuple[int, int]:
    return scale * form[0], scale * form[1]


def add_linear(*forms: tuple[int, int]) -> tuple[int, int]:
    return sum(form[0] for form in forms), sum(form[1] for form in forms)


def multiply_linear(
    left: tuple[int, int], right: tuple[int, int]
) -> tuple[int, int, int]:
    """Return coefficients (x^2, x, 1) of two multiplied linear forms."""

    a, b = left
    c, d = right
    return a * c, a * d + b * c, b * d


def scale_quadratic(
    scale: int, polynomial: tuple[int, int, int]
) -> tuple[int, int, int]:
    return tuple(scale * coefficient for coefficient in polynomial)  # type: ignore[return-value]


def family_certificate() -> dict[str, object]:
    """Recompute the family identities without importing legacy producers."""

    p, q, r, s = (FORMS[name] for name in ("P", "Q", "R", "S"))
    identities = {
        "12P-7Q": add_linear(scale_linear(12, p), scale_linear(-7, q)),
        "18R-7S": add_linear(scale_linear(18, r), scale_linear(-7, s)),
        "12P-7S": add_linear(scale_linear(12, p), scale_linear(-7, s)),
        "7Q-18R": add_linear(scale_linear(7, q), scale_linear(-18, r)),
        "2P-3R": add_linear(scale_linear(2, p), scale_linear(-3, r)),
        "S-Q": add_linear(s, scale_linear(-1, q)),
    }

    two_pq_minus_one = list(scale_quadratic(2, multiply_linear(p, q)))
    two_pq_minus_one[2] -= 1
    three_rs = scale_quadratic(3, multiply_linear(r, s))

    leading_multipliers = {
        "P": Fraction(12, 7) * FORMS["P"][0] ** 2,
        "Q": Fraction(7, 12) * FORMS["Q"][0] ** 2,
        "R": Fraction(54, 14) * FORMS["R"][0] ** 2,
        "S": Fraction(7, 12) * FORMS["S"][0] ** 2,
    }

    return {
        "T": T,
        "slopes": {name: form[0] for name, form in FORMS.items()},
        "constants": {name: form[1] for name, form in FORMS.items()},
        "two_pq_minus_one": tuple(two_pq_minus_one),
        "three_rs": three_rs,
        "identities": identities,
        "common_quadratic_coefficient": leading_multipliers,
        "common_quadratic_integer": 3024 * T * T,
        "C0": 72 * T + 19,
    }


def prime_factorization(value: int) -> tuple[tuple[int, int], ...]:
    """Trial-division factorization, adequate for the small certificates here."""

    if value == 0:
        raise ValueError("zero has no prime factorization")
    remaining = abs(value)
    result: list[tuple[int, int]] = []
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        if exponent:
            result.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        result.append((remaining, 1))
    return tuple(result)


def exceptional_prime_certificate() -> dict[str, object]:
    b_values = {
        "P": -246 * T,
        "Q": 246 * T,
        "R": 258 * T,
        "S": -258 * T,
    }
    factorization = {
        name: prime_factorization(value) for name, value in b_values.items()
    }
    exceptional = sorted(
        {prime for factors in factorization.values() for prime, _ in factors}
    )
    fixed_residues = {
        prime: {name: constant % prime for name, (_, constant) in FORMS.items()}
        for prime in (2, 3, 41, 43)
    }
    return {
        "T_factorization": prime_factorization(T),
        "b_values": b_values,
        "b_factorization": factorization,
        "exceptional_primes": tuple(exceptional),
        "fixed_branch_residues": fixed_residues,
        "three_quotient_residue": ((FORMS["R"][1] * FORMS["S"][1] - 1) // 2)
        % 3,
    }


def unit_residues(modulus: int) -> tuple[int, ...]:
    return tuple(c for c in range(modulus) if gcd(c, modulus) == 1)


def top_residue_tables() -> dict[str, tuple[tuple[int, int, int, bool], ...]]:
    """Exhaust all unit classes used in the top-prime digit classification.

    Each row is ``(c, c^2 mod m, numerator residue mod m, survives)``.
    The Q and S branches never survive the least-digit inequality, so their
    final field is false for every unit class.
    """

    p_rows = tuple(
        (c, c * c % 7, 12 * c * c % 7, 12 * c * c % 7 == 3)
        for c in unit_residues(7)
    )
    q_rows = tuple(
        (c, c * c % 12, 7 * c * c % 12, False)
        for c in unit_residues(12)
    )
    r_rows = tuple(
        (c, c * c % 14, 54 * c * c % 14, 54 * c * c % 14 == 6)
        for c in unit_residues(14)
    )
    s_rows = tuple(
        (c, c * c % 12, 7 * c * c % 12, False)
        for c in unit_residues(12)
    )
    return {"P": p_rows, "Q": q_rows, "R": r_rows, "S": s_rows}


def euler_phi(modulus: int) -> int:
    result = modulus
    for prime, _ in prime_factorization(modulus):
        result -= result // prime
    return result


def crt_class_certificate() -> dict[str, dict[str, int]]:
    """Enumerate, rather than infer, both periodic allowed-class counts."""

    a_p = FORMS["P"][0]
    a_r = FORMS["R"][0]
    p_count = sum(
        gcd(c, a_p) == 1 and c % 7 in (3, 4) for c in range(a_p)
    )
    r_count = sum(
        gcd(c, a_r) == 1 and c % 14 in (5, 9) for c in range(a_r)
    )
    return {
        "P": {
            "modulus": a_p,
            "phi": euler_phi(a_p),
            "allowed": p_count,
        },
        "R": {
            "modulus": a_r,
            "phi": euler_phi(a_r),
            "allowed": r_count,
        },
    }


def restricted_digit_count(p: int, digits: int, excluded_endpoint: int) -> int:
    """Exhaust (28) for a chosen prime, depth, and excluded units digit."""

    if p % 2 == 0 or digits < 1:
        raise ValueError("require an odd p and at least one digit")
    h = (p + 1) // 2
    if excluded_endpoint not in (0, h - 1):
        raise ValueError("the excluded digit must be a permitted endpoint")
    count = 0
    for value in range(p**digits):
        digits_list: list[int] = []
        work = value
        for _ in range(digits):
            digits_list.append(work % p)
            work //= p
        if digits_list[0] != excluded_endpoint and all(digit < h for digit in digits_list):
            count += 1
    return count


def log_ratio_upper(d: int) -> Fraction:
    """The exact bound U(d) for log((d+1)/(d-1)), valid for d >= 3."""

    if d < 3:
        raise ValueError("require d >= 3")
    x = Fraction(1, d)
    partial = 2 * (x + x**3 / 3)
    tail = 2 * x**5 / (5 * (1 - x * x))
    return partial + tail


def rational_certificate() -> dict[str, object]:
    finite_log_uppers = tuple(log_ratio_upper(2 * r + 3) for r in range(1, 7))
    tail_upper = Fraction(1, 98_304)
    s_upper = sum(
        (finite_log_uppers[r - 1] / 4**r for r in range(1, 7)),
        Fraction(0),
    ) + tail_upper
    log2_upper = log_ratio_upper(3)
    total_upper = 4 * s_upper + Fraction(2, 3) * log2_upper
    target = Fraction(2393, 2500)
    difference = target - total_upper
    return {
        "finite_log_uppers": finite_log_uppers,
        "tail_upper": tail_upper,
        "s_upper": s_upper,
        "log2_upper": log2_upper,
        "total_upper": total_upper,
        "target": target,
        "difference": difference,
    }


def verify_all() -> dict[str, object]:
    family = family_certificate()
    assert family["T"] == 5289
    assert family["slopes"] == {
        "P": 222_138,
        "Q": 380_808,
        "R": 148_092,
        "S": 380_808,
    }
    assert family["two_pq_minus_one"] == family["three_rs"] == (
        6048 * T * T,
        2676 * T,
        285,
    )
    assert family["identities"] == EXPECTED_IDENTITIES
    assert set(family["common_quadratic_coefficient"].values()) == {
        Fraction(3024 * T * T)
    }
    assert family["common_quadratic_integer"] == 84_591_927_504
    assert family["C0"] == 380_827

    exceptional = exceptional_prime_certificate()
    assert exceptional["T_factorization"] == ((3, 1), (41, 1), (43, 1))
    assert exceptional["exceptional_primes"] == (2, 3, 41, 43)
    assert exceptional["three_quotient_residue"] == 2

    tables = top_residue_tables()
    assert tuple(row[0] for row in tables["P"] if row[3]) == (3, 4)
    assert not any(row[3] for row in tables["Q"])
    assert tuple(row[0] for row in tables["R"] if row[3]) == (5, 9)
    assert not any(row[3] for row in tables["S"])

    crt = crt_class_certificate()
    assert crt["P"] == {"modulus": 222_138, "phi": 60_480, "allowed": 20_160}
    assert crt["R"] == {"modulus": 148_092, "phi": 40_320, "allowed": 13_440}

    rational = rational_certificate()
    assert rational["finite_log_uppers"] == EXPECTED_LOG_UPPERS
    assert rational["s_upper"] == Fraction(
        11_117_760_449_158_646_497,
        89_848_527_388_139_520_000,
    )
    assert rational["log2_upper"] == Fraction(1123, 1620)
    assert rational["total_upper"] == Fraction(
        21_498_408_212_212_214_497,
        22_462_131_847_034_880_000,
    )
    assert rational["difference"] == Fraction(
        2_344_391_769_572_639,
        22_462_131_847_034_880_000,
    )
    assert rational["difference"] > 0

    return {
        "family": family,
        "exceptional": exceptional,
        "top_tables": tables,
        "crt": crt,
        "rational": rational,
    }


def main() -> None:
    result = verify_all()
    print(f"SOURCE_SHA256={SOURCE_SHA256}")
    print(f"T={result['family']['T']}")
    print(f"SLOPES={result['family']['slopes']}")
    print(f"CRT={result['crt']}")
    rational = result["rational"]
    print(f"S_UPPER={rational['s_upper']}")
    print(f"LOG2_UPPER={rational['log2_upper']}")
    print(f"TOTAL_UPPER={rational['total_upper']}")
    print(f"POSITIVE_MARGIN={rational['difference']}")


if __name__ == "__main__":
    main()
