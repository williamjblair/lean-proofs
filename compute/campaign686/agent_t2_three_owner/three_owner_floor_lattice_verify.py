#!/usr/bin/env python3
"""Independent exact audit for the Target-2 three-owner quotient route."""

from __future__ import annotations

from itertools import combinations


DEEP = 10**120
DEEP_N16 = int(
    "11048779707016795813821579472468786620154883955085119052786776282417721075083493368730493012989644397541638075075311190921"
)


def sign(value: int) -> int:
    return (value > 0) - (value < 0)


def endpoint_window(k: int, n: int, d: int) -> bool:
    return (
        (n + d + k) ** k <= 4 * (n + k) ** k
        and 4 * (n + 1) ** k <= (n + d + 1) ** k
    )


def window_band(k: int, d: int) -> tuple[int, int]:
    def upper(n: int) -> bool:
        return (n + d + k) ** k <= 4 * (n + k) ** k

    def lower(n: int) -> bool:
        return 4 * (n + 1) ** k <= (n + d + 1) ** k

    lo, hi = 0, (k + 2) * d
    while lo < hi:
        mid = (lo + hi) // 2
        if upper(mid):
            hi = mid
        else:
            lo = mid + 1
    first = lo
    lo, hi = 0, (k + 2) * d
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if lower(mid):
            lo = mid
        else:
            hi = mid - 1
    return first, lo


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
    return tuple(coefficients[:3])  # type: ignore[return-value]


def residuals(k: int, n: int, d: int, owners: tuple[int, int, int]) -> tuple[int, ...]:
    center = 2 * n + d + k + 1
    if k % 2 == 0:
        return tuple(center + 3 * (n + owner) for owner in owners)
    return tuple(5 * (n + owner) - center for owner in owners)


def deep_window_falsifier() -> dict[str, int | bool]:
    k, n, d = 16, DEEP_N16, DEEP
    owners = (1, 8, 16)
    center = 2 * n + d + k + 1
    even = tuple(center + 3 * (n + owner) for owner in owners)
    odd = tuple(5 * (n + owner) - center for owner in owners)
    even_product = even[0] * even[1] * even[2]
    odd_product = odd[0] * odd[1] * odd[2]
    assert endpoint_window(k, n, d)
    assert even_product < 15 * center**3
    assert odd_product < 3 * center**3
    assert even_product < 16 * center**3
    assert odd_product < 4 * center**3
    return {
        "window": True,
        "even_expected_lower_fails": True,
        "odd_expected_lower_fails": True,
        "even_lower_margin": 15 * center**3 - even_product,
        "odd_lower_margin": 3 * center**3 - odd_product,
    }


def restricted_k220_window_audit() -> int:
    """Check the exact integer inequalities behind the k>=220 proof.

    The universal proof is: `k*d<5*n`, `d>=k`, and `k>=220` imply
    `n>22(d+k+1)-45i`.  This is equivalent to both lower linear bounds.
    The grid checks both boundary k and large/deep values.
    """

    checked = 0
    for k in (220, 221, 300, 1000):
        for d in (k, k + 1, 2 * k, 10**6 * k, DEEP):
            first, last = window_band(k, d)
            for n in {first, (first + last) // 2, last}:
                if not first <= n <= last:
                    continue
                assert k * d < 5 * n
                center = 2 * n + d + k + 1
                for owner in (1, (k + 1) // 2, k):
                    even = center + 3 * (n + owner)
                    odd = 5 * (n + owner) - center
                    assert 37 * center < 15 * even
                    assert 2 * even < 5 * center
                    assert 13 * center < 9 * odd
                    assert 2 * odd < 3 * center
                    checked += 1
    return checked


def verify_square_fixture(
    k: int,
    n: int,
    d: int,
    components: tuple[int, int, int],
    owners: tuple[int, int, int],
    cofactors: tuple[int, int, int],
) -> None:
    center = 2 * n + d + k + 1
    assert center == components[0] * components[1] * components[2]
    values = tuple(center + 3 * (n + owner) for owner in owners)
    assert values == tuple(
        cofactor * component**2
        for component, cofactor in zip(components, cofactors, strict=True)
    )


def synthetic_fixture_audit() -> None:
    verify_square_fixture(
        16, 8341, 4500, (17, 29, 43), (6, 11, 1), (160, 55, 25)
    )
    verify_square_fixture(
        16,
        8_547_105,
        847_742,
        (41, 239, 1831),
        (1, 13, 3),
        (25_927, 763, 13),
    )
    assert 9 * 847_742 < 8_547_105
    assert 4 * (8_547_105 + 1) ** 16 <= (8_547_105 + 847_742 + 1) ** 16
    assert not (
        (8_547_105 + 847_742 + 16) ** 16
        <= 4 * (8_547_105 + 16) ** 16
    )


def composed_rows(
    k: int, owners: tuple[int, int, int]
) -> tuple[tuple[int, int, int], ...]:
    rows = []
    for owner in owners:
        other = tuple(index for index in owners if index != owner)
        delta = (owner - other[0]) * (owner - other[1])
        constant, linear, quadratic = local_coefficients(k, owner)
        if k % 2 == 0:
            rows.append((9 * constant, 180 * quadratic * delta, -108 * linear * delta))
        else:
            rows.append((5 * constant, -60 * quadratic * delta, 100 * linear * delta))
    return tuple(rows)


def lattice_weights(rows: tuple[tuple[int, int, int], ...]) -> tuple[int, int, int]:
    (a1, b1, _), (a2, b2, _), (a3, b3, _) = rows
    return (a2 * b3 - a3 * b2, a3 * b1 - a1 * b3, a1 * b2 - a2 * b1)


def canonical_mixed_scan() -> int:
    """Exact k=16..200 scan of a canonical deep parameter cell per row.

    This supplies a counterfamily to any claim that all large-k reflected
    third-composition cells are one-sided.  It is not a finite proof of the
    target and deliberately makes no square-decomposition claim.
    """

    mixed = 0
    for k in range(16, 201):
        d = 10**6 * k
        first, last = window_band(k, d)
        n = (first + last) // 2
        assert endpoint_window(k, n, d)
        center = 2 * n + d + k + 1
        owners = (1, (k + 1) // 2, k)
        values = residuals(k, n, d, owners)
        product_value = values[0] * values[1] * values[2]
        rows = composed_rows(k, owners)
        weights = lattice_weights(rows)
        gamma = sum(weight * row[2] for weight, row in zip(weights, rows, strict=True))
        if gamma < 0:
            weights = tuple(-weight for weight in weights)
            gamma = -gamma
        scaled_terms = tuple(
            row[0] * product_value + (row[1] * center + row[2]) * center**2
            for row in rows
        )
        term_signs = tuple(
            sign(weight) * sign(term) if weight else 0
            for weight, term in zip(weights, scaled_terms, strict=True)
        )
        assert set(term_signs) - {0} == {-1, 1}, (k, term_signs)
        assert sum(
            weight * term for weight, term in zip(weights, scaled_terms, strict=True)
        ) == gamma * center**2
        mixed += 1
    return mixed


def main() -> None:
    print(
        {
            "deep_window": deep_window_falsifier(),
            "k220_linear_rows": restricted_k220_window_audit(),
            "canonical_mixed_rows": canonical_mixed_scan(),
        }
    )
    synthetic_fixture_audit()


if __name__ == "__main__":
    main()
