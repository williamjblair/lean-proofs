#!/usr/bin/env python3
"""Exact arithmetic for the ELS consecutive-integer-property lane.

For ``x > 0``, ``small_part(k, x)`` is the largest divisor of ``x`` whose
prime divisors are at most ``k``.  Erdős--Lacampagne--Selfridge call the
sequence of these parts, over a block of ``k`` consecutive integers, a
sequence with the consecutive integer property.

This file deliberately separates three assertions:

* the elementary factorial and two-block product identities;
* the published bounded-part classification (checked here on every concrete
  fixture on which it is invoked, but not treated as a computational proof of
  the uniform theorem);
* hostile boundary fixtures, including a target-row counterexample showing
  why the factorial identity alone is not an equation proof.

Only integer arithmetic is used.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial, gcd, isqrt, prod
from typing import Iterable


@lru_cache(maxsize=None)
def primes_up_to(k: int) -> tuple[int, ...]:
    if k < 0:
        raise ValueError("k must be nonnegative")
    if k < 2:
        return ()
    sieve = bytearray(b"\x01") * (k + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(k) + 1):
        if sieve[p]:
            sieve[p * p : k + 1 : p] = b"\x00" * (((k - p * p) // p) + 1)
    return tuple(p for p in range(2, k + 1) if sieve[p])


def small_part(k: int, x: int) -> int:
    """Largest divisor of ``x`` supported on prime bases at most ``k``."""
    if k < 1 or x < 1:
        raise ValueError("small_part requires k,x >= 1")
    answer = 1
    remainder = x
    for p in primes_up_to(k):
        while remainder % p == 0:
            answer *= p
            remainder //= p
    return answer


def rough_part(k: int, x: int) -> int:
    part = small_part(k, x)
    assert x % part == 0
    return x // part


def part_block(k: int, start: int) -> tuple[int, ...]:
    """Parts of ``start+1,...,start+k``."""
    if start < 0:
        raise ValueError("start must be nonnegative")
    return tuple(small_part(k, start + i) for i in range(1, k + 1))


def rough_block(k: int, start: int) -> tuple[int, ...]:
    return tuple(rough_part(k, start + i) for i in range(1, k + 1))


def block_product(k: int, start: int) -> int:
    return prod(start + i for i in range(1, k + 1))


def part_product(k: int, start: int) -> int:
    return prod(part_block(k, start))


def factorial_quotient(k: int, start: int) -> int:
    value = part_product(k, start)
    assert value % factorial(k) == 0
    return value // factorial(k)


def equation_holds(k: int, n: int, d: int) -> bool:
    return block_product(k, n + d) == 4 * block_product(k, n)


def small_product_ratio_holds(k: int, n: int, d: int) -> bool:
    return part_product(k, n + d) == 4 * part_product(k, n)


def rough_product_equality_holds(k: int, n: int, d: int) -> bool:
    return prod(rough_block(k, n + d)) == prod(rough_block(k, n))


def centered_root_bracket_audit(k_max: int = 512) -> dict[str, object]:
    """Exact audit of the centered `29/(20k)` root bracket.

    The uniform proof retains the first six binomial terms.  For every
    ``k>=16``, each normalized falling-factor term is at least its value at
    ``k=16`` because ``(k-r)/k >= (16-r)/16``.  The frozen rational below is
    therefore a uniform lower bound, not a floating-point estimate.
    """
    partial = sum(
        (Fraction(comb(16, j)) * Fraction(29, 320) ** j for j in range(6)),
        Fraction(),
    )
    assert partial == Fraction(839_241_148_077, 209_715_200_000)
    assert partial - 4 == Fraction(380_348_077, 209_715_200_000) > 0
    samples: list[dict[str, int]] = []
    for k in range(16, k_max + 1):
        margin = (20 * k + 29) ** k - 4 * (20 * k) ** k
        if margin <= 0:
            raise AssertionError(("centered root bracket", k, margin))
        if k in (16, 17, 19, 64, k_max):
            samples.append({"k": k, "integer_margin": margin})
    return {
        "k_min": 16,
        "k_max": k_max,
        "partial_sum_numerator": partial.numerator,
        "partial_sum_denominator": partial.denominator,
        "excess_numerator": (partial - 4).numerator,
        "excess_denominator": (partial - 4).denominator,
        "samples": samples,
    }


def bounded_k_classification_holds(k: int, start: int) -> bool:
    """Concrete instance of ELS Theorem 1 when its bound is true."""
    values = part_block(k, start)
    if max(values) > k:
        return True
    return sorted(values) == list(range(1, k + 1))


def bounded_k_plus_one_data(k: int, start: int) -> dict[str, object] | None:
    """Concrete Theorem-4 certificate, or ``None`` outside its bound.

    In the non-``k!`` case, Theorem 4 says that the values are
    ``1,...,k+1`` with one value ``r`` deleted, and that if ``k+1`` is in
    position ``j`` then ``r=gcd(j,k+1)``.  This routine verifies all those
    identities directly for a supplied finite block.
    """
    values = part_block(k, start)
    if max(values) > k + 1:
        return None
    if len(set(values)) != k:
        raise AssertionError("bounded ELS values are not distinct")
    expected = set(range(1, k + 2))
    missing = sorted(expected.difference(values))
    if len(missing) != 1:
        raise AssertionError("bounded ELS block has no unique missing value")
    r = missing[0]
    if prod(values) != factorial(k + 1) // r:
        raise AssertionError("missing-value product formula failed")
    if r == k + 1:
        if sorted(values) != list(range(1, k + 1)):
            raise AssertionError("k! branch is not 1,...,k")
        return {
            "missing": r,
            "product": prod(values),
            "position_k_plus_one": None,
            "position_gcd": None,
        }
    j = values.index(k + 1) + 1
    if r != gcd(j, k + 1):
        raise AssertionError("ELS deleted-value/gcd formula failed")
    if gcd(start, k + 1) != r:
        raise AssertionError("block-start gcd does not equal deleted value")
    return {
        "missing": r,
        "product": prod(values),
        "position_k_plus_one": j,
        "position_gcd": gcd(j, k + 1),
    }


def period_for_bounded_parts(k: int) -> int:
    """A period resolving all parts at most ``k+1`` exactly."""
    answer = 1
    for p in primes_up_to(k):
        power = p
        while power <= k + 1:
            power *= p
        answer *= power
    return answer


@dataclass(frozen=True)
class FixtureAudit:
    name: str
    k: int
    n: int
    d: int
    equation: bool
    small_ratio: bool
    rough_ratio: bool
    lower_factorial_quotient: int
    upper_factorial_quotient: int
    lower_max: int
    lower_max_position: int
    upper_max: int
    upper_max_position: int
    lower_at_most_k_plus_one_count: int
    upper_at_most_k_plus_one_count: int
    gcd_upper_start_k_plus_one: int
    quarter_gcd_divides_k_plus_one: bool


def audit_fixture(name: str, k: int, n: int, d: int) -> FixtureAudit:
    lower = part_block(k, n)
    upper = part_block(k, n + d)
    g = gcd(n + d, k + 1)
    return FixtureAudit(
        name=name,
        k=k,
        n=n,
        d=d,
        equation=equation_holds(k, n, d),
        small_ratio=small_product_ratio_holds(k, n, d),
        rough_ratio=rough_product_equality_holds(k, n, d),
        lower_factorial_quotient=factorial_quotient(k, n),
        upper_factorial_quotient=factorial_quotient(k, n + d),
        lower_max=max(lower),
        lower_max_position=lower.index(max(lower)) + 1,
        upper_max=max(upper),
        upper_max_position=upper.index(max(upper)) + 1,
        lower_at_most_k_plus_one_count=sum(x <= k + 1 for x in lower),
        upper_at_most_k_plus_one_count=sum(x <= k + 1 for x in upper),
        gcd_upper_start_k_plus_one=g,
        quarter_gcd_divides_k_plus_one=(k + 1) % (4 * g) == 0,
    )


def target_row_mass_counterexample() -> dict[str, object]:
    """A k=19 exact counterexample to the mass-only closure.

    The upper start is congruent to 1 modulo a period that fixes every
    ``19``-small part at most 20, hence its parts are exactly ``2,...,20``.
    The lower start 1540 has small-part product ``5*19!``.  Thus the stripped
    products have the exact factor-four relation and the upper block is in
    the exceptional bounded ELS branch, but the original block equation is
    false (and its ratio window is deliberately not asserted).
    """
    k = 19
    lower_start = 1540
    period = period_for_bounded_parts(k)
    upper_start = period + 1
    d = upper_start - lower_start
    lower = part_block(k, lower_start)
    upper = part_block(k, upper_start)
    upper_els = bounded_k_plus_one_data(k, upper_start)
    assert period == 2_258_015_666_306_400
    assert lower == (
        1,
        6,
        1,
        8,
        15,
        2,
        1547,
        36,
        1,
        50,
        33,
        16,
        1,
        42,
        5,
        4,
        9,
        38,
        1,
    )
    assert upper == tuple(range(2, 21))
    assert prod(lower) == 5 * factorial(19)
    assert prod(upper) == factorial(20) == 4 * prod(lower)
    assert upper_els == {
        "missing": 1,
        "product": factorial(20),
        "position_k_plus_one": 19,
        "position_gcd": 1,
    }
    assert gcd(upper_start, 20) == 1
    assert d % 2 == 1
    assert not equation_holds(k, lower_start, d)
    return {
        "k": k,
        "lower_start": lower_start,
        "upper_start": upper_start,
        "d": d,
        "period": period,
        "lower_parts": list(lower),
        "upper_parts": list(upper),
        "lower_product_over_factorial": prod(lower) // factorial(k),
        "upper_missing": upper_els["missing"],
        "upper_k_plus_one_position": upper_els["position_k_plus_one"],
        "small_product_ratio_four": prod(upper) == 4 * prod(lower),
        "full_equation": equation_holds(k, lower_start, d),
    }


def bounded_equation_core_multisets(k: int, r: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """ELS multisets in the branch where both equation blocks are <= k+1.

    The upper deleted value is ``r``.  Exact quotient-four mass makes the
    lower deleted value ``4r``.  This helper checks the necessary arithmetic
    ``4r | k+1`` and returns the sorted lower and upper multisets.
    """
    K = k + 1
    if k < 16 or r < 1 or K % (4 * r) != 0:
        raise ValueError("requires k>=16, r>=1, and 4r | k+1")
    lower = tuple(x for x in range(1, K + 1) if x != 4 * r)
    upper = tuple(x for x in range(1, K + 1) if x != r)
    assert len(lower) == len(upper) == k
    assert prod(upper) == 4 * prod(lower)
    return lower, upper


def maximum_strict_matching_size(
    lower: Iterable[int], upper: Iterable[int]
) -> int:
    """Maximum pairs ``a<b`` by the exact sorted greedy algorithm."""
    aa = sorted(lower)
    bb = sorted(upper)
    i = 0
    matches = 0
    for b in bb:
        if i < len(aa) and aa[i] < b:
            i += 1
            matches += 1
    return matches


def owner_graph_edge_dichotomy_audit(limit: int = 2_000) -> dict[str, object]:
    """Finite exact audit of the uniform no-perfect-matching proof.

    A perfect owner matching would pair every lower core ``a`` with an upper
    core ``b>a``.  The proof is uniform: for ``r>1`` both multisets contain
    the minimum 1, so upper 1 has no predecessor; for ``r=1`` and ``k>=16``
    both contain the maximum ``k+1``, so lower ``k+1`` has no successor.
    The loop below independently checks every arithmetic branch through the
    stated limit.
    """
    branches = 0
    largest_matching_deficit = 0
    sample: list[dict[str, int]] = []
    for k in range(16, limit + 1):
        K = k + 1
        for r in range(1, K // 4 + 1):
            if K % (4 * r):
                continue
            branches += 1
            lower, upper = bounded_equation_core_multisets(k, r)
            matched = maximum_strict_matching_size(lower, upper)
            if matched >= k:
                raise AssertionError(("strict perfect matching survived", k, r))
            largest_matching_deficit = max(largest_matching_deficit, k - matched)
            if len(sample) < 8:
                sample.append(
                    {
                        "k": k,
                        "r": r,
                        "lower_missing": 4 * r,
                        "upper_missing": r,
                        "maximum_strict_pairs": matched,
                        "owner_edges_required": k + 1,
                    }
                )
    return {
        "k_min": 16,
        "k_max": limit,
        "arithmetic_branches": branches,
        "largest_matching_deficit": largest_matching_deficit,
        "samples": sample,
    }


def balanced_component_capacity_audit(k_max: int = 256) -> dict[str, object]:
    """Audit the explicit large-d component-balance threshold.

    Put ``K=k+1`` and ``T=(2K)^k``.  If a component has ``ell`` lower and
    ``u`` upper vertices, the rough-part bounds imply, when ``ell>u``,
    ``n^(ell-u) < 2^u K^ell`` (and symmetrically when ``u>ell``).  For
    ``ell,u<=k`` the right side is at most ``T``.  Thus ``n>=T`` forces
    ``ell=u``.  The loop checks every exponent pair in the frozen range.
    """
    pairs = 0
    samples: list[dict[str, int]] = []
    for k in range(16, k_max + 1):
        K = k + 1
        threshold = (2 * K) ** k
        for ell in range(1, k + 1):
            for u in range(1, k + 1):
                if ell == u:
                    continue
                pairs += 1
                rhs = (2**u) * (K**ell) if ell > u else (2**ell) * (K**u)
                if rhs > threshold:
                    raise AssertionError(("component threshold failure", k, ell, u))
        if k in (16, 17, 19, 64, k_max):
            samples.append(
                {
                    "k": k,
                    "threshold": threshold,
                    "balanced_nontrivial_min_edges": k + 2,
                }
            )
    return {
        "k_min": 16,
        "k_max": k_max,
        "unequal_component_size_pairs": pairs,
        "samples": samples,
    }


def rational_rank(matrix: list[list[int]]) -> int:
    """Exact Gaussian rank over Q for the tiny incidence audits."""
    a = [[Fraction(x) for x in row] for row in matrix]
    if not a:
        return 0
    rows = len(a)
    cols = len(a[0])
    pivot_row = 0
    for col in range(cols):
        pivot = next((r for r in range(pivot_row, rows) if a[r][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        scale = a[pivot_row][col]
        a[pivot_row] = [x / scale for x in a[pivot_row]]
        for r in range(rows):
            if r == pivot_row or not a[r][col]:
                continue
            scale = a[r][col]
            a[r] = [x - scale * y for x, y in zip(a[r], a[pivot_row])]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def cycle_incidence_audit(s_max: int = 24) -> dict[str, object]:
    """Show exactly why an even owner cycle has no second determinant.

    Rows are the ``s`` lower vertices followed by the ``s`` upper vertices;
    columns are the ``2s`` cyclic edges.  The unoriented incidence matrix has
    rank ``2s-1`` over Q.  Its sole left dependency is +1 on every lower row
    and -1 on every upper row: after exponentiating, this is exactly the
    already-known equality of total lower and upper rough products.
    """
    rows: list[dict[str, int]] = []
    for s in range(2, s_max + 1):
        matrix = [[0 for _ in range(2 * s)] for _ in range(2 * s)]
        # Edge 2i joins lower i to upper i; edge 2i+1 joins upper i
        # to lower i+1 (cyclically).
        for i in range(s):
            matrix[i][2 * i] = 1
            matrix[s + i][2 * i] = 1
            matrix[s + i][2 * i + 1] = 1
            matrix[(i + 1) % s][2 * i + 1] = 1
        rank = rational_rank(matrix)
        if rank != 2 * s - 1:
            raise AssertionError(("cycle incidence rank", s, rank))
        dependency = [1] * s + [-1] * s
        if any(
            sum(dependency[r] * matrix[r][c] for r in range(2 * s)) != 0
            for c in range(2 * s)
        ):
            raise AssertionError(("cycle global dependency", s))
        rows.append({"vertices_per_side": s, "rank": rank, "nullity": 1})
    return {"s_min": 2, "s_max": s_max, "cycles": rows}


def reflection_compatible_four_cycle_fixture() -> dict[str, object]:
    """Exact row/reflection counterfixture for a minimal owner cycle.

    This is not an equation: it fails the lower ratio-window inequality.  It
    is frozen to show that owner ordering, pairwise-coprime large support,
    all four shifted-difference divisibilities, ``n>9d``, and the aggregate
    reflection compression do not by themselves eliminate a 4-cycle.
    """
    k = 19
    n = 239_446
    d = 5_198
    K = k + 1
    edges = {
        (1, 19): 163,
        (1, 1): 113,
        (3, 19): 79,
        (3, 1): 433,
    }
    lower_cores = {1: 13, 3: 7}
    upper_cores = {19: 19, 1: 5}
    lower_values = {
        i: lower_cores[i] * prod(q for (ii, _), q in edges.items() if ii == i)
        for i in lower_cores
    }
    upper_values = {
        j: upper_cores[j] * prod(q for (_, jj), q in edges.items() if jj == j)
        for j in upper_cores
    }
    assert lower_values == {1: n + 1, 3: n + 3}
    assert upper_values == {19: n + d + 19, 1: n + d + 1}
    labels = list(edges.values())
    assert all(q > k and all(q % h for h in range(2, isqrt(q) + 1)) for q in labels)
    assert all(gcd(labels[i], labels[j]) == 1 for i in range(4) for j in range(i))
    for (i, j), q in edges.items():
        assert (d + j - i) % q == 0
    S = 2 * n + d + K
    reflection_product = prod(d + K - 2 * i for i in range(1, k + 1))
    assert S == 484_110
    assert 5 * reflection_product % S == 0
    upper_window = (n + d + k) ** k <= 4 * (n + k) ** k
    lower_window = 4 * (n + 1) ** k <= (n + d + 1) ** k
    assert upper_window and not lower_window
    return {
        "k": k,
        "n": n,
        "d": d,
        "edges": {f"{i},{j}": q for (i, j), q in edges.items()},
        "lower_cores": lower_cores,
        "upper_cores": upper_cores,
        "lower_values": lower_values,
        "upper_values": upper_values,
        "n_gt_9d": n > 9 * d,
        "reflection_center": S,
        "reflection_compression": True,
        "upper_ratio_window": upper_window,
        "lower_ratio_window": lower_window,
    }


def proper_component_separation_audit(k_max: int = 512) -> dict[str, object]:
    """Audit the only rational exceptions to ``4^(s/k)``.

    For ``0<s<k``, ``4^(s/k)`` is rational exactly when ``k`` is even and
    ``s=k/2``.  Outside that case the integer norm gives the explicit gap
    ``|P/Q-4^(s/k)| >= 1/(k*K^(s*(2k-1)))`` for ``1<=P,Q<=K^s``.
    The findings use this with a quantified ratio-window error.
    """
    pairs = 0
    rational = []
    for k in range(16, k_max + 1):
        for s in range(1, k):
            pairs += 1
            is_rational = (2 * s) % k == 0
            expected = k % 2 == 0 and s == k // 2
            if is_rational != expected:
                raise AssertionError(("rational component exponent", k, s))
            if is_rational and len(rational) < 12:
                rational.append({"k": k, "s": s, "value": 2})
    return {
        "k_min": 16,
        "k_max": k_max,
        "proper_component_sizes": pairs,
        "rational_exceptions": rational,
    }


FIXTURES = (
    ("row-prefix-17", 984, 3_177_026, 4_480),
    ("row-prefix-16", 244, 48_502, 277),
    ("smooth-reflection-even", 16, 582_087, 52_684),
    ("smooth-reflection-odd", 17, 996_082, 84_632),
    ("d-one-telescope-k9", 9, 2, 1),
    ("d-one-telescope-k15", 15, 4, 1),
)


def exhaustive_small_audit() -> dict[str, int]:
    """Finite sanity check of the two published bounded classifications."""
    theorem1_cases = 0
    theorem4_cases = 0
    starts = 0
    for k in range(2, 13):
        for start in range(0, 2_000):
            starts += 1
            values = part_block(k, start)
            if max(values) <= k:
                theorem1_cases += 1
                if not bounded_k_classification_holds(k, start):
                    raise AssertionError(("Theorem 1 finite failure", k, start))
            if max(values) <= k + 1:
                theorem4_cases += 1
                bounded_k_plus_one_data(k, start)
    return {
        "lengths": 11,
        "starts": starts,
        "theorem1_bounded_cases": theorem1_cases,
        "theorem4_bounded_cases": theorem4_cases,
    }


def report() -> dict[str, object]:
    fixtures = [asdict(audit_fixture(*row)) for row in FIXTURES]
    for row in fixtures:
        if row["equation"]:
            assert row["small_ratio"] and row["rough_ratio"]
            assert row["upper_max"] > row["k"]
    return {
        "source": {
            "authors": "P. Erdos, C. B. Lacampagne, J. L. Selfridge",
            "title": "Prime factors of binomial coefficients and related problems",
            "journal": "Acta Arithmetica 49 (1988), 507-523",
            "doi": "10.4064/aa-49-5-507-523",
            "theorem1_pages": "507-508",
            "theorem4_page": "521",
        },
        "finite_classification_audit": exhaustive_small_audit(),
        "centered_root_bracket": centered_root_bracket_audit(),
        "fixtures": fixtures,
        "target_row_mass_counterexample": target_row_mass_counterexample(),
        "owner_graph_edge_dichotomy": owner_graph_edge_dichotomy_audit(),
        "balanced_component_capacity": balanced_component_capacity_audit(),
        "cycle_incidence": cycle_incidence_audit(),
        "reflection_compatible_four_cycle": reflection_compatible_four_cycle_fixture(),
        "proper_component_separation": proper_component_separation_audit(),
    }


if __name__ == "__main__":
    import json

    print(json.dumps(report(), indent=2, sort_keys=True))
