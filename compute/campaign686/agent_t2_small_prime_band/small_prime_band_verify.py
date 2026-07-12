"""Exact crossing-band and small-prime valuation audit for Erdős 686.

No floating-point arithmetic is used.  The archimedean band is exactly the
set of natural ``n`` satisfying both power inequalities already proved in
``ratio_window_four_nat``.  Valuation discrepancies are evaluated with
Legendre floor sums, not by factoring huge block products.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import prod
from typing import Callable, Iterable, Iterator


def primes_through(limit: int) -> tuple[int, ...]:
    if limit < 2:
        return ()
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return tuple(i for i in range(2, limit + 1) if sieve[i])


def prime_power_base_exponent(value: int) -> tuple[int, int] | None:
    """Return ``(p,A)`` exactly when ``value=p**A`` for a prime ``p``."""

    if value < 2:
        return None
    factor = 2 if value % 2 == 0 else None
    candidate = 3
    while factor is None and candidate * candidate <= value:
        if value % candidate == 0:
            factor = candidate
            break
        candidate += 2
    if factor is None:
        return value, 1
    exponent = 0
    remaining = value
    while remaining % factor == 0:
        remaining //= factor
        exponent += 1
    return (factor, exponent) if remaining == 1 else None


def lower_prime_power_positions(k: int, n: int) -> tuple[tuple[int, int, int], ...]:
    """List ``(i,p,A)`` with ``1<=i<=k`` and ``n+i=p**A``."""

    rows = []
    for i in range(1, k + 1):
        result = prime_power_base_exponent(n + i)
        if result is not None:
            rows.append((i, result[0], result[1]))
    return tuple(rows)


def lower_window_holds(k: int, d: int, n: int) -> bool:
    """The first exact inequality from ``ratio_window_four_nat``."""

    return pow(n + d + k, k) <= 4 * pow(n + k, k)


def upper_window_holds(k: int, d: int, n: int) -> bool:
    """The second exact inequality from ``ratio_window_four_nat``."""

    return 4 * pow(n + 1, k) <= pow(n + d + 1, k)


def _least_true(monotone: Callable[[int], bool]) -> int:
    if monotone(0):
        return 0
    lo, hi = 0, 1
    while not monotone(hi):
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if monotone(mid):
            hi = mid
        else:
            lo = mid
    return hi


def _greatest_true(monotone: Callable[[int], bool]) -> int:
    if not monotone(0):
        return -1
    lo, hi = 0, 1
    while monotone(hi):
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if monotone(mid):
            lo = mid
        else:
            hi = mid
    return lo


@dataclass(frozen=True)
class CrossingBand:
    k: int
    d: int
    lower: int
    upper: int

    @property
    def width(self) -> int:
        return max(0, self.upper - self.lower + 1)

    def values(self) -> range:
        return range(self.lower, self.upper + 1)


def exact_crossing_band(k: int, d: int) -> CrossingBand:
    if k <= 0 or d <= 0:
        raise ValueError("k and d must be positive")
    lower = _least_true(lambda n: lower_window_holds(k, d, n))
    upper = _greatest_true(lambda n: upper_window_holds(k, d, n))
    band = CrossingBand(k, d, lower, upper)
    # Endpoint maximality/minimality is part of every reproduction run.
    assert lower_window_holds(k, d, lower)
    assert lower == 0 or not lower_window_holds(k, d, lower - 1)
    if upper >= 0:
        assert upper_window_holds(k, d, upper)
        assert not upper_window_holds(k, d, upper + 1)
    return band


def factorial_valuation(n: int, p: int) -> int:
    if n < 0 or p < 2:
        raise ValueError("invalid factorial valuation input")
    value = 0
    power = p
    while power <= n:
        value += n // power
        power *= p
    return value


def block_valuation(k: int, n: int, p: int) -> int:
    """``v_p((n+1)...(n+k))`` by exact floor sums."""

    return factorial_valuation(n + k, p) - factorial_valuation(n, p)


def block_valuation_direct(k: int, n: int, p: int) -> int:
    value = prod(range(n + 1, n + k + 1))
    exponent = 0
    while value % p == 0:
        value //= p
        exponent += 1
    return exponent


def valuation_discrepancy(k: int, n: int, d: int, p: int) -> int:
    return block_valuation(k, n + d, p) - block_valuation(k, n, p)


def valuation_discrepancy_by_powers(k: int, n: int, d: int, p: int) -> int:
    """Same discrepancy as a sum of four floor/carry terms."""

    total = 0
    power = p
    top = n + d + k
    while power <= top:
        total += (n + d + k) // power - (n + d) // power
        total -= (n + k) // power - n // power
        power *= p
    return total


def target_valuation(p: int) -> int:
    return 2 if p == 2 else 0


@dataclass(frozen=True)
class ValuationCheck:
    passes: bool
    first_failure: int | None
    discrepancy: int | None


@dataclass(frozen=True)
class PrimePowerEndpointCheck:
    """Exact arithmetic behind the Lean prime-power endpoint theorem."""

    p: int
    exponent: int
    k: int
    d: int
    endpoint: int
    factorial_baseline: int
    lower_valuation: int
    upper_valuation: int

    @property
    def valuation_discrepancy(self) -> int:
        return self.upper_valuation - self.lower_valuation


@dataclass(frozen=True)
class InternalPrimePowerPositionCheck:
    """Exact local valuations when the lower owner ``n+i`` is ``p^A``."""

    p: int
    exponent: int
    k: int
    d: int
    i: int
    n: int
    lower_valuation: int
    upper_valuation: int
    split_factorial_baseline: int

    @property
    def valuation_discrepancy(self) -> int:
        return self.upper_valuation - self.lower_valuation


def check_small_prime_system(
    k: int, n: int, d: int, primes: Iterable[int] | None = None
) -> ValuationCheck:
    if primes is None:
        primes = primes_through(k)
    for p in primes:
        discrepancy = valuation_discrepancy(k, n, d, p)
        assert discrepancy == valuation_discrepancy_by_powers(k, n, d, p)
        if discrepancy != target_valuation(p):
            return ValuationCheck(False, p, discrepancy)
    return ValuationCheck(True, None, None)


def check_prime_power_endpoint(
    p: int, exponent: int, k: int, d: int
) -> PrimePowerEndpointCheck:
    """Replay the two quantified valuation bounds in the Lean core theorem.

    Preconditions are exactly ``1 <= k <= d < p**exponent``.  The returned
    assertions use Legendre floor sums, independently of Lean's factorization
    and concentration implementation.
    """

    endpoint = pow(p, exponent)
    if p not in primes_through(p):
        raise ValueError("p must be prime")
    if not (1 <= k <= d < endpoint):
        raise ValueError("need 1 <= k <= d < p**exponent")
    n = endpoint - k
    baseline = factorial_valuation(k - 1, p)
    lower = block_valuation(k, n, p)
    upper = block_valuation(k, n + d, p)
    assert lower >= exponent + baseline
    assert upper <= exponent - 1 + baseline
    assert upper < lower
    return PrimePowerEndpointCheck(
        p,
        exponent,
        k,
        d,
        endpoint,
        baseline,
        lower,
        upper,
    )


def check_internal_prime_power_position(
    p: int, exponent: int, k: int, d: int, i: int
) -> InternalPrimePowerPositionCheck:
    """Reproduce the exact internal-owner correction under ``9*d<n``.

    The lower owner is fixed by ``n+i=p**exponent``.  The lower valuation is
    exactly ``A+v_p((i-1)!)+v_p((k-i)!)``.  Translation by ``p**A`` preserves
    the valuations of every positive upper offset, so the upper valuation is
    the shifted block valuation at ``d-i``.  These identities are diagnostic:
    they do not assert the full quotient-four equation.
    """

    endpoint = pow(p, exponent)
    if p not in primes_through(p):
        raise ValueError("p must be prime")
    if not (1 <= i <= k <= d):
        raise ValueError("need 1 <= i <= k <= d")
    if i >= endpoint:
        raise ValueError("the lower owner must define a natural starting point")
    n = endpoint - i
    if not 9 * d < n:
        raise ValueError("need the exact target-shaped bound 9*d<n")
    split = factorial_valuation(i - 1, p) + factorial_valuation(k - i, p)
    lower = block_valuation(k, n, p)
    upper = block_valuation(k, n + d, p)
    shifted_upper = block_valuation(k, d - i, p)
    assert lower == exponent + split
    assert upper == shifted_upper
    return InternalPrimePowerPositionCheck(
        p, exponent, k, d, i, n, lower, upper, split
    )


@dataclass(frozen=True)
class BandScan:
    band: CrossingBand
    survivors: tuple[int, ...]
    first_failure_histogram: tuple[tuple[int, int], ...]


def scan_band(k: int, d: int) -> BandScan:
    band = exact_crossing_band(k, d)
    primes = primes_through(k)
    survivors: list[int] = []
    histogram: dict[int, int] = {}
    for n in band.values():
        result = check_small_prime_system(k, n, d, primes)
        if result.passes:
            survivors.append(n)
        else:
            assert result.first_failure is not None
            histogram[result.first_failure] = histogram.get(result.first_failure, 0) + 1
    return BandScan(band, tuple(survivors), tuple(sorted(histogram.items())))


def direct_block(k: int, n: int) -> int:
    return prod(range(n + 1, n + k + 1))


def named_fixture_report() -> tuple[dict[str, object], ...]:
    rows = []
    for k, n, d in ((984, 3_177_026, 4_480), (244, 48_502, 277)):
        band = exact_crossing_band(k, d)
        result = check_small_prime_system(k, n, d)
        rows.append(
            {
                "k": k,
                "n": n,
                "d": d,
                "band_lower": band.lower,
                "band_upper": band.upper,
                "in_band": band.lower <= n <= band.upper,
                "valuation_passes": result.passes,
                "first_failure": result.first_failure,
                "failure_discrepancy": result.discrepancy,
            }
        )
    return tuple(rows)


def structured_grid(
    k_values: Iterable[int], multipliers: Iterable[int]
) -> Iterator[dict[str, object]]:
    for k in k_values:
        for multiplier in multipliers:
            d = multiplier * k
            scan = scan_band(k, d)
            yield {
                "k": k,
                "d": d,
                "multiplier": multiplier,
                "width": scan.band.width,
                "survivors": len(scan.survivors),
                "first": scan.survivors[:3],
            }


def run_report() -> dict[str, object]:
    fixtures = named_fixture_report()
    grid = tuple(structured_grid(range(16, 65), (1, 2, 3, 5, 8, 13)))
    return {
        "fixtures": fixtures,
        "grid_rows": len(grid),
        "grid_zero_survivor_rows": sum(row["survivors"] == 0 for row in grid),
        "grid": grid,
    }


if __name__ == "__main__":
    report = run_report()
    print("fixtures", report["fixtures"])
    print(
        "grid",
        report["grid_rows"],
        "zero-survivor rows",
        report["grid_zero_survivor_rows"],
    )
    for row in report["grid"]:
        print(row)
