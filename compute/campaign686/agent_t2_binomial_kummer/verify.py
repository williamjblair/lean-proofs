"""Exact hostile verifier for the large-prime component and Lucas lanes.

Only Python integers and ``math.comb`` are used.  No floating point enters
any asserted check.
"""

from __future__ import annotations

from math import comb, factorial, prod


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    q = 2
    while q * q <= n:
        if n % q == 0:
            return False
        q += 1
    return True


def next_prime(n: int) -> int:
    p = n
    while not is_prime(p):
        p += 1
    return p


def valuation(n: int, p: int) -> int:
    assert n > 0 and is_prime(p)
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def unit_mod_prime(n: int, p: int) -> int:
    return (n // p ** valuation(n, p)) % p


def block(k: int, n: int) -> int:
    return prod(n + i for i in range(1, k + 1))


def binomial_block(k: int, n: int) -> int:
    return factorial(k) * comb(n + k, k)


def lucas_delta(p: int, a: int, x: int) -> int:
    q = p**a
    return comb(x + q - 1, q - 1) % p


def dominance_lhs(k: int, d: int) -> int:
    return (13 * k - 6) * d + 18 * (k - 1)


def dominance_rhs(p: int, e: int) -> int:
    return 6 * p ** (2 * e)


def verify_block_binomial_bridge() -> None:
    for k in range(0, 35):
        for n in range(0, 80):
            assert block(k, n) == binomial_block(k, n)


def verify_lucas_delta_and_unit_formula() -> None:
    """Check the delta and the stronger exact Kummer/unit pattern.

    If ``x=q*s+r`` with ``0<r<q``, then exact factor cancellation gives

      v_p C(x+q-1,q-1) = a-v_p(r)+v_p(s+1)

    and the p-free unit is ``unit(s+1)/unit(r)`` modulo p.
    The proof artifact banks only the simpler Lucas delta consequence.
    """

    for p in (3, 5, 7, 11, 13, 17, 19):
        for a in range(1, 5):
            q = p**a
            if q > 10_000:
                continue
            if q <= 300:
                xs = range(0, 12 * q + 1)
            else:
                residues = {0, 1, 2, p, p + 1, q // p, q - 2, q - 1}
                quotients = {0, 1, 2, p - 1, p, p + 1, 17}
                xs = sorted({q * s + r for s in quotients for r in residues})
            for x in xs:
                expected = 1 if x % q == 0 else 0
                assert lucas_delta(p, a, x) == expected
                if x and x % q:
                    s, r = divmod(x, q)
                    value = comb(x + q - 1, q - 1)
                    expected_v = a - valuation(r, p) + valuation(s + 1, p)
                    assert valuation(value, p) == expected_v
                    lhs = unit_mod_prime(value, p)
                    rhs = unit_mod_prime(s + 1, p) * pow(
                        unit_mod_prime(r, p), -1, p
                    ) % p
                    assert lhs == rhs


def verify_lucas_endpoint_restriction() -> None:
    # Exhaust the modular implication on complete residue grids.  This is not
    # advertised as a congruence closure: the surviving nonzero-residue pairs
    # are abundant.
    for p, a in ((5, 1), (7, 1), (11, 1), (5, 2), (7, 2), (5, 3)):
        q = p**a
        values = [lucas_delta(p, a, x) for x in range(q)]
        survivors = 0
        for x in range(q):
            for y in range(q):
                if values[y] == (4 * values[x]) % p:
                    assert x != 0 and y != 0
                    survivors += 1
        assert survivors == (q - 1) ** 2


def kummer_equation_condition(p: int, a: int, n: int, d: int) -> bool:
    q = p**a
    s, r = divmod(n, q)
    upper_s, upper_r = divmod(n + d, q)
    if r == 0 or upper_r == 0:
        return False
    left = (upper_s + 1) * r
    right = (s + 1) * upper_r
    v_left = valuation(left, p)
    v_right = valuation(right, p)
    return v_left == v_right and (
        left // p**v_left - 4 * (right // p**v_right)
    ) % p == 0


def verify_kummer_equation_restriction() -> None:
    """Exhaust the first two quotient digits for p=5,a=1.

    This condition is exactly valuation equality plus the p-free unit equation
    forced by an integer quotient of four.  It is stronger than the endpoint
    delta but leaves many survivors, so it is not a congruence closure.
    """

    p, a, q, k = 5, 1, 5, 4
    total = survivors = 0
    for s in range(25):
        for upper_s in range(25):
            for r in range(1, q):
                for upper_r in range(1, q):
                    n = q * s + r
                    upper = q * upper_s + upper_r
                    d = upper - n
                    if d < k:
                        continue
                    total += 1
                    lower_binom = comb(n + q - 1, q - 1)
                    upper_binom = comb(upper + q - 1, q - 1)
                    direct = (
                        valuation(upper_binom, p) == valuation(lower_binom, p)
                        and unit_mod_prime(upper_binom, p)
                        == 4 * unit_mod_prime(lower_binom, p) % p
                    )
                    compressed = kummer_equation_condition(p, a, n, d)
                    assert compressed == direct
                    survivors += compressed
    assert (total, survivors) == (4728, 774)
    # Endpoint-only data can fail the new restriction.
    assert 1 % q and (1 + 5) % q
    assert not kummer_equation_condition(5, 1, 1, 5)
    # It remains far from a closure, even with d>=k.
    assert kummer_equation_condition(5, 1, 1, 7)


def verify_exact_power_bracket() -> None:
    # The Lean proof is uniform; this is an independent, exact regression.
    for k in range(1, 5001):
        assert (13 * k + 18) ** k < 4 * (13 * k) ** k


def verify_upper_window_linearization() -> None:
    # Exhaust every small tuple satisfying only the upper endpoint window.
    for k in range(1, 45):
        for n in range(0, 180):
            for d in range(1, 180):
                if 4 * (n + 1) ** k <= (n + d + 1) ** k:
                    assert 18 * (n + 1) < 13 * k * d


def verify_infinite_family_dominance() -> None:
    # Both p=k (when k is prime) and the first p>k are checked.  Exponents
    # 2..8 cover the minimum boundary and higher powers independently.
    for k in range(16, 2501):
        bases = {next_prime(k)}
        if is_prime(k):
            bases.add(k)
        for p in bases:
            assert p >= k
            for e in range(2, 9):
                d = p**e
                assert 3 * k <= d
                assert dominance_lhs(k, d) <= dominance_rhs(p, e)
        # The size-form corollary also includes exponent-one prime gaps once
        # p=d is at least 3k.
        p_large = next_prime(3 * k)
        assert p_large > k and 3 * k <= p_large
        assert dominance_lhs(k, p_large) <= dominance_rhs(p_large, 1)


def verify_proper_component_examples_and_boundaries() -> None:
    # e=1 is not automatic at the smallest boundary.
    assert dominance_lhs(16, 17) > dominance_rhs(17, 1)
    # It can nevertheless close when the prime is large, even if p^e is a
    # proper divisor of d rather than the whole gap.
    assert 101 < 2 * 101
    assert dominance_lhs(16, 2 * 101) <= dominance_rhs(101, 1)
    # Equality is accepted by the dominance premise; the contradiction later
    # remains strict because the endpoint ratio bound is strict.  Search a
    # wide exact box and retain every equality without weakening <= to <.
    equalities = []
    for k in range(16, 101):
        for p in range(k, 251):
            if not is_prime(p):
                continue
            for e in range(1, 4):
                pe = p**e
                for mult in range(1, 9):
                    d = mult * pe
                    if dominance_lhs(k, d) == dominance_rhs(p, e):
                        equalities.append((k, p, e, d))
    # The logic does not depend on whether this finite search happens to find
    # equality; this check ensures equality cases, if found, obey the premise.
    for k, p, e, d in equalities:
        assert dominance_lhs(k, d) <= dominance_rhs(p, e)
    # d=k is not smuggled into this lane: no prime p>=k can divide d unless
    # p=k is prime, and at e=1 its dominance fails throughout this range.
    for k in range(16, 1000):
        if is_prime(k):
            assert dominance_lhs(k, k) > dominance_rhs(k, 1)


def verify_chain_has_no_arithmetic_model() -> None:
    """Exhaust the post-lift inequalities, independently of the equation."""

    for k in range(16, 45):
        for d in range(k, 100):
            for p in range(k, 150):
                if not is_prime(p):
                    continue
                for e in range(1, 4):
                    if d % (p**e):
                        continue
                    if dominance_lhs(k, d) > dominance_rhs(p, e):
                        continue
                    p2 = p ** (2 * e)
                    for i in range(1, k + 1):
                        # The exact chain assumes 9d<n, the upper endpoint
                        # bound, and p^(2e)<=3(n+i)-d.  No n can satisfy all.
                        for n in range(9 * d + 1, 13 * k * d // 18 + 2):
                            if 18 * (n + 1) >= 13 * k * d:
                                continue
                            assert p2 > 3 * (n + i) - d


def mandatory_fixture_report() -> dict[str, object]:
    fixtures = {
        "deep_984": (984, 3_177_026, 4480),
        "cluster_48502": (244, 48_502, 277),
    }
    out: dict[str, object] = {}
    for name, (k, n, d) in fixtures.items():
        eligible = []
        for p in range(k, d + 1):
            if is_prime(p) and d % p == 0:
                e = valuation(d, p)
                eligible.append(
                    (p, e, dominance_lhs(k, d) <= dominance_rhs(p, e))
                )
        out[name] = eligible
    # k=9,15 telescope fixtures have d=1 and lie outside k>=16,d>=k.
    out["odd_telescopes_in_domain"] = False
    return out


def run_all() -> None:
    verify_block_binomial_bridge()
    verify_lucas_delta_and_unit_formula()
    verify_lucas_endpoint_restriction()
    verify_kummer_equation_restriction()
    verify_exact_power_bracket()
    verify_upper_window_linearization()
    verify_infinite_family_dominance()
    verify_proper_component_examples_and_boundaries()
    verify_chain_has_no_arithmetic_model()
    report = mandatory_fixture_report()
    assert report == {
        "deep_984": [],
        "cluster_48502": [(277, 1, False)],
        "odd_telescopes_in_domain": False,
    }


if __name__ == "__main__":
    run_all()
    print("all exact large-prime-component and Lucas checks passed")
