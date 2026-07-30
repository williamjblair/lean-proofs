"""Erdős #848 finite-side engine prototype.

Layered verification that f(N) = |A7(N)| for all N up to a bound M:
this file implements the shared core —
  1. U(M): all x <= M with x^2+1 non-squarefree, via root sieving
     (x ≡ ±r_p mod p^2 where r_p^2 ≡ -1 mod p^2, p ≡ 1 mod 4), plus the
     witness bookkeeping (smallest witness prime per x).
  2. Per-outsider compatibility counts: for an outsider x (witness >= 13),
     count / enumerate {a <= M : a ≡ 7 or 18 mod 25, mu(x*a+1) = 0}
     by sieving classes a ≡ -x^{-1} mod q^2 over primes q.
Everything is exact; the counts feed the clique-exclusion argument
(a clique containing an outsider x has size <= 1 + |compat(x) ∩ U|,
refined recursively when the crude bound is insufficient).

Validation: cross-check U(M) and compat counts against brute force for
M <= 20000.
"""
from __future__ import annotations
import sys
from sympy import sqrt_mod, isprime


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i:: i] = b"\x00" * len(sieve[i * i:: i])
    return [i for i in range(n + 1) if sieve[i]]


def roots_minus1_mod_p2(p):
    """r with r^2 ≡ -1 (mod p^2), p ≡ 1 mod 4 prime; returns (r, p^2 - r)."""
    r = sqrt_mod(-1, p)                      # root mod p
    # Hensel lift to mod p^2: r' = r - f(r)/f'(r), f = x^2+1
    p2 = p * p
    fr = (r * r + 1) % p2
    inv2r = pow(2 * r, p2 - p * (p - 1) - 1, p2) if False else pow(2 * r, -1, p2)
    r2 = (r - fr * inv2r) % p2
    assert (r2 * r2 + 1) % p2 == 0
    return r2, p2 - r2


def build_universe(M, pmax=None):
    """Return dict x -> smallest witness prime, for x <= M with x^2+1 not
    squarefree. pmax limits sieving primes (default: all p <= M; witnesses
    p > M would need p^2 | x^2+1 <= M^2+1, i.e. p^2 <= M^2+1 — a prime
    p in (M, sqrt(M^2+1)] is impossible except p^2 = x^2+1 (never, as
    x^2+1 is not a square for x >= 1); so p <= M suffices — proof:
    p^2 | x^2+1 and p > M >= x means p^2 > x^2+1 unless p^2 <= x^2+1;
    p > x forces p^2 >= (x+1)^2 > x^2+1. Hence all witnesses are <= x <= M."""
    witness = {}
    ps = primes_upto(pmax or M)
    for p in ps:
        if p % 4 != 1:
            continue
        p2 = p * p
        for r in roots_minus1_mod_p2(p):
            for x in range(r, M + 1, p2):
                if x >= 1 and x not in witness:
                    witness[x] = p
                elif x >= 1:
                    witness[x] = min(witness[x], p)
    return witness


def brute_universe(M):
    out = {}
    ps = primes_upto(M + 1)
    for x in range(1, M + 1):
        v = x * x + 1
        for p in ps:
            if p * p > v:
                break
            if v % (p * p) == 0:
                out[x] = p
                break
    return out


def compat_count_in_classes(x, M, primes, cls=(7, 18)):
    """Exact |{a <= M : a mod 25 in cls, (x*a+1) not squarefree}| by
    sieving a ≡ -x^{-1} (mod q^2) over primes q with q ∤ x, q^2 <= x*M+1;
    for q > sqrt(x*M+1)... impossible (q^2 | xa+1 <= xM+1). Exact via
    marking; memory M/25*2 bools."""
    import numpy as np
    marked = np.zeros(M + 1, dtype=bool)
    xM1 = x * M + 1
    for q in primes:
        if q * q > xM1:
            break
        if x % q == 0:
            continue
        q2 = q * q
        try:
            inv = pow(x, -1, q2)
        except ValueError:
            continue
        a0 = (-inv) % q2
        if a0 == 0:
            a0 = q2
        marked[a0:: q2] = True
    total = 0
    for c in cls:
        idx = range(c, M + 1, 25)
        total += int(marked[list(idx)].sum())
    return total


def validate(M=20000):
    print(f"validating universe at M={M} ...", flush=True)
    w1 = build_universe(M)
    w2 = brute_universe(M)
    assert w1 == w2, (len(w1), len(w2),
                      set(w1.items()) ^ set(w2.items()))
    n_out = sum(1 for x, p in w1.items() if p >= 13)
    print(f"  |U({M})| = {len(w1)}, outsiders(witness>=13) = {n_out}  OK")

    ps = primes_upto(2000)
    import random
    rng = random.Random(848)
    outs = [x for x, p in w1.items() if p >= 13]
    for x in rng.sample(outs, min(5, len(outs))):
        got = compat_count_in_classes(x, M, primes_upto(int((x * M + 1) ** 0.5) + 1))
        # brute force
        want = 0
        psb = primes_upto(int((x * M + 1) ** 0.5) + 1)
        for c in (7, 18):
            for a in range(c, M + 1, 25):
                v = x * a + 1
                for p in psb:
                    if p * p > v:
                        break
                    if v % (p * p) == 0:
                        want += 1
                        break
        assert got == want, (x, got, want)
        frac = got / (2 * (M // 25))
        print(f"  outsider x={x} (witness {w1[x]}): compat∩(A7∪A18) = {got} "
              f"({frac:.3f} of classes)  OK")
    print("validation PASSED")


if __name__ == "__main__":
    validate(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
