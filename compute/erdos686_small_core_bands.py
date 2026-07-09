#!/usr/bin/env python3
"""Band parameters for the Erdos 686 small-core d<=220 kernel certificates.

For each k in [5,15] the ratio window
    (n+d+k)^k <= 4*(n+k)^k   (hup)
    4*(n+1)^k <= (n+d+1)^k   (hlo)
pins n to a narrow band around d/(4^(1/k)-1).  We linearize both sides with
rational brackets of c = 4^(1/k):

  lower side (from hup): pick A/B > c with 4*B^k < A^k.  Then
      B*(n+d+k) < A*(n+k)  =>  B*d < (A-B)*(n+k)  =>  n >= B*d/(A-B) + 1 - k
      (integer floor division; matches `ratio_window_linearize_of_pow_bracket`).

  upper side (from hlo): pick A'/B' < c with A'^k < 4*B'^k.  Then
      A'*(n+1) < B'*(n+d+1)  =>  (A'-B')*(n+1) < B'*d
      =>  n + 1 <= (B'*d - 1) // (A'-B')
      (matches `ratio_window_upper_linearize_of_pow_bracket`).

The Lean certificate for each k quantifies over d in [k,220] and
n = nLo(k,d) + i, i < W_k, with
    nLo(k,d) = B*d // (A-B) + 1 - k   (Nat-truncated subtraction).

This script:
  * finds tight brackets (A,B) and (A',B') per k via Stern-Brocot search,
  * computes the exact band width W_k = max_d (nmax - nLo + 1),
  * independently rescans the full window (n up to 2500) and confirms every
    window triple lies in the band and matches the banked witness artifact
    (20779 triples, n_max 2271, first-failure histogram),
  * emits the Lean-ready parameter table.
"""

import json
import math
from fractions import Fraction

ART = "/Users/williamblair/personal/lean-proofs/compute/artifacts/small_core_witnesses.json"

D_MAX = 220
K_RANGE = range(5, 16)


def brackets(k, max_den=400):
    """Best fractions below/above c = 4^(1/k) with denominator <= max_den.

    Returns ((A_hi, B_hi), (A_lo, B_lo)) with A_hi/B_hi > c (4*B^k < A^k)
    and A_lo/B_lo < c (A^k < 4*B^k), each tightest for its denominator bound.
    """
    best_hi = None  # smallest fraction above c
    best_lo = None  # largest fraction below c
    for b in range(1, max_den + 1):
        # a/b > c  <=>  a^k > 4*b^k ; smallest such a
        a = math.isqrt(1)  # placeholder
        # integer k-th root of 4*b^k, then +1 until strict
        target = 4 * b ** k
        a = round(target ** (1.0 / k))
        while a ** k <= target:
            a += 1
        while (a - 1) ** k > target:
            a -= 1
        # now a^k > target >= (a-1)^k
        fa = Fraction(a, b)
        if best_hi is None or fa < best_hi:
            best_hi = fa
        a2 = a - 1
        if a2 ** k < target:  # strict below
            fa2 = Fraction(a2, b)
            if best_lo is None or fa2 > best_lo:
                best_lo = fa2
    return (best_hi.numerator, best_hi.denominator), (best_lo.numerator, best_lo.denominator)


def nat_sub(a, b):
    return a - b if a >= b else 0


def band(k, d, A, B, Ap, Bp):
    """(nLo, nmax) implied by the two linearizations for this (k, d)."""
    nlo = nat_sub(B * d // (A - B) + 1, k)          # Nat semantics of B*d/(A-B) + 1 - k
    nmax = (Bp * d - 1) // (Ap - Bp) - 1            # n+1 <= (Bp*d-1)//(Ap-Bp)
    return nlo, nmax


def main():
    art = json.load(open(ART))
    wit = art["witnesses"]
    assert len(wit) == 20779 == art["total_window_triples"]
    wit_by_k = {}
    for k, n, d, j in wit:
        wit_by_k.setdefault(k, []).append((n, d, j))

    print(f"{'k':>3} {'A':>5} {'B':>5} {'A\'':>5} {'B\'':>5} {'W':>4} {'D':>4} "
          f"{'grid':>6} {'wins':>6} {'nmax_seen':>9}")

    params = {}
    total_grid = 0
    for k in K_RANGE:
        (A, B), (Ap, Bp) = brackets(k)
        # exact bracket sanity
        assert 4 * B ** k < A ** k, (k, A, B)
        assert Ap ** k < 4 * Bp ** k, (k, Ap, Bp)

        # width over all d in [k, 220]
        W = 0
        for d in range(k, D_MAX + 1):
            nlo, nmax = band(k, d, A, B, Ap, Bp)
            W = max(W, nmax - nlo + 1)

        # coverage of banked witnesses
        nmax_seen = 0
        for n, d, j in wit_by_k.get(k, []):
            nlo, nmax = band(k, d, A, B, Ap, Bp)
            assert nlo <= n <= nmax, ("witness outside band", k, n, d, nlo, nmax)
            assert n < nlo + W
            nmax_seen = max(nmax_seen, n)

        D = D_MAX + 1 - k
        params[k] = (A, B, Ap, Bp, W, D)
        total_grid += D * W
        print(f"{k:>3} {A:>5} {B:>5} {Ap:>5} {Bp:>5} {W:>4} {D:>4} "
              f"{D*W:>6} {len(wit_by_k.get(k, [])):>6} {nmax_seen:>9}")

    print(f"total grid points: {total_grid}")

    # ---- independent full rescan: window truth + band containment ----
    def first_fail_row(k, n, d):
        for j in range(1, k + 1):
            prod = 1
            for i in range(1, k + 1):
                prod *= nat_sub(d + i, j)
            if prod % (n + j) != 0:
                return j
        return None

    hist = {}
    total = 0
    n_top = 0
    N_SCAN = 2500
    for k in K_RANGE:
        A, B, Ap, Bp, W, D = params[k]
        for d in range(k, D_MAX + 1):
            nlo, nmax = band(k, d, A, B, Ap, Bp)
            for n in range(0, N_SCAN + 1):
                if (n + d + k) ** k <= 4 * (n + k) ** k and \
                   4 * (n + 1) ** k <= (n + d + 1) ** k:
                    if n == 0:
                        continue  # artifact restricts to n >= 1
                    assert nlo <= n <= nmax, ("window point outside band", k, n, d)
                    j = first_fail_row(k, n, d)
                    assert j is not None and j <= 5, ("no small-row failure", k, n, d)
                    hist[j] = hist.get(j, 0) + 1
                    total += 1
                    n_top = max(n_top, n)

    print(f"rescan: total={total} n_max={n_top} hist={dict(sorted(hist.items()))}")
    assert total == 20779, total
    assert n_top == 2271, n_top
    assert {str(a): b for a, b in hist.items()} == art["expected_histogram"], hist

    # n=0 window points (excluded from artifact) must still be escaped rows,
    # since the Lean theorem quantifies over all n : Nat.
    zero_pts = []
    for k in K_RANGE:
        for d in range(k, D_MAX + 1):
            n = 0
            if (n + d + k) ** k <= 4 * (n + k) ** k and \
               4 * (n + 1) ** k <= (n + d + 1) ** k:
                zero_pts.append((k, d, first_fail_row(k, n, d)))
    print(f"n=0 window points: {zero_pts}")

    # window n-bound layer-1 check: 57^15 < 4*52^15 and resulting bound
    assert 57 ** 15 < 4 * 52 ** 15
    # 57*(n+1) < 52*(n+d+1), d<=220  =>  5*n < 52*d - 5 <= 11435  => n <= 2286
    print("layer-1 bracket 57/52 ok; n < 2287 (covers n_max 2271)")

    print("\nLean parameter table:")
    for k in K_RANGE:
        A, B, Ap, Bp, W, D = params[k]
        print(f"  k={k:2d}: A={A} B={B} (4*{B}^{k}<{A}^{k}), "
              f"A'={Ap} B'={Bp} ({Ap}^{k}<4*{Bp}^{k}), "
              f"nLo=({B}*d)/{A-B}+1-{k}, W={W}, D={D}")


if __name__ == "__main__":
    main()
