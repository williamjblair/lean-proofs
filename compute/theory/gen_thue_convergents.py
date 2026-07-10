#!/usr/bin/env python3
"""
Erdos 686, odd-k campaign: uniform machine-readable convergent data for
alpha_k = 4^(1/k), k in {5, 7, 9, 11, 13, 15}.

Writes compute/artifacts/thue_convergents_k{K}.json with, for every index
i = 0..340, the row  [p_i, q_i, D_i, a_{i+1}]  where p_i/q_i is the i-th
continued-fraction convergent of 4^(1/k), D_i = p_i^k - 4*q_i^k (its sign is
the exact side certificate: D_i < 0  <=>  i even), and a_{i+1} is the next
partial quotient.  All integers are exact (JSON bignums; Python json reads
them back losslessly).

EXACTNESS: no floating point anywhere.  Term extraction uses an exact
rational sandwich  r/10^D < alpha < (r+1)/10^D  from an integer k-th root
(strictness: 4*10^(kD) = 2^(2kD+2) * 5^(kD) is never a k-th power since
2kD+2 is not divisible by k for odd k... verified per instance by the strict
integer comparisons), then the common CF prefix of the two endpoints.

CERTIFICATION (the proof objects, independent of extraction):
  * straddle certificates: every partial quotient a_{i+1} is pinned by TWO
    integer sign checks of u^k - 4 v^k at the semiconvergents
      s_a     = (a p_i + p_{i-1}, a q_i + q_{i-1})   [a = a_{i+1}: far side,
                                                      = the (i+1)-convergent]
      s_{a+1}                                        [crossed alpha]
    (s_a is a Moebius, hence monotone, function of a and x -> x^k is
    strictly increasing, so the single sign flip certifies the floor);
  * sign alternation of D_i (minimal-polynomial side test);
  * determinant identity p_i q_{i-1} - p_{i-1} q_i = (-1)^(i-1)  (=> the
    convergents are in lowest terms).

BONUS CROSS-CHECK (uniform, all six k): the self-contained confinement
family (theorem in oddk_9/note.md Section 3) is enumerated to Y <= 10^100
with the per-k headline constant C_k, and the exact centered equation
P_k(X) = 4 P_k(Y), P_k(T) = T * prod_{j<=(k-1)/2} (T^2 - j^2), is checked on
every member: the only hits anywhere are the two d = 1 telescopes
(Y, X) = (7, 8) for k = 9 and (12, 13) for k = 15 (overlapping blocks,
outside the m >= n + k problem domain).
"""

import json
import os
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ARTIFACTS = os.path.normpath(os.path.join(HERE, "..", "artifacts"))

N_INDEX = 340                 # emit rows i = 0..N_INDEX
N_TERMS = N_INDEX + 2         # need a_0..a_{N_INDEX+1}
Y_LIMIT = 10 ** 100

# per-k headline pinning constants (exact rationals, PROVED in the per-k
# notes; for k = 15 the scan's margin constant 9/5 >= 1729/1000 is used)
HEADLINE_C = {
    5: F(61, 100),            # k5_third_row_note.md Section 6
    7: F(399, 500),           # oddk_7/note.md
    9: F(1031, 1000),         # oddk_9/note.md
    11: F(13, 10),            # oddk_11/note.md
    13: F(3, 2),              # oddk_13/note.md
    15: F(9, 5),              # oddk_15/note.md (margin over 1729/1000)
}
TELESCOPES = {9: (7, 8), 15: (12, 13)}   # d = 1 overlaps, k = 3(n+1)


def iroot(n, k):
    """floor(n**(1/k)) for n >= 0, pure integer arithmetic."""
    if n == 0:
        return 0
    r = 1 << ((n.bit_length() + k - 1) // k + 1)
    while True:
        r2 = ((k - 1) * r + n // r ** (k - 1)) // k
        if r2 >= r:
            break
        r = r2
    while r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r


def cf_of_fraction(num, den):
    terms = []
    while den:
        a = num // den
        terms.append(a)
        num, den = den, num - a * den
    return terms


def cf_terms(k, n_terms):
    """First n_terms partial quotients of 4^(1/k), exact."""
    digits = 500
    while True:
        r = iroot(4 * 10 ** (k * digits), k)
        assert r ** k < 4 * 10 ** (k * digits) < (r + 1) ** k   # strict
        lo = cf_of_fraction(r, 10 ** digits)
        hi = cf_of_fraction(r + 1, 10 ** digits)
        terms = []
        for a, b in zip(lo, hi):
            if a != b:
                break
            terms.append(a)
        if len(terms) >= n_terms:
            return terms[:n_terms]
        digits *= 2


def Pk(k, t):
    """Centered polynomial P_k(t) = t * prod (t^2 - j^2), exact."""
    r = t
    for j in range(1, (k - 1) // 2 + 1):
        r *= t * t - j * j
    return r


def process(k):
    t0 = time.time()
    terms = cf_terms(k, N_TERMS)
    assert terms[0] == 1 and all(a >= 1 for a in terms[1:])

    # convergents
    ps, qs = [], []
    pm1, pm2, qm1, qm2 = 1, 0, 0, 1
    for a in terms:
        p, q = a * pm1 + pm2, a * qm1 + qm2
        ps.append(p)
        qs.append(q)
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q

    # certificates -------------------------------------------------------
    D = []
    for i in range(len(ps)):
        d = ps[i] ** k - 4 * qs[i] ** k
        assert d != 0
        assert (d < 0) == (i % 2 == 0), f"k={k}: alternation fails at {i}"
        D.append(d)
    for i in range(1, len(ps)):
        assert ps[i] * qs[i - 1] - ps[i - 1] * qs[i] == (-1) ** (i - 1)
    assert 1 ** k < 4 < 2 ** k                      # a_0 = 1 floor bracket
    n_straddle = 0
    pprev, qprev = 1, 0
    for i in range(len(ps) - 1):
        a = terms[i + 1]
        u1, v1 = a * ps[i] + pprev, a * qs[i] + qprev
        u2, v2 = u1 + ps[i], v1 + qs[i]
        s1 = u1 ** k - 4 * v1 ** k
        s2 = u2 ** k - 4 * v2 ** k
        assert s1 != 0 and (s1 < 0) == ((i + 1) % 2 == 0)
        assert s2 != 0 and (s2 < 0) == (i % 2 == 0)
        n_straddle += 2
        pprev, qprev = ps[i], qs[i]

    m100 = next(i for i in range(len(qs)) if qs[i] > Y_LIMIT)
    amax = max(terms[:N_INDEX + 2])

    # bonus: self-contained confinement family + exact equation ----------
    C = HEADLINE_C[k]
    half = (k + 1) // 2                  # Y = n + half >= half
    fam = {}
    for m in range(m100 + 1):
        qm, qm1_ = qs[m], qs[m + 1]
        if qm1_ <= qm:
            continue
        capn, capd = C.numerator * (qm + qm1_), C.denominator
        g = 1
        while g * g * qm * capd < capn and g * qm < qm1_:
            if g * qm <= Y_LIMIT:
                fam.setdefault(g * qm, m)
            g += 1
        t = 1
        while t * qm * capd < capn:
            r = -((-(1 + t) * qm) // qm1_)
            Yc = r * qm1_ - t * qm
            if qm <= Yc < qm1_ and t * Yc * capd < capn and Yc <= Y_LIMIT:
                fam.setdefault(Yc, m)
            t += 1
        s = 2
        while s * qm * capd < capn:
            r = ((s - 1) * qm) // qm1_
            if r >= 1:
                Yc = s * qm - r * qm1_
                if qm <= Yc < qm1_ and s * Yc * capd < capn and Yc <= Y_LIMIT:
                    fam.setdefault(Yc, m)
            s += 1
    hits = []
    pairs = 0
    for Yc in fam:
        if Yc < half:
            continue
        X0 = iroot(4 * Yc ** k, k)
        p4 = 4 * Pk(k, Yc)
        for X in range(X0 - 2, X0 + 4):
            if X > Yc:
                pairs += 1
                if Pk(k, X) == p4:
                    hits.append((Yc, X))
    expected = [TELESCOPES[k]] if k in TELESCOPES else []
    assert all(X - Yc < k for (Yc, X) in hits), \
        f"k={k}: UNEXPECTED DISJOINT-BLOCK SOLUTION {hits}"
    assert hits in ([], expected), f"k={k}: unexpected hit set {hits}"

    out = {
        "k": k,
        "alpha": f"4^(1/{k})",
        "generated_by": "compute/theory/gen_thue_convergents.py",
        "columns": ["p_i", "q_i", "D_i = p_i^k - 4*q_i^k", "a_{i+1}"],
        "num_rows": N_INDEX + 1,
        "index_range": [0, N_INDEX],
        "cf_a0": terms[0],
        "certification": {
            "straddle_sign_checks": n_straddle,
            "alternation": "sign(D_i) = (-1)^(i+1) for all i",
            "determinant": "p_i q_(i-1) - p_(i-1) q_i = (-1)^(i-1) for all i",
        },
        "max_partial_quotient_to_341": amax,
        "argmax_partial_quotient": terms.index(amax),
        "first_index_q_exceeds_1e100": m100,
        "headline_C": [C.numerator, C.denominator],
        "selfcontained_family_size_to_1e100": len(fam),
        "equation_checks_on_family": pairs,
        "equation_hits": [list(h) for h in hits],
        "data": [[ps[i], qs[i], D[i], terms[i + 1]] for i in range(N_INDEX + 1)],
    }
    path = os.path.join(ARTIFACTS, f"thue_convergents_k{k}.json")
    with open(path, "w") as fh:
        json.dump(out, fh)
    print(f"[PASS] k={k:2d}: {N_INDEX+1} rows, a_max={amax} (at i="
          f"{terms.index(amax)}), q_i > 1e100 at i={m100}, "
          f"{n_straddle} straddles, family={len(fam)} (C={C}), "
          f"{pairs} eq checks, hits={hits if hits else 'none'}  "
          f"[{time.time()-t0:.1f}s]  -> {os.path.basename(path)} "
          f"({os.path.getsize(path)//1024} KiB)")
    return out


if __name__ == "__main__":
    total0 = time.time()
    for k in (5, 7, 9, 11, 13, 15):
        process(k)
    print(f"ALL SIX k DONE ({time.time()-total0:.1f}s); only equation hits "
          f"anywhere are the d=1 telescopes (k=9: (7,8); k=15: (12,13)) -- "
          f"both outside the m >= n+k problem domain")
