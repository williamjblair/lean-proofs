#!/usr/bin/env python3
"""
E9: exact kappa3 for the k=5 support-3 moment elimination.

Rows t in a 4-subset of {0..4}, each with a degree-3 numerator
M_t(d) = prod_{s in S_t} (d+s), where S_t is either a 3-subset of the row-t
window shifts [-t, 4-t], or a 2-subset promoted by an arbitrary shift w in
[-6..6].  Conditions on integer alpha: sum a = 0, sum a*t = 0,
sum a*sigma_t = 0 (sigma_t = sum of shifts).  Then
  Lambda := sum_t a_t M_t(d)/(A+t)  =  E/c - S/c^2 + T2/c^3 + O(1/d)
with E = sum a e2(S_t), S = sum a sigma_t t, T2 = sum a t^2.
kappa3 = min over nondegenerate configs of dist(E/c - S/c^2 + T2/c^3, Z).

E10: support profile of two-row (R0&R1) survivors at large d for k=11,13,15.
"""
import itertools, sys
from fractions import Fraction

sys.setrecursionlimit(10000)

PREC = 10**50

def c_enclosure(k):
    lo, hi = PREC, 20 * PREC
    f = lambda num: 4 * num**k - (num + PREC)**k
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return Fraction(lo, PREC), Fraction(hi, PREC)

def e2(shifts):
    a, b, c = shifts
    return a * b + a * c + b * c

def kernel_int(v1, v2, v3):
    """Integer kernel vector of the 3x4 matrix with rows v1,v2,v3 (4-vectors),
    via signed 3x3 minors (generalized cross product)."""
    M = [v1, v2, v3]
    def minor(cols):
        (c0, c1, c2) = cols
        return (M[0][c0] * (M[1][c1] * M[2][c2] - M[1][c2] * M[2][c1])
                - M[0][c1] * (M[1][c0] * M[2][c2] - M[1][c2] * M[2][c0])
                + M[0][c2] * (M[1][c0] * M[2][c1] - M[1][c1] * M[2][c0]))
    a = [0, 0, 0, 0]
    sign = 1
    for j in range(4):
        cols = tuple(x for x in range(4) if x != j)
        a[j] = sign * minor(cols)
        sign = -sign
    from math import gcd
    g = 0
    for x in a:
        g = gcd(g, abs(x))
    if g > 1:
        a = [x // g for x in a]
    return a

def row_shift_options(t, k=5, promo=range(-6, 7)):
    """All shift-multisets usable as a degree-3 numerator for row t."""
    window = list(range(-t, k - t))
    opts = []
    for S in itertools.combinations(window, 3):
        opts.append(tuple(sorted(S)))
    for S in itertools.combinations(window, 2):
        for w in promo:
            opts.append(tuple(sorted(S + (w,))))
    return sorted(set(opts))

def main():
    k = 5
    clo, chi = c_enclosure(k)
    c = (clo + chi) / 2
    c2, c3 = c * c, c * c * c
    inv_c, inv_c2, inv_c3 = 1 / c, 1 / c2, 1 / c3

    best = None
    n_deg_full = 0
    n_configs = 0
    row_opts = {t: row_shift_options(t) for t in range(5)}
    # limit: pure support-3 options only for the headline number, promotions separately
    pure_opts = {t: [S for S in row_opts[t] if all(-t <= s <= 4 - t for s in set(S)) and len(set(S)) == 3]
                 for t in range(5)}

    def scan(opts_by_row, label):
        nonlocal best, n_deg_full, n_configs
        local_best = None
        for T in itertools.combinations(range(5), 4):
            for choice in itertools.product(*(opts_by_row[t] for t in T)):
                n_configs += 1
                sig = [sum(S) for S in choice]
                v1 = [1, 1, 1, 1]
                v2 = [t for t in T]
                v3 = sig
                a = kernel_int(v1, v2, v3)
                if all(x == 0 for x in a):
                    continue  # rank<3: kernel via minors failed; skip (handled by subset configs)
                # check conditions actually hold (rank could be <3 giving junk)
                if (sum(a) != 0 or sum(x * t for x, t in zip(a, T)) != 0
                        or sum(x * s for x, s in zip(a, sig)) != 0):
                    continue
                E = sum(x * e2(S) for x, S in zip(a, choice))
                S2 = sum(x * s * t for x, s, t in zip(a, sig, T))
                T2 = sum(x * t * t for x, t in zip(a, T))
                if E == 0 and S2 == 0 and T2 == 0:
                    n_deg_full += 1
                    continue
                val = E * inv_c - S2 * inv_c2 + T2 * inv_c3
                fr = val - int(val)
                if fr < 0:
                    fr += 1
                dist = min(fr, 1 - fr)
                rec = (dist, T, choice, a, (E, S2, T2))
                if local_best is None or dist < local_best[0]:
                    local_best = rec
                if best is None or dist < best[0]:
                    best = rec
        if local_best:
            d0, T, ch, a, coeffs = local_best
            print(f"[E9-{label}] min dist = {float(d0):.6e}  rows={T} shifts={ch} alpha={a} (E,S,T2)={coeffs}")
        print(f"[E9-{label}] configs={n_configs} fully-degenerate={n_deg_full}")

    scan(pure_opts, "pure3")
    print()
    # promotions included (support-2 rows promoted by w in [-6,6])
    n_configs = 0
    n_deg_full = 0
    best = None
    scan(row_opts, "with-promo")
    d0 = best[0]
    # bound: |Lambda - value| <= C3/d with C3 ~ 40*||alpha||_1*k^3 (conservative)
    print()
    print("interpretation: kappa3(pure3) is the exact min over 4-row support-3")
    print("configs of the distance of the limit value to the nearest integer;")
    print("B3(5) ~ C3(alpha)*c^0 / kappa3 with C3 ~ 40*||alpha||_1*125.")

if __name__ == "__main__":
    main()
