#!/usr/bin/env python3
"""
Exact-arithmetic experiments for the prefix-three finiteness note (Erdos 686, N=4, small k).

Setting: k in [5,15], c = 1/(4^{1/k}-1), window (W):
    (A+d+k-1)^k <= 4*(A+k-1)^k  and  4*A^k <= (A+d)^k
raw rows: A+t | G_t(d) = prod_{i=0}^{k-1} (d-t+i),  t = 0..k-1.

Experiments:
  E1  rational enclosure of c(k); verify window => 0 < c*d - A < k on all scan hits
  E2  survivor scan (W & R0 & R1 & R2), plus R0&R1 two-row survivors
  E3  shape analysis of survivors (minimal support of each row)
  E4  kappa2(k) = min |J c^2 - D c - tau| and B2(k)
  E5  kappa1(k,T) = min_{g<=T} dist(g c, Z)/g and B1(k,T)
  E6  verify the k=7,q=4 saturation counter-datum
  E7  verify the (2,2) near-integer identity on found support-2 row pairs
"""
import sys, math, json
from fractions import Fraction
from math import gcd

PREC = 10**50  # scale for integer enclosure of c

def c_enclosure(k):
    """Return (lo, hi) Fractions with lo < c(k) < hi, width ~ 1/PREC.
    c is the positive root of (x+1)^k = 4 x^k."""
    # f(x) = 4x^k - (x+1)^k ; f(c)=0, f increasing for large x? check sign:
    # at x -> infty, 4x^k dominates => f>0; at x=cd small f<0. Bisect on integers n/PREC.
    lo, hi = 1, 20 * PREC  # c in (1,20)
    lo *= PREC // PREC
    lo = PREC  # x=1
    f = lambda num: 4 * num**k - (num + PREC)**k  # x = num/PREC
    assert f(lo) < 0 and f(hi) > 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return Fraction(lo, PREC), Fraction(hi, PREC)

def window_ok(A, d, k):
    return (A + d + k - 1)**k <= 4 * (A + k - 1)**k and 4 * A**k <= (A + d)**k

def row_ok(A, d, k, t):
    r = 1
    M = A + t
    for i in range(k):
        r = (r * (d - t + i)) % M
        if r == 0 and i < k - 1:
            # keep multiplying (still fine), but can short-circuit
            return True
    return r == 0

def scan(k, dmax, clo, chi, need_rows=(0, 1, 2)):
    """Return survivors of window + rows in need_rows, and count of R0-only hits.

    Uses (W) <=> 0 < c*d - A < k-1 (proved in the note; spot-verified below with
    the exact integer inequalities on every R0 hit)."""
    survivors = []
    r0_count = 0
    r01 = []
    ln, ld = clo.numerator, clo.denominator
    hn, hd = chi.numerator, chi.denominator
    for d in range(max(k + 3, 5), dmax + 1):
        top = (ln * d) // ld  # floor(clo*d) = floor(cd) (enclosure width tiny)
        for A in range(top, top - k + 1, -1):
            if A < 2:
                continue
            # exact rational window check: A < c d and c d < A + k - 1
            if not (A * ld < ln * d and hn * d < (A + k - 1) * hd):
                continue
            if not row_ok(A, d, k, 0):
                continue
            r0_count += 1
            # E1 cross-check on R0 hits: rational window <=> exact integer (W)
            assert window_ok(A, d, k), ("window mismatch", k, d, A)
            if not row_ok(A, d, k, 1):
                continue
            r01.append((d, A))
            ok = all(row_ok(A, d, k, t) for t in need_rows)
            if ok:
                survivors.append((d, A))
    return survivors, r0_count, r01

def min_support(A, d, k, t, maxsize=4):
    """Minimal number of window elements whose product is divisible by A+t."""
    from itertools import combinations
    M = A + t
    elems = [d - t + i for i in range(k)]
    for size in range(1, maxsize + 1):
        for comb in combinations(range(k), size):
            p = 1
            for i in comb:
                p *= elems[i]
            if p % M == 0:
                return size, comb
    return None, None

def shape_report(A, d, k, tmax=3):
    rep = []
    for t in range(tmax):
        sz, comb = min_support(A, d, k, t, maxsize=5)
        M = A + t
        gcds = [gcd(M, d - t + i) for i in range(k)]
        rep.append(dict(t=t, M=M, support=sz, comb=comb, gcds=gcds))
    return rep

def kappa2(k, clo, chi, Jmax, Dmax_, taumax):
    """min |J c^2 - D c - tau| over |J|<=Jmax, |D|<=Dmax_, 1<=tau<=taumax, exactly (interval)."""
    c = (clo + chi) / 2
    w = chi - clo
    best = None
    c2 = c * c
    for J in range(-Jmax, Jmax + 1):
        for D in range(-Dmax_, Dmax_ + 1):
            base = J * c2 - D * c
            # tau nearest to base minimizes |base - tau| over integer tau in [1,taumax]
            for tau in set([max(1, min(taumax, int(base))), max(1, min(taumax, int(base) + 1))]):
                v = abs(base - tau)
                if best is None or v < best[0]:
                    best = (v, J, D, tau)
    # error from enclosure width: |d/dc (J c^2 - D c)| <= 2 Jmax c + Dmax
    err = (2 * Jmax * c + Dmax_) * w
    return best, err

def kappa1(k, clo, chi, T):
    """min over 1<=g<=T of dist(g c, Z)/g."""
    c = (clo + chi) / 2
    best = None
    for g in range(1, T + 1):
        x = c * g
        fr = x - int(x)
        v = min(fr, 1 - fr) / g
        if best is None or v < best[0]:
            best = (v, g)
    return best

def main():
    out = {}
    odd_ks = [5, 7, 9, 11, 13, 15]
    enclosures = {}
    for k in odd_ks:
        clo, chi = c_enclosure(k)
        enclosures[k] = (clo, chi)
        print(f"[E1] k={k}: c ~= {float(clo):.12f} (deg over Q = {k})")

    dmax_by_k = {5: 200000, 7: 100000, 9: 60000, 11: 60000, 13: 60000, 15: 60000}
    all_surv = {}
    for k in odd_ks:
        clo, chi = enclosures[k]
        dmax = dmax_by_k[k]
        surv, r0c, r01 = scan(k, dmax, clo, chi)
        all_surv[k] = (surv, r01)
        maxd3 = max((d for d, A in surv), default=0)
        maxd2 = max((d for d, A in r01), default=0)
        print(f"[E2] k={k} dmax={dmax}: R0 hits={r0c}, R0&R1 survivors={len(r01)} (max d={maxd2}), "
              f"R0&R1&R2 survivors={len(surv)} (max d={maxd3})")
        for d, A in surv:
            print(f"      survivor k={k} d={d} A={A}")

    print()
    for k in odd_ks:
        surv, r01 = all_surv[k]
        clo, chi = enclosures[k]
        c = float((clo + chi) / 2)
        for d, A in surv:
            rep = shape_report(A, d, k, tmax=3)
            supp = [r['support'] for r in rep]
            print(f"[E3] k={k} d={d} A={A} eps={c*d-A:.3f} supports(t=0,1,2)={supp}")
            for r in rep:
                print(f"      t={r['t']} M={r['M']} supp={r['support']} elems(comb)={r['comb']} gcds={r['gcds']}")

    print()
    for k in odd_ks:
        clo, chi = enclosures[k]
        best, err = kappa2(k, clo, chi, Jmax=2 * k, Dmax_=4 * k, taumax=k - 1)
        v, J, D, tau = best
        c = (clo + chi) / 2
        B2 = (5 * k * k * c * c / v + k) / c
        print(f"[E4] k={k}: kappa2={float(v):.3e} at (J,Delta,tau)=({J},{D},{tau}), encl-err<={float(err):.1e}, B2(k)~{float(B2):.3e}")

    print()
    for k in odd_ks:
        clo, chi = enclosures[k]
        for T in (100, 1000):
            best = kappa1(k, clo, chi, T)
            v, g = best
            c = (clo + chi) / 2
            B1 = (c + 3) * k / v
            print(f"[E5] k={k} T={T}: kappa1={float(v):.3e} at g={g}, B1(k,T)~{float(B1):.3e}")

    # E6: k=7, q=4 datum
    print()
    k, q, d, u = 7, 4, 302, 135
    A = (q + 1) * d - u
    print(f"[E6] k=7 q=4 datum: A={A}, window_ok={window_ok(A, d, k)}")
    for t in range(3):
        print(f"      raw row t={t}: (A+t)|G_t = {row_ok(A, d, k, t)}")
    lam = q + 1
    # affine saturation at t: M | q^k * affineResidualPoly(k,q,u,t), affine = prod(u+(q+1)s-(q+2)t)
    for t in range(3):
        M = A + t
        aff = 1
        for s in range(k):
            aff *= (u + (q + 1) * s - (q + 2) * t)
        sat = (q**k * aff) % M == 0
        print(f"      affine saturation t={t}: M | q^k*affine = {sat} (affine={aff})")

    # E7: verify (2,2) identity on support-2 row pairs among R0&R1 survivors
    print()
    for k in odd_ks:
        surv, r01 = all_surv[k]
        clo, chi = enclosures[k]
        c = (clo + chi) / 2
        checked = 0
        for d, A in r01:
            if d < 3 * k:
                continue
            s0, c0 = min_support(A, d, k, 0, maxsize=2)
            s1, c1 = min_support(A, d, k, 1, maxsize=2)
            if s0 == 2 and s1 == 2:
                a, b = (d + c0[0]), (d + c0[1])
                a1, b1 = (d - 1 + c1[0]), (d - 1 + c1[1])
                F = a * b // A
                F1 = a1 * b1 // (A + 1)
                J = F - F1
                Delta = (c0[0] + c0[1]) - (c1[0] - 1 + c1[1] - 1)
                pred = Fraction(Delta) / c + Fraction(1) / (c * c)
                resid = float(J - pred)
                bound = 5 * k * k / (float(c) * d - k)
                print(f"[E7] k={k} d={d} A={A}: J={J} Delta={Delta} |J-Delta/c-1/c^2|={abs(resid):.4f} "
                      f"bound={bound:.4f} OK={abs(resid) <= bound}")
                checked += 1
                if checked > 6:
                    break

if __name__ == "__main__":
    main()
