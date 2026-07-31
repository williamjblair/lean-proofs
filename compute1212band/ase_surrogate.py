#!/usr/bin/env python3
"""ASE surrogate measurement.

A dual staircase separator exists iff there is a chain c_1, ..., c_K with
c_i a BLOCK column of reservoir row r_i, and for each i the horizontal slab
between c_i and c_{i+1} containing NO climb column across the vertical gap
between rows r_i and r_{i+1}.  (Planar duality: the dual curve crosses row i
at a missing horizontal edge, then travels through the interface, which it can
only do where no vertical edge exists.)

We build a faithful miniature reservoir (semiprime rows with both factors >= Z
inside a height window of length <= Z, hence pairwise-coprime with disjoint
prime supports), compute the exact block and climb sets, and run the exact
reachability DP.  Boundary convention is GENEROUS to the adversary: a climb
column blocks travel only if it lies strictly between c_i and c_{i+1}.

Reports the DP depth reached (how many rows a partial staircase can traverse),
which is the graded statistic; full depth == staircase exists == ASE false at
these parameters.
"""
import sys
import numpy as np
from sympy import factorint

def build_rows(H, E, Z):
    """Semiprime rows in [H, H+E) with both prime factors >= Z."""
    rows = []
    for r in range(H | 1, H + E, 2):
        f = factorint(r)
        ps = []
        for p, e in f.items():
            ps.extend([p] * e)
        if len(ps) == 2 and min(ps) >= Z:
            rows.append((r, sorted(set(ps))))
    return rows

def prime_mask(A, L):
    """Boolean array: True where A+i is PRIME (so climb columns exclude them)."""
    hi = A + L
    lim = int(hi ** 0.5) + 1
    base = np.ones(lim + 1, dtype=bool); base[:2] = False
    for i in range(2, int(lim ** 0.5) + 1):
        if base[i]:
            base[i * i::i] = False
    small = np.flatnonzero(base)
    isp = np.ones(L, dtype=bool)
    for p in small:
        start = (-A) % int(p)
        if A + start == p:
            start += p
        isp[start::p] = False
    isp &= (np.arange(A, hi) > 1)
    return isp

def gap_primes(r1, r2):
    ps = set()
    for m in range(r1, r2 + 1):
        ps |= set(factorint(m).keys())
    return ps

def climb_mask(A, L, r1, r2, isprime_arr):
    """Columns admitting a dockable composite climb from row r1 to row r2."""
    ok = np.ones(L, dtype=bool)
    for p in gap_primes(r1, r2):          # coprime to every swept height
        p = int(p)
        if p >= L + A:
            if A <= p < A + L:
                ok[p - A] = False
            continue
        ok[(-A) % p::p] = False
    ok &= ~isprime_arr                     # climb column must be composite
    for r in (r1, r2):                     # docking on both endpoint rows
        for p in factorint(r):
            p = int(p)
            for j in (-2, -1, 0, 1, 2):
                st = (-A - j) % p
                ok[st::p] = False
    return ok

def block_cols(A, L, primes):
    """Columns a with gcd(row, a(a+1)(a+2)) > 1."""
    m = np.zeros(L, dtype=bool)
    for p in primes:
        p = int(p)
        for j in (0, 1, 2):
            m[(-A - j) % p::p] = True
    return np.flatnonzero(m) + A

def run(H, E, Z, A, L, verbose=True):
    rows = build_rows(H, E, Z)
    K = len(rows)
    if K < 3:
        print(f"  Z={Z}: only {K} rows — skip"); return None
    isp = prime_mask(A, L)
    B = [block_cols(A, L, ps) for _, ps in rows]
    reach = B[0]
    depth = 1
    stats = []
    for i in range(K - 1):
        cm = climb_mask(A, L, rows[i][0], rows[i + 1][0], isp)
        climbs = np.flatnonzero(cm) + A
        if len(climbs) == 0:
            stats.append((rows[i + 1][0] - rows[i][0], 0, L))
            reach = B[i + 1]          # no climbs at all: interface free
            depth += 1
            continue
        maxgap = int(np.max(np.diff(climbs))) if len(climbs) > 1 else L
        # generous: allow c' anywhere in the closed climb-free interval [lo,hi]
        lo_idx = np.searchsorted(climbs, reach, side='left') - 1
        hi_idx = np.searchsorted(climbs, reach, side='right')
        lo = np.where(lo_idx >= 0, climbs[np.clip(lo_idx, 0, len(climbs) - 1)], A)
        hi = np.where(hi_idx < len(climbs), climbs[np.clip(hi_idx, 0, len(climbs) - 1)],
                      A + L - 1)
        nxt = B[i + 1]
        s = np.searchsorted(nxt, lo, side='left')
        e = np.searchsorted(nxt, hi, side='right')
        keep = np.zeros(len(nxt), dtype=bool)
        for a, b in zip(s[e > s], e[e > s]):
            keep[a:b] = True
        stats.append((rows[i + 1][0] - rows[i][0], len(climbs), maxgap))
        reach = nxt[keep]
        if len(reach) == 0:
            break
        depth += 1
    survived = depth == K
    if verbose:
        gaps = [s[0] for s in stats]; dens = [s[1] / L for s in stats]
        mx = [s[2] for s in stats]
        print(f"  Z={Z:5d}  rows K={K:3d}  blocks/row~{len(B[0]):6d}  "
              f"height-gaps {min(gaps)}-{max(gaps)}")
        print(f"          climb density {min(dens):.3f}-{max(dens):.3f}  "
              f"max climb-free gap {min(mx)}-{max(mx)}")
        print(f"          DP depth {depth}/{K}  survivors at stop: {len(reach)}  "
              f"STAIRCASE={'EXISTS -> ASE FALSE here' if survived else 'none'}")
    return dict(Z=Z, K=K, depth=depth, survived=survived)

if __name__ == '__main__':
    H = 10 ** 9
    A = 10 ** 7
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 2 * 10 ** 6
    print(f"reservoir height ~1e9, columns [{A}, {A+L}), L={L}")
    for Z in (300, 600, 1200, 2400):
        run(H, Z, Z, A, L)
