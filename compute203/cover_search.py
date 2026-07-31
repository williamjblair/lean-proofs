#!/usr/bin/env python3
"""Cover search on torus (Z/N)^2 for tiles u*k+v*l == c (mod n), one shift
c per prime. Greedy placement + single-prime re-optimization + restarts.
Success (0 uncovered) => covering system => CRT witness m for Erdos #203."""
import sys, json, math, time
import numpy as np
from sympy import n_order, primitive_root, discrete_log

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5040
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
rng = np.random.default_rng(seed)
fam = {int(p): n for p, n in json.load(open(f"harvest_N{N}.json")).items()}
# compute (u, v, n) per prime
tiles = []
for p, n in sorted(fam.items()):
    g0 = primitive_root(p)
    g = pow(g0, (p - 1) // n, p)
    u = discrete_log(p, 2, g); v = discrete_log(p, 3, g)
    tiles.append((p, u % n, v % n, n))
print(f"N={N}: {len(tiles)} tiles, density {sum(1.0/t[3] for t in tiles):.4f}")
K, L = np.meshgrid(np.arange(N, dtype=np.int64), np.arange(N, dtype=np.int64), indexing='ij')
def resid(u, v, n):
    return ((u * K + v * L) % n).astype(np.int32)
best_unc = N * N
for attempt in range(40):
    order = rng.permutation(len(tiles))
    # greedy with slight randomization: sort by n ascending + noise
    order = sorted(range(len(tiles)), key=lambda i: tiles[i][3] * (1 + 0.3*rng.random()))
    U = np.ones((N, N), dtype=bool)
    shifts = {}
    for i in order:
        p, u, v, n = tiles[i]
        R = resid(u, v, n)
        cnt = np.bincount(R[U], minlength=n)
        c = int(np.argmax(cnt))
        shifts[p] = c
        U &= (R != c)
        del R
    unc = int(U.sum())
    # local search sweeps
    for sweep in range(6):
        improved = False
        for i in range(len(tiles)):
            p, u, v, n = tiles[i]
            R = resid(u, v, n)
            # remove p's tile: recompute uncovered without it
            U2 = np.ones((N, N), dtype=bool)
            for j in range(len(tiles)):
                if j == i: continue
                pj, uj, vj, nj = tiles[j]
                Rj = resid(uj, vj, nj)
                U2 &= (Rj != shifts[pj])
                del Rj
            cnt = np.bincount(R[U2], minlength=n)
            c = int(np.argmax(cnt))
            newunc = int(U2.sum() - cnt[c])
            if newunc < unc:
                shifts[p] = c; unc = newunc; improved = True
            U = U2 & (R != shifts[p])
            del R, U2
            if unc == 0: break
        if unc == 0 or not improved: break
    if unc < best_unc:
        best_unc = unc
        json.dump({'N': N, 'uncovered': unc, 'shifts': {str(p): int(c) for p, c in shifts.items()}},
                  open(f'best_cover_N{N}.json', 'w'))
        print(f"attempt {attempt}: uncovered = {unc} ({100*unc/(N*N):.4f}%)  ** new best **", flush=True)
    if best_unc == 0:
        print("COVER FOUND"); break
print(f"FINAL best uncovered: {best_unc} of {N*N} ({100*best_unc/(N*N):.4f}%)")
