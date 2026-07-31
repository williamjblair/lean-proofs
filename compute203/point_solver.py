#!/usr/bin/env python3
"""Point-forced backtracking cover solver for Erdos #203.
Branch: pick an uncovered point x (from the smallest = hardest cell);
each available tile covers x at the FORCED shift c = phi_p(x); try tiles
in order of (coverage gain, scarcity); propagate cells; prune when
residual > remaining supply. Restarts with randomized tie-breaks."""
import json, math, sys, time, random
sys.argv = ['cell_search.py', '5040']
from full_search import TILES, split, idx

DENS = [1.0/t[3] for t in TILES]
def phi(t, x):
    p, u, v, n = t
    return (u*x[0] + v*x[1]) % n

def cell_point(cell):
    # b is a point of the cell
    return (cell[4], cell[5])

def place(cells, i, c):
    out = []
    p, u, v, n = TILES[i]
    for cell in cells:
        r = split(cell, u, v, n, c)
        if r is None: out.append(cell)
        else: out.extend(r)
    return out

def resid(cells): return sum(1.0/idx(c) for c in cells)

def solve(seed, tlimit):
    rng = random.Random(seed)
    t0 = time.time()
    best = [1.0]
    sys.setrecursionlimit(10000)
    def rec(cells, avail, placed, depth):
        if time.time() - t0 > tlimit: return None
        if not cells: return placed
        R = resid(cells)
        if R < best[0]:
            best[0] = R
            if R < 3e-4 or depth < 25:
                print(f"  d={depth} resid={R:.2e} cells={len(cells)} tiles_left={len(avail)}", flush=True)
        if R > sum(DENS[i] for i in avail): return None       # supply prune
        # class prune: cells needing q^a beyond remaining supply
        # (cheap version: skip)
        cells_s = sorted(cells, key=idx, reverse=True)         # hardest = biggest idx? 
        x = cell_point(cells_s[0])                             # point of deepest cell
        # cheap scoring on the dominant cells only
        big = cells_s[:60]
        opts = []
        for i in avail:
            c = phi(TILES[i], x)
            est = 0.0
            for cell in big:
                p_, u_, v_, n_ = TILES[i]
                r = split(cell, u_, v_, n_, c)
                if r is None: continue
                est += 1.0/idx(cell) - sum(1.0/idx(ch) for ch in r)
            if est <= 1e-18: continue
            opts.append((est + rng.random()*1e-9, i, c))
        opts.sort(reverse=True)
        for _, i, c in opts[:8]:
            nc = place(cells, i, c)
            r = rec(nc, [j for j in avail if j != i], placed + [(i, c)], depth + 1)
            if r is not None: return r
        return None
    return rec([(1,0,0,1,0,0)], list(range(len(TILES))), [], 0)

if __name__ == '__main__':
    tl = float(sys.argv[1]) if len(sys.argv) > 1 else 1200
    for s in range(4):
        print(f"--- seed {s} ---", flush=True)
        r = solve(s, tl)
        if r:
            print("*** COVER FOUND ***")
            json.dump({'shifts': {str(TILES[i][0]): int(c) for i, c in r}},
                      open('point_cover.json', 'w'))
            break
