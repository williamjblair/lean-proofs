#!/usr/bin/env python3
"""Fleet ship 2: deep point-forced backtracking RESTRICTED to the n|5040
family (31 tiles, density 1.0214 — knife-edge exact-cover regime)."""
import sys, json, math, time, random
TL = 28000
sys.argv = ['x', '5040']
import full_search as F
FAM = [i for i, t in enumerate(F.TILES) if 5040 % t[3] == 0]
print(f"5040-family: {len(FAM)} tiles, density {sum(1.0/F.TILES[i][3] for i in FAM):.4f}", flush=True)
from full_search import split, idx
TILES = F.TILES
def resid(cells): return sum(1.0/idx(c) for c in cells)
def place(cells, i, c):
    out = []
    p,u,v,n = TILES[i]
    for cell in cells:
        r = split(cell, u, v, n, c)
        if r is None: out.append(cell)
        else: out.extend(r)
    return out
best = [2.0]
t0 = time.time()
def rec(cells, avail, placed, depth, rng):
    if time.time() - t0 > TL: return None
    if not cells: return placed
    R = resid(cells)
    if R < best[0]:
        best[0] = R
        print(f"  d={depth} resid={R:.4e} cells={len(cells)}", flush=True)
    if R > sum(1.0/TILES[i][3] for i in avail) + 1e-15: return None
    cell = max(cells, key=lambda c: 1.0/idx(c))
    x = (cell[4], cell[5])
    opts = []
    big = sorted(cells, key=idx)[:60]
    for i in avail:
        c = (TILES[i][1]*x[0] + TILES[i][2]*x[1]) % TILES[i][3]
        est = 0.0
        for cl in big:
            r = split(cl, TILES[i][1], TILES[i][2], TILES[i][3], c)
            if r is None: continue
            est += 1.0/idx(cl) - sum(1.0/idx(ch) for ch in r)
        if est > 1e-18: opts.append((est + rng.random()*1e-12, i, c))
    opts.sort(reverse=True)
    for _, i, c in opts:              # FULL branching — exhaustive within time
        r = rec(place(cells, i, c), [j for j in avail if j != i],
                placed + [(i, c)], depth + 1, rng)
        if r is not None: return r
    return None
for s in range(3):
    print(f"--- 5040 seed {s} ---", flush=True)
    r = rec([(1,0,0,1,0,0)], FAM[:], [], 0, random.Random(s))
    if r:
        print("*** COVER FOUND (5040 family) ***", flush=True)
        json.dump({'shifts': {str(TILES[i][0]): int(c) for i, c in r}}, open('cover_5040.json','w'))
        break
