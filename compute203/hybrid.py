#!/usr/bin/env python3
"""Hybrid solver: P1 bulk greedy (proven: resid ~1e-3 with ~13 tiles) then
point-forced backtracking endgame on the remaining cells with full pool."""
import json, math, sys, time, random
LIMIT = float(sys.argv[1]) if len(sys.argv) > 1 else 1800
sys.argv = ['cell_search.py', '5040']
from full_search import TILES, split, idx
from full_search2 import phase1
import full_search2
full_search2.RESERVED = None   # no reservation; endgame has real backtracking

def resid(cells): return sum(1.0/idx(c) for c in cells)
def phi(t, x): return (t[1]*x[0] + t[2]*x[1]) % t[3]
def place(cells, i, c):
    out = []
    p, u, v, n = TILES[i]
    for cell in cells:
        r = split(cell, u, v, n, c)
        if r is None: out.append(cell)
        else: out.extend(r)
    return out

def endgame(cells, avail, placed, tlimit, seed):
    rng = random.Random(seed)
    t0 = time.time(); best = [resid(cells)]
    def rec(cells, avail, placed, depth):
        if time.time() - t0 > tlimit: return None
        if not cells: return placed
        R = resid(cells)
        if R < best[0]*0.98:
            best[0] = R
            print(f"  end d={depth} resid={R:.3e} cells={len(cells)}", flush=True)
        if R > sum(1.0/TILES[i][3] for i in avail): return None
        cells_s = sorted(cells, key=idx, reverse=True)
        x = (cells_s[0][4], cells_s[0][5])
        big = cells_s[:80]
        opts = []
        for i in avail:
            c = phi(TILES[i], x)
            est = 0.0
            for cell in big:
                r = split(cell, TILES[i][1], TILES[i][2], TILES[i][3], c)
                if r is None: continue
                est += 1.0/idx(cell) - sum(1.0/idx(ch) for ch in r)
            if est > 1e-18: opts.append((est + rng.random()*1e-12, i, c))
        opts.sort(reverse=True)
        for _, i, c in opts[:6]:
            nc = place(cells, i, c)
            r = rec(nc, [j for j in avail if j != i], placed + [(i, c)], depth+1)
            if r is not None: return r
        return None
    return rec(cells, sorted(avail), placed, 0)

if __name__ == '__main__':
    for s in range(6):
        cells, avail, placed = phase1(s, 240)
        print(f"seed {s}: P1 resid {resid(cells):.5f} cells {len(cells)} tiles {len(placed)}", flush=True)
        r = endgame(cells, avail, placed, LIMIT/3, s)
        if r is not None:
            print("*** COVER FOUND ***", flush=True)
            json.dump({'shifts': {str(TILES[i][0]): int(c) for i, c in r}},
                      open('hybrid_cover.json','w'))
            sys.exit(0)
        print(f"seed {s}: endgame exhausted/timeout", flush=True)
