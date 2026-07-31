#!/usr/bin/env python3
"""DFS driver over cell_search.split: cover Z^2 with one shift per tile.
Heuristic: always attack the LARGEST uncovered cell; among unused tiles,
try those whose form is 'constant-capable' on that cell (max coverage),
ordered by fraction covered; branch over best few (tile, shift) options."""
import json, sys, math, time
LIMIT_ARG = float(sys.argv[1]) if len(sys.argv) > 1 else 600
sys.argv = ['cell_search.py', '5040']
from cell_search import split, cell_index, tiles, N

t0 = time.time()
LIMIT = LIMIT_ARG
best = [float('inf'), None]
TILES = tiles  # (p, u, v, n) sorted by n asc

def density(cells): return sum(1.0/cell_index(c) for c in cells)

def options(cell, avail):
    """for a cell, rank (tile_idx, c, frac_covered) choices."""
    a11,a12,a21,a22,b1,b2 = cell
    out = []
    for i in avail:
        p, u, v, n = TILES[i]
        g1 = (u*a11 + v*a21) % n; g2 = (u*a12 + v*a22) % n
        g = math.gcd(math.gcd(g1, g2), n)
        phib = (u*b1 + v*b2) % n
        # tile covers fraction g/n of the cell, at d = n/g admissible shifts
        # constant on cell iff g == n (covers ALL of cell at c = phib)
        out.append((g/n, i, phib, g))
    out.sort(reverse=True)
    return out

def dfs(cells, avail, depth):
    if time.time() - t0 > LIMIT: return False
    if not cells:
        best[0] = 0; best[1] = 'FOUND'; return True
    d = density(cells)
    if d > sum(1.0/TILES[i][3] for i in avail) + 1e-12:  # remaining capacity < need
        return False
    # attack largest cell (smallest index)
    cells = sorted(cells, key=cell_index)
    cell = cells[0]
    rest = cells[1:]
    opts = options(cell, avail)
    tried = 0
    for frac, i, phib, g in opts[:6]:
        if frac == 0: break
        p, u, v, n = TILES[i]
        # best shift for THIS cell: any c == phib + j*g hitting it; c = phib covers
        # the j=0 slab; all admissible c cover equal fractions — try c=phib first,
        # plus a couple of alternatives for diversity
        for c in ([phib] if g < n else [phib]):
            newcells = split(cell, u, v, n, c)
            # also apply this tile to the OTHER cells (it's placed globally!)
            for oc in rest:
                newcells.extend(split(oc, u, v, n, c))
            newavail = [j for j in avail if j != i]
            if dfs(newcells, newavail, depth+1): 
                sol.append((p, u, v, n, c)); return True
            tried += 1
            if tried >= 8: return False
    return False

sol = []
cells0 = [(1,0,0,1,0,0)]
ok = dfs(cells0, list(range(len(TILES))), 0)
print(f"N={N} result: {'COVER FOUND' if ok else 'no cover found in time limit'}  ({time.time()-t0:.0f}s)")
if ok:
    json.dump({'N': N, 'uncovered': 0,
               'shifts': {str(p): int(c) for p, u, v, n, c in sol}},
              open(f'cell_cover_N{N}.json', 'w'))
    print("shifts saved to", f'cell_cover_N{N}.json')
