#!/usr/bin/env python3
"""Two-phase #203 cover search.
P1: greedy bulk (as before) until cells > CAP or no big gains.
P2: closure by constancy-matching: for leftover cells, a tile swallows a
cell iff its form is constant on it (g==n) with value phib; each tile has
ONE c, so group cells by (tile, phib); greedy set-cover over these groups;
recurse on conflicts. Non-constant tiles can also SPLIT big leftovers."""
import json, math, sys, time, random
from collections import defaultdict
from sympy import primitive_root, discrete_log
from full_search import TILES, split, idx   # reuse engine

def phase1(seed, tlimit, capcells=3000):
    rng = random.Random(seed)
    cells = [(1,0,0,1,0,0)]
    avail = set(range(len(TILES)))
    placed = []
    t0 = time.time()
    while cells and avail and time.time()-t0 < tlimit and len(cells) < capcells:
        big = sorted(cells, key=idx)[:400]   # score only the biggest cells
        best = None
        for i in avail:
            p, u, v, n = TILES[i]
            info = []
            for cell in big:
                a11,a12,a21,a22,b1,b2 = cell
                g1=(u*a11+v*a21)%n; g2=(u*a12+v*a22)%n; phib=(u*b1+v*b2)%n
                g = math.gcd(math.gcd(g1,g2),n)
                info.append((phib, g, (g/n)/idx(cell)))
            cands = {ph % n for ph, g, w in info[:40]}
            for c in cands:
                val = sum(w for ph, g, w in info if (c - ph) % g == 0)
                if best is None or val > best[0]: best = (val, i, c)
        if best is None or best[0] < 1e-12: break
        _, i, c = best
        p, u, v, n = TILES[i]
        nc = []
        for cell in cells:
            r = split(cell, u, v, n, c)
            nc.append(cell) if r is None else nc.extend(r)
        cells = nc; avail.discard(i); placed.append((i, c))
        print(f'  P1 step {len(placed)}: {len(cells)} cells, resid {sum(1.0/idx(x) for x in cells):.5f}', flush=True)
        if len(cells) > 60000: break
    return cells, avail, placed

def phase2(cells, avail, placed, rounds=400):
    """closure: swallow leftover cells via constant tiles; split stubborn ones."""
    for rnd in range(rounds):
        if rnd % 10 == 0:
            json.dump({'shifts': {str(TILES[i][0]): int(c) for i, c in placed}}, open('ckpt.json','w'))
        if rnd % 10 == 0: print(f'  P2 round {rnd}: {len(cells)} cells, resid {sum(1.0/idx(x) for x in cells):.7f}', flush=True)
        if not cells: return cells, placed
        # group: (tile i, c) -> set of cell indices it swallows
        groups = defaultdict(list)
        splitters = defaultdict(float)
        for ci, cell in enumerate(cells):
            a11,a12,a21,a22,b1,b2 = cell
            for i in avail:
                p,u,v,n = TILES[i]
                g1=(u*a11+v*a21)%n; g2=(u*a12+v*a22)%n
                g = math.gcd(math.gcd(g1,g2),n)
                phib=(u*b1+v*b2)%n
                if g % n == 0:
                    groups[(i, phib)].append(ci)
                else:
                    splitters[(i, phib, ci)] = (g/n)/idx(cell)
        if groups:
            (i, c), members = max(groups.items(), key=lambda kv: sum(1.0/idx(cells[ci]) for ci in kv[1]))
            keep = [cell for ci, cell in enumerate(cells) if ci not in set(members)]
            if sum(1.0/idx(x) for x in keep) > 3e-4:
                nc = []
                p,u,v,n = TILES[i]
                for cell in keep:
                    r = split(cell, u, v, n, c)
                    nc.append(cell) if r is None else nc.extend(r)
                cells = nc
            else:
                cells = keep   # endgame: conservative accounting, no growth
            avail.discard(i); placed.append((i, c))
        elif splitters and sum(1.0/idx(c) for c in cells) > 3e-4:
            (i, c, ci), _ = max(splitters.items(), key=lambda kv: kv[1])
            p,u,v,n = TILES[i]
            nc = []
            for cell in cells:
                r = split(cell, u, v, n, c)
                nc.append(cell) if r is None else nc.extend(r)
            cells = nc; avail.discard(i); placed.append((i, c))
        else:
            import collections
            need = collections.Counter()
            for cell in cells[:200]: need[idx(cell)] += 1
            print(f'  P2 STALL: {len(cells)} cells, resid {sum(1.0/idx(c) for c in cells):.2e}; top cell indices: {need.most_common(8)}', flush=True)
            return cells, placed
    return cells, placed

if __name__ == '__main__':
    nseeds = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    best = (1.0, None)
    for s in range(nseeds):
        t0 = time.time()
        cells, avail, placed = phase1(s, 200)
        r1 = sum(1.0/idx(c) for c in cells)
        cells, placed = phase2(cells, avail, placed)
        resid = sum(1.0/idx(c) for c in cells)
        print(f"seed {s}: P1 residual {r1:.6f} -> P2 residual {resid:.8f} "
              f"({len(cells)} cells, {len(placed)} tiles, {time.time()-t0:.0f}s)", flush=True)
        if resid < best[0]:
            best = (resid, placed)
            json.dump({'residual': resid,
                       'shifts': {str(TILES[i][0]): int(c) for i, c in placed}},
                      open('best_full2.json', 'w'))
        if resid == 0:
            print("*** COVER FOUND — extracting witness ***", flush=True); break
    print("BEST:", best[0])
