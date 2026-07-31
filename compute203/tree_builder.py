#!/usr/bin/env python3
"""Recursive parallel-direction tree builder for Erdos #203 (v1).
Moves at a cell:
  FAMILY(q, delta): q available tiles with q|n and common direction delta
    mod q, non-degenerate on the cell -> partition cell into q slabs; each
    tile takes one slab (c mod q forced); deeper shift parts chosen by fast
    scoring; recurse into each slab's leftover.
  SINGLE(i): fallback point-forced single placement (as before).
All on the validated lattice engine."""
import json, math, sys, time, random
from collections import defaultdict
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 1800
sys.argv = ['x', '5040']
from full_search import TILES, split, idx
def resid(cells): return sum(1.0/idx(c) for c in cells)

# direction tables mod each prime q | n
QS = [2, 3, 5, 7, 11, 13]
fam = defaultdict(list)          # (q, delta) -> [tile indices]; delta in P^1(F_q)
def dirclass(u, v, q):
    u, v = u % q, v % q
    if u == 0 and v == 0: return None
    if u % q and math.gcd(u, q) == 1:
        return (1, (v * pow(u, -1, q)) % q)
    return (0, 1) if u % q == 0 else (1, (v * pow(u, -1, q)) % q)
for i, (p, u, v, n) in enumerate(TILES):
    for q in QS:
        if n % q == 0:
            d = dirclass(u, v, q)
            if d: fam[(q, d)].append(i)
print("family sizes:", {k: len(v) for k, v in sorted(fam.items()) if len(v) >= k[0]}, flush=True)

def formcell(cell, u, v, n):
    """(g, phib): form restricted to cell = phib + g*Z mod n"""
    a11,a12,a21,a22,b1,b2 = cell
    g1 = (u*a11 + v*a21) % n; g2 = (u*a12 + v*a22) % n
    return math.gcd(math.gcd(g1, g2), n), (u*b1 + v*b2) % n

def place(cells, i, c):
    out = []
    p, u, v, n = TILES[i]
    for cell in cells:
        r = split(cell, u, v, n, c)
        if r is None: out.append(cell)
        else: out.extend(r)
    return out

def best_completion(cells_slab, i, cmodq, q, rng):
    """choose full shift c == cmodq (mod q) for tile i maximizing coverage
    of its slab cells (fast scoring on biggest cells)."""
    p, u, v, n = TILES[i]
    m = n // q
    big = sorted(cells_slab, key=idx)[:40]
    best = (-1.0, cmodq % n)
    # candidates: derive from big cells' phib values (CRT-consistent with cmodq)
    cands = set()
    for cell in big:
        g, phib = formcell(cell, u, v, n)
        for t in range(0, n, max(g, 1)):
            c = (phib + t) % n
            if c % q == cmodq % q: cands.add(c)
            if len(cands) > 24: break
        if len(cands) > 24: break
    if not cands:
        cands = {c for c in range(cmodq % q, n, q)}
    for c in list(cands)[:24]:
        gain = 0.0
        for cell in big:
            r = split(cell, u, v, n, c)
            if r is None: continue
            gain += 1.0/idx(cell) - sum(1.0/idx(ch) for ch in r)
        gv = gain + rng.random()*1e-12
        if gv > best[0]: best = (gv, c)
    return best[1]

def family_moves(cell, avail_set):
    """available FAMILY moves on this cell: (q, delta, tiles) with the form
    non-degenerate mod q on the cell and >= q tiles in family."""
    out = []
    for (q, d), lst in fam.items():
        tiles_av = [i for i in lst if i in avail_set]
        if len(tiles_av) < q: continue
        # non-degeneracy: direction form u0*k+v0*l mod q non-constant on cell
        u0, v0 = d
        g, _ = formcell(cell, u0, v0, q)
        if g % q == 0: continue      # degenerate (constant) on this cell
        out.append((q, d, tiles_av))
    return out

def cover(cells, avail, placed, depth, t0, rng, best):
    if time.time() - t0 > TL: return None
    if not cells: return placed
    R = resid(cells)
    if R < best[0]:
        best[0] = R
        print(f"  d={depth} resid={R:.4e} cells={len(cells)} avail={len(avail)}", flush=True)
    if R > sum(1.0/TILES[i][3] for i in avail): return None
    cell = max(cells, key=lambda c: 1.0/idx(c))     # biggest cell
    rest = [c for c in cells if c is not cell]
    moves = family_moves(cell, avail)
    # order: prefer small q, then largest surplus
    moves.sort(key=lambda m: (min(TILES[i][3] for i in m[2]), m[0], -len(m[2])))
    tried = 0
    for q, d, tiles_av in moves[:4]:
        # slab structure: partition cell by direction-form mod q
        u0, v0 = d
        # assign tiles to slabs: choose q tiles with the most surplus family
        team = sorted(tiles_av, key=lambda i: TILES[i][3])[:q]   # shallowest own slabs
        # compute the q slabs: split cell by (u0, v0, q, c') complements
        # slab_j = subcell with dirform == j; get them by splitting at each c
        state_cells = rest[:]
        newavail = [i for i in avail if i not in team]
        newplaced = placed[:]
        ok = True
        # each slab: covered by team[j] at completion chosen by scoring
        # build slab cells:
        slabs = []
        for j in range(q):
            r = split(cell, u0, v0, q, j)   # complement of slab j... we need slab j itself:
            # slab j = cell minus (complement pieces) — easier: slab j is the unique
            # child missing when splitting at c != j... Instead: slab_j = split-complement:
            pass
        # direct: slab_j = the subcell of `cell` where dirform == j:
        # split(cell, u0, v0, q, j) returns the OTHER q-1 slabs; so:
        allslabs = {}
        others = split(cell, u0, v0, q, 0)
        # others = slabs 1..q-1; slab 0 = cell minus others: recover slab j by splitting at each j
        for j in range(q):
            rr = split(cell, u0, v0, q, j)
            # slab_j = cell \ rr = the removed slab; represent it directly:
            # split returns complements; the covered slab is the missing child.
            # Get it: split at j' != j returns list incl. slab_j. Use j'=(j+1)%q:
            rr2 = split(cell, u0, v0, q, (j+1) % q)
            # find child with dirform == j:
            got = None
            for ch in rr2:
                g_, ph_ = formcell(ch, u0, v0, q)
                if ph_ % q == j and g_ % q == 0: got = ch; break
            if got is None: ok = False; break
            allslabs[j] = got
        if not ok: continue
        for j in range(q):
            i = team[j]
            cmodq = None
            # tile i's own form mod q must select slab j: c_i mod q such that
            # {phi_i == c_i} cap cell subset slab_j: phi_i and dirform are parallel
            # mod q: phi_i == alpha*dirform (mod q) for some unit alpha:
            p_, u_, v_, n_ = TILES[i]
            # find alpha: u_ = alpha*u0, v_ = alpha*v0 mod q
            alpha = None
            for a in range(1, q):
                if (u_ - a*u0) % q == 0 and (v_ - a*v0) % q == 0: alpha = a; break
            if alpha is None: ok = False; break
            cmodq = (alpha * j) % q
            c = best_completion([allslabs[j]], i, cmodq, q, rng)
            # leftover of slab j after tile i:
            r = split(allslabs[j], p_ and u_ or u_, v_, n_, c)
            if r is None: state_cells.append(allslabs[j])
            else: state_cells.extend(r)
            newplaced.append((i, c))
        if not ok: continue
        res = cover(state_cells, newavail, newplaced, depth+1, t0, rng, best)
        if res is not None: return res
        tried += 1
        if tried >= 2: break
    # fallback: single point-forced placement
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
    for _, i, c in opts[:4]:
        nc = place(cells, i, c)
        res = cover(nc, [j for j in avail if j != i], placed + [(i, c)], depth+1, t0, rng, best)
        if res is not None: return res
    return None

if __name__ == '__main__':
    for s in range(4):
        print(f"--- seed {s} ---", flush=True)
        rng = random.Random(s)
        r = cover([(1,0,0,1,0,0)], list(range(len(TILES))), [], 0, time.time(), rng, [2.0])
        if r:
            print("*** COVER FOUND ***", flush=True)
            json.dump({'shifts': {str(TILES[i][0]): int(c) for i, c in r}}, open('tree_cover.json','w'))
            break
