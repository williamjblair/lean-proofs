#!/usr/bin/env python3
"""Full-pool cell-based cover search for Erdos #203. LCM-agnostic.
Greedy-with-lookahead + restarts: maintain exact uncovered cells; at each
step pick (tile, shift) maximizing covered density, tie-break random;
tiles usable once. Restart with different seeds; report best residual."""
import json, math, sys, time, random
from sympy import primitive_root, discrete_log

pool = {int(p): n for p, n in json.load(open("pool_merged.json")).items()}
TILES = []
for p, n in sorted(pool.items(), key=lambda kv: kv[1]):
    g0 = primitive_root(p); g = pow(g0, (p-1)//n, p)
    u = discrete_log(p, 2, g) % n; v = discrete_log(p, 3, g) % n
    TILES.append((p, u, v, n))
#print(f"pool: {len(TILES)} tiles, density {sum(1/t[3] for t in TILES):.4f}", flush=True)

def egcd(a, b):
    if b == 0: return (a, 1, 0)
    g, x, y = egcd(b, a % b); return (g, y, x - (a//b)*y)

def split(cell, u, v, n, c):
    a11,a12,a21,a22,b1,b2 = cell
    g1 = (u*a11 + v*a21) % n; g2 = (u*a12 + v*a22) % n
    phib = (u*b1 + v*b2) % n
    g = math.gcd(math.gcd(g1, g2), n)
    if (c - phib) % math.gcd(g, n) != 0: return None  # tile misses cell
    d = n // g
    if d == 1: return []                              # tile swallows cell
    h1, h2 = (g1//g) % d, (g2//g) % d
    # find t0 with psi0(t0) == 1 mod d
    G, x, y = egcd(h1, d)
    t0 = None
    if G == 1: t0 = (x % d, 0)
    else:
        for yy in range(d):
            r = (1 - h2*yy) % d
            if r % G == 0:
                xx = ((r//G) * pow(h1//G, -1, d//G)) % (d//G) if d//G > 1 else 0
                if (h1*xx + h2*yy) % d == 1: t0 = (xx, yy); break
    if t0 is None: return None
    # kernel basis of psi0 mod d
    w1 = (h2 % d if h2 else d, (-h1) % d if h1 else 0)
    if (h1*w1[0] + h2*w1[1]) % d != 0 or w1 == (0,0): w1 = (h2, -h1)
    w2 = (d, 0) if (h1*d) % d == 0 else (0, d)
    det = w1[0]*w2[1] - w1[1]*w2[0]
    if det == 0:
        w1 = (0, d); w2 = (d, 0); det = -d*d
    # target slab j*: phib + j*g == c mod n
    jstar = ((c - phib) // g) % d if (c - phib) % g == 0 else None
    out = []
    for j in range(d):
        if j == jstar: continue
        nb1 = b1 + a11*(j*t0[0]) + a12*(j*t0[1])
        nb2 = b2 + a21*(j*t0[0]) + a22*(j*t0[1])
        na11 = a11*w1[0] + a12*w1[1]; na21 = a21*w1[0] + a22*w1[1]
        na12 = a11*w2[0] + a12*w2[1]; na22 = a21*w2[0] + a22*w2[1]
        out.append((na11,na12,na21,na22,nb1,nb2))
    return out

def idx(cell): return abs(cell[0]*cell[3] - cell[1]*cell[2])

def run(seed, tlimit):
    rng = random.Random(seed)
    cells = [(1,0,0,1,0,0)]
    avail = list(range(len(TILES)))
    placed = []
    t0 = time.time()
    while cells and avail and time.time()-t0 < tlimit:
        # score all (tile, best shift) by density removed; sample among top
        best = []
        for i in avail:
            p, u, v, n = TILES[i]
            # gain: for each cell, fraction g/n where g = gcd(form on cell, n),
            # need common c: greedy per-tile: pick c covering the biggest cell mass
            from collections import defaultdict
            gain = defaultdict(float)
            for cell in cells:
                a11,a12,a21,a22,b1,b2 = cell
                g1 = (u*a11 + v*a21) % n; g2 = (u*a12 + v*a22) % n
                phib = (u*b1 + v*b2) % n
                g = math.gcd(math.gcd(g1, g2), n)
                w = 1.0/idx(cell) * (g/n)
                for j in range(n // g):
                    gain[(phib + j*g) % n] += w  # covering c=that hits 1/(n/g) of cell
                # (approximation: each admissible c covers g/n of the cell)
            if gain:
                c, val = max(gain.items(), key=lambda kv: kv[1])
                best.append((val, i, c))
        if not best: break
        best.sort(reverse=True)
        pick = rng.choice(best[:max(1, min(4, len(best)))]) if rng.random() < 0.5 else best[0]
        _, i, c = pick
        p, u, v, n = TILES[i]
        newcells = []
        for cell in cells:
            r = split(cell, u, v, n, c)
            if r is None: newcells.append(cell)
            else: newcells.extend(r)
        cells = newcells
        avail.remove(i)
        placed.append((p, c))
    resid = sum(1.0/idx(c) for c in cells)
    return resid, len(cells), placed, cells

if __name__ == '__main__':
 best = (1.0, None)
 t00 = time.time()
 for s in range(int(sys.argv[1]) if len(sys.argv) > 1 else 20):
     resid, nc, placed, cells = run(s, 240)
     if resid < best[0]:
         best = (resid, placed)
         json.dump({'residual_density': resid, 'ncells': nc,
                    'shifts': {str(p): c for p, c in placed}}, open('best_full.json','w'))
     print(f"seed {s}: residual density {resid:.6f} in {nc} cells, {len(placed)} tiles used  [{time.time()-t00:.0f}s]", flush=True)
     if resid == 0:
         print("*** COVER FOUND ***"); break
 print(f"BEST residual: {best[0]:.6f}")
 