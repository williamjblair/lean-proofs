#!/usr/bin/env python3
"""For each stall cell (A, b): a new tile (u,v,n) swallows it iff
u*A1 + v*A2 == 0 (mod n) componentwise. Solutions exist for n | d2 (larger
SNF elementary divisor of A). Compute d2 per cell + the dual class
(u0 : v0) mod n. Aggregate: which (n, class) values would kill the most
residual mass? Then check the EXISTING pool's classes for near-misses."""
import json, math
from collections import defaultdict

D = json.load(open('stall_cells.json'))
cells = D['cells']
def idx(c): return abs(c[0]*c[3]-c[1]*c[2])

# SNF d2 of 2x2 integer matrix: d1 = gcd of entries, d2 = det/d1
agg = defaultdict(float)   # (d2 truncated structure) -> mass
raw = defaultdict(float)
for c in cells:
    a11,a12,a21,a22,b1,b2 = c
    det = abs(a11*a22 - a12*a21)
    d1 = math.gcd(math.gcd(a11,a12), math.gcd(a21,a22))
    d2 = det // d1
    raw[(d1, d2)] += 1.0/det
mass = sorted(raw.items(), key=lambda kv: -kv[1])
tot = sum(raw.values())
print(f"{len(cells)} cells, residual {tot:.6f}; SNF (d1, d2) classes by mass:")
for (d1, d2), m in mass[:12]:
    print(f"  d1={d1:<8} d2={d2:<14} mass={m:.2e} ({100*m/tot:.1f}%)  d2 factors: ", end='')
    n = d2; fs = {}
    d = 2
    while d*d <= n and d < 10**6:
        while n % d == 0: fs[d] = fs.get(d,0)+1; n //= d
        d += 1
    if n > 1: fs[n] = fs.get(n,0)+1
    print(fs)
# what n could swallow: any n | d2 with n>1. Existing pool n-values for comparison:
pool = {int(p): n for p, n in json.load(open('pool_merged.json')).items()}
pooln = sorted(set(pool.values()))
print("\npool n-values:", pooln[:40], "...")
# for the top class: which pool-n divide d2?
(d1, d2), m = mass[0]
compat = [n for n in pooln if d2 % n == 0]
print(f"top class d2={d2}: pool n dividing d2: {compat}")
