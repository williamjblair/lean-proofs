#!/usr/bin/env python3
"""Independent cover verification: given shifts {p: c}, check that every
(k,l) in random samples AND on full residue grids mod small lcms is covered:
some p with 2^k 3^l ≡ g^c (mod p)  i.e.  p | 2^k 3^l m + 1 for the CRT m.
This re-derives tile membership from raw modular arithmetic (no cell code)."""
import json, sys, math, random
from sympy import primitive_root, n_order

data = json.load(open(sys.argv[1]))
shifts = {int(p): c for p, c in data['shifts'].items()}
pool = {int(p): n for p, n in json.load(open('pool_merged.json')).items()}
targets = {}
for p, c in shifts.items():
    n = pool[p]
    g = pow(primitive_root(p), (p-1)//n, p)
    targets[p] = pow(g, c, p)          # tile: 2^k 3^l == t_p (mod p)
def covered(k, l):
    return any(pow(2, k, p) * pow(3, l, p) % p == t for p, t in targets.items())
rng = random.Random(203)
bad = 0
for _ in range(200000):
    k = rng.randrange(10**9); l = rng.randrange(10**9)
    if not covered(k, l): bad += 1
print(f"random sample 200k: {'ALL COVERED' if bad == 0 else f'{bad} UNCOVERED — NOT A COVER'}")
# exact check over the joint period: lcm of the n's used
L = 1
for p in shifts: L = math.lcm(L, pool[p])
print(f"joint period lcm = {L}")
if L <= 3000:
    allbad = sum(0 if covered(k, l) else 1 for k in range(L) for l in range(L))
    print(f"exact torus check {L}x{L}: {'PERFECT COVER' if allbad == 0 else f'{allbad} holes'}")
else:
    print("period too large for exact torus loop here; use per-prime-power CRT check next")
