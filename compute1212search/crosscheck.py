"""Independent BFS in G itself (no reduction), compared with H components."""
from math import gcd
from collections import deque
from sympy import isprime
import numpy as np
from h1212 import components

N = 260


def adm(x, y):
    return (x > 1 and y > 1 and gcd(x, y) == 1
            and not (isprime(x) and isprime(y)))


nodes = {(x, y) for x in range(2, N + 1) for y in range(2, N + 1) if adm(x, y)}


def comp_of(s):
    seen = {s}
    q = deque([s])
    while q:
        x, y = q.popleft()
        for nx, ny in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if (nx, ny) in nodes and (nx, ny) not in seen:
                seen.add((nx, ny))
                q.append((nx, ny))
    return seen


# largest components of G in the box, and how far right they get
seen_all = set()
best = []
for s in sorted(nodes):
    if s in seen_all:
        continue
    c = comp_of(s)
    seen_all |= c
    best.append((len(c), min(x for x, y in c), max(x for x, y in c),
                 min(y for x, y in c), max(y for x, y in c)))
best.sort(reverse=True)
print(f"G box 2..{N}: {len(best)} components; top 8 by size")
print(f"{'size':>7} {'xmin':>5} {'xmax':>6} {'ymin':>5} {'ymax':>6}")
for t in best[:8]:
    print(f"{t[0]:>7} {t[1]:>5} {t[2]:>6} {t[3]:>5} {t[4]:>6}")

# compare with H
lab, ncomp, V, aa, bb = components(N, N)
hsizes = {}
for j in range(V.shape[0]):
    for i in range(V.shape[1]):
        if V[j, i]:
            hsizes.setdefault(lab[j, i], []).append((aa[i], bb[j]))
hbest = sorted((len(v), min(a for a, b in v), max(a for a, b in v),
                min(b for a, b in v), max(b for a, b in v))
               for v in hsizes.values())[::-1]
print(f"\nH box 3..{N}: {len(hbest)} components; top 8 by size")
for t in hbest[:8]:
    print(f"{t[0]:>7} {t[1]:>5} {t[2]:>6} {t[3]:>5} {t[4]:>6}")

# consistency: two hubs in the same H component must be in the same G component
gmap = {}
for k, s in enumerate(sorted(nodes)):
    pass
gcomp = {}
seen_all = set()
k = 0
for s in sorted(nodes):
    if s in seen_all:
        continue
    c = comp_of(s)
    seen_all |= c
    for v in c:
        gcomp[v] = k
    k += 1
bad = 0
for cid, verts in hsizes.items():
    gs = {gcomp[(a, b)] for a, b in verts}
    if len(gs) != 1:
        bad += 1
print("\nH components that split in G (should be 0):", bad)
# and: G components restricted to hubs, do they merge H components?
merge = 0
inv = {}
for cid, verts in hsizes.items():
    for a, b in verts:
        inv[(a, b)] = cid
byg = {}
for (a, b), cid in inv.items():
    byg.setdefault(gcomp[(a, b)], set()).add(cid)
merge = sum(1 for v in byg.values() if len(v) > 1)
print("G components merging >1 H component (nonzero only from x=2/y=2 border):",
      merge)
