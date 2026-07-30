"""Verify, from the RAW definition of G, that the hub graph H built by hub.py
is exactly the right reduction, on a box.

Checks:
  (0) admissible vertices with both coords even do not exist (gcd rules it out)
  (1) every admissible vertex is either a hub (both coords odd, >=3) or a
      "link" (exactly one even coord); links with even coord >= 4 have exactly
      the two hub neighbours obtained by +-1 on the even coord; links with even
      coord == 2 have at most one admissible neighbour (dead end, useless)
  (2) hub-hub connectivity through a link matches hub.py's Hm / Vm exactly
  (3) global: components of the raw admissible graph restricted to hubs in an
      interior sub-box agree with components of H on the box
"""
from math import gcd
import sys
import numpy as np
from hub import prime_mask, Builder

N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
pr = prime_mask(N + 4)


def comp(n):
    return n >= 4 and not pr[n]


adm = set()
for x in range(2, N + 1):
    for y in range(2, N + 1):
        if gcd(x, y) == 1 and (comp(x) or comp(y)):
            adm.add((x, y))

# (0)/(1)
bad = 0
hubs = set()
links = []
for (x, y) in adm:
    if x % 2 == 0 and y % 2 == 0:
        bad += 1
    elif x % 2 and y % 2:
        if x < 3 or y < 3:
            bad += 1
        hubs.add((x, y))
    else:
        links.append((x, y))
print(f"admissible={len(adm)} hubs={len(hubs)} links={len(links)} bad={bad}")

link_pairs = set()
deadend2 = 0
for (x, y) in links:
    nb = [(u, v) for (u, v) in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1))
          if (u, v) in adm]
    e = x if x % 2 == 0 else y
    if e == 2:
        if len(nb) > 1:
            deadend2 += 1
    else:
        assert all(u % 2 and v % 2 for (u, v) in nb), (x, y, nb)
        if len(nb) == 2:
            link_pairs.add(tuple(sorted(nb)))
print(f"links with even coord 2 having >1 admissible nbr: {deadend2}")
print(f"hub-hub pairs joined by a link: {len(link_pairs)}")

# (2) compare to hub.py
B = Builder(N, prime_mask(max(N, 8) + 4))
aa, V, Hm, Vm = B.build(1, (N - 1) // 2 + 1)
mine = set()
for j in range(B.nb):
    b = int(B.bb[j])
    for i in range(len(aa)):
        a = int(aa[i])
        if Hm[j, i] and a + 2 <= N:
            mine.add(tuple(sorted([(a, b), (a + 2, b)])))
        if j + 1 < B.nb and Vm[j, i] and b + 2 <= N:
            mine.add(tuple(sorted([(a, b), (a, b + 2)])))
# restrict raw pairs to those inside the box
lp = {p for p in link_pairs if max(max(p[0]), max(p[1])) <= N}
mn = {p for p in mine if max(max(p[0]), max(p[1])) <= N}
print(f"edge sets equal: {lp == mn}  |raw|={len(lp)} |hub.py|={len(mn)}")
if lp != mn:
    print("  raw-only:", list(lp - mn)[:8])
    print("  hub-only:", list(mn - lp)[:8])

# (3) component agreement on an interior sub-box
par = {}


def find(u):
    while par[u] != u:
        par[u] = par[par[u]]
        u = par[u]
    return u


def uni(u, v):
    ru, rv = find(u), find(v)
    if ru != rv:
        par[ru] = rv


for v in adm:
    par[v] = v
for (x, y) in adm:
    for (u, v) in ((x + 1, y), (x, y + 1)):
        if (u, v) in adm:
            uni((x, y), (u, v))

par2 = {}
for e in mn:
    for v in e:
        par2.setdefault(v, v)
par, par2 = par2, par
for e in mn:
    uni(e[0], e[1])
par, par2 = par2, par

M = N // 2
sub = sorted(h for h in hubs if max(h) <= M)
ok = True
for i in range(len(sub)):
    for k in range(i + 1, len(sub)):
        u, v = sub[i], sub[k]
        same_raw = find(u) == find(v)
        pu = par2.get(u, u)
        while par2.get(pu, pu) != pu:
            pu = par2[pu]
        pv = par2.get(v, v)
        while par2.get(pv, pv) != pv:
            pv = par2[pv]
        if same_raw != (pu == pv):
            ok = False
            print("MISMATCH", u, v, same_raw)
            break
    if not ok:
        break
print(f"component agreement on hubs with max coord <= {M}: {ok}")
