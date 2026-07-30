"""Extract an explicit path in the giant component, lift it to G, verify it
from the raw definition, and write the trajectory."""
import sys
from math import gcd
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import dijkstra
from strip import build
from h1212 import prime_mask

A = int(sys.argv[1]) if len(sys.argv) > 1 else 64001
B = int(sys.argv[2]) if len(sys.argv) > 2 else 1400
OUT = sys.argv[3] if len(sys.argv) > 3 else f"trajectory_{A}_{B}.txt"

V, Hm, Vm, aa, bb, na, nb = build(A, B)
vid = np.cumsum(V.ravel(), dtype=np.int32) - 1
nv = int(vid[-1]) + 1
fh = np.flatnonzero(Hm.ravel()); fv = np.flatnonzero(Vm.ravel())
src = np.concatenate([vid[fh], vid[fv]])
dst = np.concatenate([vid[fh + 1], vid[fv + na]])
g = coo_matrix((np.ones(src.size), (src, dst)), shape=(nv, nv)).tocsr()
g = g + g.T

flatV = np.flatnonzero(V.ravel())          # vid k  ->  flat cell flatV[k]


def cell(k):
    f = int(flatV[k]); return int(aa[f % na]), int(bb[f // na])


# source: leftmost vertex of the component that reaches the last column
from scipy.sparse.csgraph import connected_components as scc
ncomp, lab = scc(g, directed=False)
last_col = vid[np.flatnonzero(V[:, -1].astype(bool)) * na + (na - 1)]
target_comps = np.unique(lab[last_col])
mask = np.isin(lab, target_comps)
cols_of = flatV % na
kmin = int(np.flatnonzero(mask)[np.argmin(cols_of[mask])])
s = kmin
print(f"strip a<={A}, b<={B}; giant reaches last column; source = {cell(s)}")

d, pred = dijkstra(g, indices=s, return_predecessors=True, unweighted=True)
cand = last_col[np.isfinite(d[last_col])]
t = int(cand[np.argmin(d[cand])])
print(f"target = {cell(t)}, hops in H = {int(d[t])}")

seq = []
u = t
while u != s:
    seq.append(u); u = pred[u]
seq.append(s); seq.reverse()
hpath = [cell(k) for k in seq]

# lift H -> G by inserting the subdivision vertex
gpath = [hpath[0]]
for (x1, y1), (x2, y2) in zip(hpath, hpath[1:]):
    gpath.append(((x1 + x2) // 2, (y1 + y2) // 2))
    gpath.append((x2, y2))

# ---- independent verification straight from the definition
pr = prime_mask(max(max(x for x, y in gpath), max(y for x, y in gpath)) + 2)


def composite(n):
    return n >= 4 and not pr[n]


bad = []
for i, (x, y) in enumerate(gpath):
    if gcd(x, y) != 1:
        bad.append((i, x, y, "gcd"))
    if min(x, y) <= 1:
        bad.append((i, x, y, "min"))
    if not (composite(x) or composite(y)):
        bad.append((i, x, y, "composite"))
for (x1, y1), (x2, y2) in zip(gpath, gpath[1:]):
    if abs(x1 - x2) + abs(y1 - y2) != 1:
        bad.append(((x1, y1), (x2, y2), "step"))
print(f"G-path length = {len(gpath)} vertices; violations = {len(bad)}")
if bad:
    print(bad[:10]); sys.exit(1)
xs = [x for x, y in gpath]; ys = [y for x, y in gpath]
print(f"x range {min(xs)}..{max(xs)}   y range {min(ys)}..{max(ys)}")

with open(OUT, "w") as f:
    f.write(f"# Erdos 1212 witness path in G, verified from the definition\n")
    f.write(f"# {len(gpath)} vertices, x in [{min(xs)},{max(xs)}], "
            f"y in [{min(ys)},{max(ys)}]\n")
    for x, y in gpath:
        f.write(f"{x} {y}\n")
print("wrote", OUT)
np.save(OUT.replace('.txt', '_hub.npy'), np.array(hpath))
