"""Extract an explicit path in H inside a box and describe the moves used."""
import sys
import numpy as np
from scipy.sparse import coo_matrix, csr_matrix
from scipy.sparse.csgraph import breadth_first_order, dijkstra
from h1212 import hub_matrix, edges
from sympy import factorint

N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000

V, aa, bb = hub_matrix(N, N)
Hm, Vm = edges(N, N, V, aa, bb)
nb, na = V.shape
idx = np.arange(nb * na, dtype=np.int32).reshape(nb, na)
s1, d1 = [], []
jj, ii = np.nonzero(Hm); s1.append(idx[jj, ii]); d1.append(idx[jj, ii + 1])
jj, ii = np.nonzero(Vm); s1.append(idx[jj, ii]); d1.append(idx[jj + 1, ii])
src = np.concatenate(s1); dst = np.concatenate(d1)
g = coo_matrix((np.ones(src.size), (src, dst)), shape=(nb * na, nb * na))
g = (g + g.T).tocsr()

from scipy.sparse.csgraph import connected_components as scc
ncomp, lab = scc(g, directed=False)
lab2 = np.where(V, lab.reshape(nb, na), -1)

Amat = np.broadcast_to(aa[None, :], V.shape)
Bmat = np.broadcast_to(bb[:, None], V.shape)
S = Amat + Bmat
# giant = component with the largest span in a+b
best, bestc = -1, None
for c in np.unique(lab2[V]):
    m = lab2 == c
    sp = S[m].max() - S[m].min()
    if sp > best:
        best, bestc = sp, c
m = lab2 == bestc
print(f"N={N}  giant component: size={m.sum()}  a+b in "
      f"[{S[m].min()},{S[m].max()}]  a in [{Amat[m].min()},{Amat[m].max()}]"
      f"  b in [{Bmat[m].min()},{Bmat[m].max()}]")

# lowest and highest vertices of the giant, by a+b
lo = np.argwhere(m & (S == S[m].min()))[0]
hi = np.argwhere(m & (S == S[m].max()))[0]
src_i = int(idx[lo[0], lo[1]]); dst_i = int(idx[hi[0], hi[1]])
print("lowest vertex :", (int(Amat[lo[0], lo[1]]), int(Bmat[lo[0], lo[1]])))
print("highest vertex:", (int(Amat[hi[0], hi[1]]), int(Bmat[hi[0], hi[1]])))

dist, pred = dijkstra(g, indices=src_i, return_predecessors=True, unweighted=True)
path = []
u = dst_i
while u != -9999 and u != src_i:
    path.append(u); u = pred[u]
path.append(src_i); path.reverse()
print("path length (hops):", len(path) - 1)

pts = [(int(aa[u % na]), int(bb[u // na])) for u in path]
np.save(f"path_{N}.npy", np.array(pts))

# summarise the moves: runs along a row / runs along a column
runs = []
cur = [pts[0]]
def kind(p, q): return 'H' if p[1] == q[1] else 'V'
k = kind(pts[0], pts[1])
for p, q in zip(pts, pts[1:]):
    if kind(p, q) != k:
        runs.append((k, cur[0], cur[-1]))
        cur = [p]; k = kind(p, q)
    cur.append(q)
runs.append((k, cur[0], cur[-1]))
print(f"\n{len(runs)} maximal straight runs. First 40:")
print(f"{'dir':>3} {'from':>16} {'to':>16} {'hops':>5}  line value & its factorisation")
for kk, p, q in runs[:40]:
    line = p[1] if kk == 'H' else p[0]
    hops = (abs(q[0]-p[0]) + abs(q[1]-p[1])) // 2
    print(f"{kk:>3} {str(p):>16} {str(q):>16} {hops:>5}  {line} = {factorint(line)}")

# how long are the runs, and what are the line values?
import collections
lens = collections.Counter(((abs(q[0]-p[0]) + abs(q[1]-p[1])) // 2) for kk, p, q in runs)
print("\nrun-length histogram:", dict(sorted(lens.items())))
lines = [(p[1] if kk == 'H' else p[0]) for kk, p, q in runs]
spf = []
for L in lines:
    f = factorint(L)
    spf.append(min(f) if f else L)
print("smallest-prime-factor of the travel line, histogram:",
      dict(sorted(collections.Counter(spf).items())))
