"""m(a) = minimal possible max-row over all paths from a fixed source to column a.

This is a bottleneck (minimax) shortest path.  Weight every edge by the larger
row-index of its two endpoints; then the bottleneck value of a path equals the
largest row it visits.  Bottleneck distances are read off the minimum spanning
forest.
"""
import sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import (minimum_spanning_tree, breadth_first_order,
                                  connected_components as scc)
from h1212 import hub_matrix, edges

N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
OUT = sys.argv[2] if len(sys.argv) > 2 else f"bott_{N}.npz"

V, aa, bb = hub_matrix(N, N)
Hm, Vm = edges(N, N, V, aa, bb)
nb, na = V.shape
idx = np.arange(nb * na, dtype=np.int32).reshape(nb, na)

s, d, w = [], [], []
jj, ii = np.nonzero(Hm)
s.append(idx[jj, ii]); d.append(idx[jj, ii + 1]); w.append(bb[jj])
jj, ii = np.nonzero(Vm)
s.append(idx[jj, ii]); d.append(idx[jj + 1, ii]); w.append(bb[jj + 1])
s = np.concatenate(s); d = np.concatenate(d); w = np.concatenate(w).astype(float)
n = nb * na
g = coo_matrix((w, (s, d)), shape=(n, n)).tocsr()

ncomp, lab = scc(g + g.T, directed=False)
lab2 = np.where(V, lab.reshape(nb, na), -1)
S = (np.broadcast_to(aa[None, :], V.shape) + np.broadcast_to(bb[:, None], V.shape))
flat_lab = lab2.ravel(); flat_S = S.ravel()
mask = flat_lab >= 0
mn = np.full(ncomp, 1 << 60); mx = np.full(ncomp, -1)
np.minimum.at(mn, flat_lab[mask], flat_S[mask])
np.maximum.at(mx, flat_lab[mask], flat_S[mask])
span = mx - mn
giant = int(np.argmax(span))
print(f"N={N}: giant comp span(a+b)={span[giant]} in [{mn[giant]},{mx[giant]}]"
      f"  size={(flat_lab == giant).sum()}")

# source = the giant's vertex of least a+b (ties -> least a)
cand = np.argwhere((lab2 == giant) & (S == mn[giant]))
j0, i0 = cand[0]
print(f"source = (a,b) = ({aa[i0]}, {bb[j0]})")
src = int(idx[j0, i0])

mst = minimum_spanning_tree(g + g.T)
mst = (mst + mst.T).tocsr()
order, pred = breadth_first_order(mst, src, directed=False,
                                  return_predecessors=True)
bott = np.full(n, -1, dtype=np.int64)
bott[src] = bb[j0]
indptr, indices, data = mst.indptr, mst.indices, mst.data
bt = bott
pr = pred
for u in order[1:]:
    p = pr[u]
    lo, hi = indptr[p], indptr[p + 1]
    k = lo + int(np.searchsorted(indices[lo:hi], u))
    bt[u] = max(bt[p], int(data[k]))
bott = bt.reshape(nb, na)
bott = np.where(V & (lab2 == giant), bott, -1)

# m(a): min over rows of the bottleneck value in column a
col = np.where(bott >= 0, bott, 1 << 40).min(axis=0)
col = np.where(col == (1 << 40), -1, col)
np.savez(OUT, aa=aa, m=col, bott=bott, source=(int(aa[i0]), int(bb[j0])))

ok = col >= 0
print(f"\ncolumns of the giant reached: {ok.sum()} of {na};"
      f" largest a = {aa[ok].max()}")

# minimum row of the giant present in each column
minrow = np.where(lab2 == giant, np.broadcast_to(bb[:, None], V.shape),
                  1 << 40).min(axis=0)

print(f"\nbinned profile ({'a-bin':>16} {'#cols':>6} {'median m(a)':>12} "
      f"{'min m(a)':>9} {'max m(a)':>9} {'median minrow':>14})")
lo = 1
while lo < N:
    hi = min(2 * lo, N)
    sel = ok & (aa >= lo) & (aa < hi)
    if sel.sum():
        c = col[sel]
        mr = minrow[(aa >= lo) & (aa < hi) & (minrow < (1 << 40))]
        print(f"{f'[{lo},{hi})':>16} {sel.sum():>6} {int(np.median(c)):>12} "
              f"{c.min():>9} {c.max():>9} "
              f"{int(np.median(mr)) if mr.size else -1:>14}")
    lo = hi
