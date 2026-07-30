"""Exact connected components of H on a long thin strip  3<=a<=A, 3<=b<=B.

Memory-lean: never materialises an index matrix; flat indices come straight out
of np.flatnonzero on the ravelled masks, and vertices are compacted before the
graph is built.  Left moves are fully allowed, so this is exact for every path
that stays inside the strip (truncation in a is conservative: it can only make
the answer worse, never better).
"""
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components as scc
from h1212 import prime_mask


def build(A, B):
    na = (A - 1) // 2 + 1
    nb = (B - 1) // 2 + 1
    aa = (2 * np.arange(na, dtype=np.int64) + 1)
    bb = (2 * np.arange(nb, dtype=np.int64) + 1)
    pr = prime_mask(max(A, B) + 2)
    pa = pr[aa]

    V = np.zeros((nb, na), dtype=bool)
    for j in range(nb):
        b = int(bb[j])
        if b < 3:
            continue
        ok = (np.gcd(aa, b) == 1) & (aa >= 3)
        if pr[b]:
            ok &= ~pa
        V[j] = ok

    Hm = np.zeros((nb, na), dtype=bool)
    Vm = np.zeros((nb, na), dtype=bool)
    for j in range(nb):
        b = int(bb[j])
        if b < 3:
            continue
        Hm[j, :-1] = V[j, :-1] & V[j, 1:] & (np.gcd(aa[:-1] + 1, b) == 1)
        if j + 1 < nb:
            Vm[j] = V[j] & V[j + 1] & (np.gcd(aa, b + 1) == 1)
    return V, Hm, Vm, aa, bb, na, nb


def components(A, B):
    V, Hm, Vm, aa, bb, na, nb = build(A, B)
    vid = np.cumsum(V.ravel(), dtype=np.int32) - 1
    nv = int(vid[-1]) + 1
    fh = np.flatnonzero(Hm.ravel())
    fv = np.flatnonzero(Vm.ravel())
    src = np.concatenate([vid[fh], vid[fv]])
    dst = np.concatenate([vid[fh + 1], vid[fv + na]])
    del fh, fv, Hm, Vm
    g = coo_matrix((np.ones(src.size, dtype=np.int8), (src, dst)),
                   shape=(nv, nv))
    ncomp, lab = scc(g, directed=False)
    del g, src, dst
    L = np.full(na * nb, -1, dtype=np.int32)
    L[V.ravel()] = lab
    return L.reshape(nb, na), ncomp, V, aa, bb


def span_report(A, B, top=6):
    L, ncomp, V, aa, bb = components(A, B)
    nb, na = V.shape
    flat = L.ravel()
    m = flat >= 0
    cols = np.broadcast_to(np.arange(na, dtype=np.int32), (nb, na)).ravel()[m]
    rows = np.broadcast_to(np.arange(nb, dtype=np.int32)[:, None],
                           (nb, na)).ravel()[m]
    lb = flat[m]
    cmin = np.full(ncomp, na, dtype=np.int32)
    cmax = np.full(ncomp, -1, dtype=np.int32)
    rmax = np.full(ncomp, -1, dtype=np.int32)
    rmin = np.full(ncomp, nb, dtype=np.int32)
    np.minimum.at(cmin, lb, cols)
    np.maximum.at(cmax, lb, cols)
    np.minimum.at(rmin, lb, rows)
    np.maximum.at(rmax, lb, rows)
    size = np.bincount(lb, minlength=ncomp)
    span = cmax - cmin
    order = np.argsort(span)[::-1][:top]
    out = []
    for c in order:
        out.append(dict(comp=int(c), size=int(size[c]),
                        a=(int(aa[cmin[c]]), int(aa[cmax[c]])),
                        b=(int(bb[rmin[c]]), int(bb[rmax[c]])),
                        span=int(aa[cmax[c]] - aa[cmin[c]])))
    return out, L, V, aa, bb


if __name__ == "__main__":
    import sys
    A = int(sys.argv[1]); B = int(sys.argv[2])
    out, L, V, aa, bb = span_report(A, B)
    print(f"strip a<={A}, b<={B}:  |V|={int(V.sum())}")
    print(f"{'size':>10} {'a-span':>10} {'a range':>22} {'b range':>18}")
    for d in out:
        print(f"{d['size']:>10} {d['span']:>10} {str(d['a']):>22} "
              f"{str(d['b']):>18}")
