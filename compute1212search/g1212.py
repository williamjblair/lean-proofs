"""Core library for Erdos #1212 computational search.

Graph G: vertices (x,y) in N^2 with gcd(x,y)=1; edges join vertices differing by
exactly 1 in one coordinate (the *other* endpoint must also be a vertex, i.e.
coprime).

Constrained vertex set A ("admissible"):
    gcd(x,y) = 1,  min(x,y) > 1,  and (x composite or y composite).

We want a path to infinity inside A.

Everything here is exact integer arithmetic on numpy arrays.
"""

import numpy as np


# ----------------------------------------------------------------- sieves


def prime_mask(n):
    """Boolean array p[0..n], p[k] iff k is prime."""
    p = np.ones(n + 1, dtype=bool)
    p[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if p[i]:
            p[i * i:: i] = False
    return p


def composite_mask(n):
    """c[k] iff k is composite (k >= 4 and not prime)."""
    p = prime_mask(n)
    c = ~p
    c[:4] = False          # 0,1 are neither; 2,3 are prime
    return c


def smallest_prime_factor(n):
    spf = np.zeros(n + 1, dtype=np.int64)
    for i in range(2, n + 1):
        if spf[i] == 0:
            spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])
    return spf


def gcd_row(y, X):
    """np.gcd(arange(0,X+1), y)."""
    return np.gcd(np.arange(X + 1, dtype=np.int64), np.int64(y))


# ------------------------------------------------------- admissibility


def admissible_matrix(X, Y):
    """A[y, x] for 0<=x<=X, 0<=y<=Y : (x,y) is an admissible vertex."""
    n = max(X, Y)
    comp = composite_mask(n)
    compX = comp[: X + 1]
    xs = np.arange(X + 1, dtype=np.int64)
    A = np.zeros((Y + 1, X + 1), dtype=bool)
    for y in range(2, Y + 1):
        cop = np.gcd(xs, np.int64(y)) == 1
        ok = cop & (xs > 1)
        if comp[y]:
            A[y] = ok
        else:
            A[y] = ok & compX
    return A


# ---------------------------------------------------- run-based components


def _runs_along_axis(mask, axis):
    """Label maximal runs of True along `axis`.

    Returns (labels, count).  labels has the same shape as mask; entries where
    mask is False are -1.  Runs are numbered 0..count-1.
    """
    m = mask if axis == 1 else mask.T          # runs along last axis
    starts = m.copy()
    starts[:, 1:] &= ~m[:, :-1]
    ids = np.cumsum(starts.ravel()) - 1
    ids = ids.reshape(m.shape)
    ids = np.where(m, ids, -1)
    count = int(starts.sum())
    return (ids if axis == 1 else ids.T), count


def components(X, Y, A=None):
    """Connected components of the admissible subgraph on [0,X] x [0,Y].

    Horizontal edges exist only on odd rows y (proved below); vertical edges
    only on odd columns x.  Every admissible vertex therefore lies on at least
    one "run": a maximal horizontal interval (odd row) or maximal vertical
    interval (odd column).  Contracting each run to a node and joining runs that
    share a vertex gives exactly the connected components of the graph.

    Returns (label[y, x] with -1 off A, ncomp).
    """
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components as scc

    if A is None:
        A = admissible_matrix(X, Y)
    Yp1, Xp1 = A.shape

    odd_rows = (np.arange(Yp1) % 2 == 1)[:, None]
    odd_cols = (np.arange(Xp1) % 2 == 1)[None, :]

    hmask = A & odd_rows          # vertices that can move horizontally
    vmask = A & odd_cols          # vertices that can move vertically

    hid, nh = _runs_along_axis(hmask, axis=1)
    vid, nv = _runs_along_axis(vmask, axis=0)

    both = hmask & vmask
    hh = hid[both]
    vv = vid[both] + nh
    n = nh + nv
    g = coo_matrix((np.ones(hh.size, dtype=np.int8), (hh, vv)), shape=(n, n))
    ncomp, lab = scc(g, directed=False)

    out = np.full(A.shape, -1, dtype=np.int64)
    out[hmask] = lab[hid[hmask]]
    out[vmask] = lab[vid[vmask] + nh]
    # a vertex in both must agree (it forced the union) -- assert cheaply
    return out, ncomp


def reach_profile(X, Y, start):
    """Component label of `start`, and the max x it reaches, per row."""
    lab, _ = components(X, Y)
    sx, sy = start
    c = lab[sy, sx]
    assert c >= 0, f"start {start} is not admissible"
    return lab, c
