"""Erdos #1212: the reduced graph H (odd-odd "hubs").

G:  V = {(x,y) in N^2 : gcd(x,y)=1}, edges = +-1 in one coordinate.
A:  admissible vertices = V with min(x,y) > 1 and (x composite or y composite).

Reduction (verified in verify_reduction.py):
  * gcd(x,y)=1 => not both even, so every vertex has an odd coordinate.
  * horizontal step needs y odd, vertical step needs x odd.
  * hence A (restricted to x,y >= 3) is exactly the barycentric subdivision of

        H:  V(H) = {(a,b) : a,b odd, >= 3, gcd(a,b)=1, not (a prime and b prime)}
            (a,b) ~ (a+2,b)  iff both are in V(H) and gcd(a+1,b)=1
            (a,b) ~ (a,b+2)  iff both are in V(H) and gcd(a,b+1)=1

    because the subdivision vertex has one even coordinate >= 4, which is
    automatically composite, so the composite condition is free there.

An infinite path in H lifts to an infinite path in A.

Indexing: a = 2*i+1, b = 2*j+1.  Arrays are [j, i] (row-major over columns).
"""

import numpy as np


def prime_mask(n):
    p = np.ones(n + 1, dtype=bool)
    p[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if p[i]:
            p[i * i:: i] = False
    return p


def hub_matrix(A, B):
    """V[j,i] for a=2i+1 <= A, b=2j+1 <= B: (a,b) is a vertex of H."""
    na = (A - 1) // 2 + 1
    nb = (B - 1) // 2 + 1
    aa = 2 * np.arange(na, dtype=np.int64) + 1
    bb = 2 * np.arange(nb, dtype=np.int64) + 1
    pr = prime_mask(max(A, B))
    pa = pr[aa]
    V = np.zeros((nb, na), dtype=bool)
    for j, b in enumerate(bb):
        if b < 3:
            continue
        ok = (np.gcd(aa, b) == 1) & (aa >= 3)
        if pr[b]:
            ok &= ~pa
        V[j] = ok
    return V, aa, bb


def edges(A, B, V=None, aa=None, bb=None):
    """Boolean edge masks.

    Hmask[j,i]  : edge (a,b)--(a+2,b)     (i -> i+1)
    Vmask[j,i]  : edge (a,b)--(a,b+2)     (j -> j+1)
    """
    if V is None:
        V, aa, bb = hub_matrix(A, B)
    nb, na = V.shape
    Hm = np.zeros((nb, na), dtype=bool)
    Vm = np.zeros((nb, na), dtype=bool)
    for j, b in enumerate(bb):
        if b < 3:
            continue
        mid = np.gcd(aa + 1, b) == 1          # gcd(a+1, b) == 1
        Hm[j, :-1] = V[j, :-1] & V[j, 1:] & mid[:-1]
    for j in range(nb - 1):
        b = bb[j]
        mid = np.gcd(aa, b + 1) == 1          # gcd(a, b+1) == 1
        Vm[j] = V[j] & V[j + 1] & mid
    return Hm, Vm


def components(A, B):
    """Connected components of H on the box a<=A, b<=B.

    Returns (label[j,i] (-1 off V), ncomp, V, aa, bb).
    """
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components as scc

    V, aa, bb = hub_matrix(A, B)
    Hm, Vm = edges(A, B, V, aa, bb)
    nb, na = V.shape
    idx = np.arange(nb * na, dtype=np.int32).reshape(nb, na)

    src = []
    dst = []
    jj, ii = np.nonzero(Hm)
    src.append(idx[jj, ii]); dst.append(idx[jj, ii + 1])
    jj, ii = np.nonzero(Vm)
    src.append(idx[jj, ii]); dst.append(idx[jj + 1, ii])
    src = np.concatenate(src); dst = np.concatenate(dst)

    g = coo_matrix((np.ones(src.size, dtype=np.int8), (src, dst)),
                   shape=(nb * na, nb * na))
    ncomp, lab = scc(g, directed=False)
    lab = lab.reshape(nb, na)
    lab = np.where(V, lab, -1)
    return lab, ncomp, V, aa, bb


def travel_rows(A, B):
    """R[j,i] = row b=2j+1 permits the horizontal hop a -> a+2, ignoring the
    'not both prime' condition, i.e. gcd(b, a(a+1)(a+2)) == 1."""
    na = (A - 1) // 2 + 1
    nb = (B - 1) // 2 + 1
    aa = 2 * np.arange(na, dtype=np.int64) + 1
    R = np.zeros((nb, na), dtype=bool)
    for j in range(nb):
        b = 2 * j + 1
        if b < 3:
            continue
        R[j] = ((np.gcd(aa, b) == 1) & (np.gcd(aa + 1, b) == 1)
                & (np.gcd(aa + 2, b) == 1))
    return R, aa
