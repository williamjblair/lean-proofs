"""Diagnose exactly why the band-limited search stalls at a given wall."""
import sys
from math import gcd
import numpy as np
from sympy import factorint
from scipy.sparse.csgraph import connected_components as scc
from windowed import Window
from h1212 import prime_mask

Bmax = int(sys.argv[1]); Amax = int(sys.argv[2]); W = 25000
pr = prime_mask(Amax + 8)
win = Window(Bmax, pr)
cur_a, cur_rows = 1065, np.array([917], dtype=np.int64)
while True:
    na = min(W, (Amax - cur_a) // 2 + 1)
    aa, V, Hm, Vm = win.build(cur_a, na)
    g, vid, nv = win.graph(na, V, Hm, Vm)
    j0 = (cur_rows - 1) // 2; j0 = j0[V[j0, 0]]
    n_, lab = scc(g, directed=False)
    good = np.unique(lab[vid[j0 * na + 0]])
    flat = np.full(V.size, -1, dtype=np.int64); flat[V.ravel()] = lab
    L = flat.reshape(win.nb, na)
    hit = np.isin(L, good) & V
    cols = np.flatnonzero(hit.any(axis=0))
    last = np.flatnonzero(V[:, na - 1])
    keep = last[np.isin(lab[vid[last * na + (na - 1)]], good)] if last.size else last
    if keep.size == 0:
        acut = int(aa[cols.max()])
        print(f"STALL at column a = {acut}  (window {cur_a}..{int(aa[-1])})\n")
        for d in range(6, -1, -1):
            i = int(cols.max()) - d
            if i < 0:
                continue
            a = int(aa[i])
            R = np.flatnonzero(hit[:, i])
            P = a * (a + 1) * (a + 2)
            openr = [int(b) for b in win.bb
                     if b >= 3 and gcd(int(b), P) == 1
                     and not (pr[int(b)] and (pr[a] or pr[a + 2]))]
            inter = sorted(set(int(v) for v in win.bb[R]) & set(openr))
            nv_ = int((np.gcd(a, win.bb[:-1] + 1) == 1).sum())
            print(f"a={a:>9} lpf(a)={min(factorint(a)):>5} "
                  f"reachable rows={R.size:>4}  open rows={len(openr):>4}  "
                  f"reachable AND open={len(inter):>3}  "
                  f"vertical-mobile rows at a={nv_:>4}")
            if R.size and R.size <= 14:
                print(f"            reachable = {[int(v) for v in win.bb[R]]}")
        a = acut
        print(f"\nwall column a = {a}")
        for t, n in ((a, a), (a + 1, a + 1), (a + 2, a + 2)):
            print(f"  {t} = {factorint(n)}")
        break
    cur_rows = win.bb[keep]; cur_a = int(aa[-1])
    if cur_a >= Amax:
        print("no stall below", Amax); break
