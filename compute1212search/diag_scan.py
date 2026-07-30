"""Do components grow with the box?  Look along the diagonal, not in a band."""
import sys
import numpy as np
from h1212 import components

for N in [int(t) for t in sys.argv[1].split(',')]:
    lab, ncomp, V, aa, bb = components(N, N)
    nb, na = V.shape
    L = lab[V]
    A = np.broadcast_to(aa[None, :], V.shape)[V]
    B = np.broadcast_to(bb[:, None], V.shape)[V]
    S = A + B
    order = np.argsort(L, kind='stable')
    L2, A2, B2, S2 = L[order], A[order], B[order], S[order]
    bnd = np.flatnonzero(np.diff(L2)) + 1
    seg = np.concatenate(([0], bnd, [L2.size]))
    rows = []
    for k in range(len(seg) - 1):
        lo, hi = seg[k], seg[k + 1]
        rows.append((hi - lo, S2[lo:hi].min(), S2[lo:hi].max(),
                     A2[lo:hi].min(), A2[lo:hi].max(),
                     B2[lo:hi].min(), B2[lo:hi].max()))
    rows.sort(key=lambda r: r[2] - r[1], reverse=True)
    tot = len(rows)
    print(f"N={N}: {tot} components on V, |V|={V.sum()}")
    print(f"  {'size':>7} {'span(a+b)':>10} {'a+b range':>18} {'a range':>16} {'b range':>16}")
    for r in rows[:5]:
        print(f"  {r[0]:>7} {r[2]-r[1]:>10} {str((r[1],r[2])):>18} "
              f"{str((r[3],r[4])):>16} {str((r[5],r[6])):>16}")
    big = max(r[0] for r in rows)
    print(f"  max size={big}   max span(a+b)={rows[0][2]-rows[0][1]}"
          f"   (box diag span = {2*N-6})")
