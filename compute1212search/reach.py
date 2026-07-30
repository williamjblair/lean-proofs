"""reach(B) = how far right a path can go while staying in rows b <= B.

For each B: pick the best start from an exact box computation, then run the
windowed sweep (exact inside each 25000-column window) until it dies.
"""
import sys
import numpy as np
from strip import components
from windowed import sweep

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3000001
BS = [int(t) for t in sys.argv[2].split(',')] if len(sys.argv) > 2 else \
    [200, 300, 400, 600, 800, 1000, 1200, 1400]
SEED_BOX = 30001

print(f"{'B':>6} {'start (a,b)':>16} {'reach in a':>14} {'log2 reach':>11}")
for B in BS:
    L, ncomp, V, aa, bb = components(SEED_BOX, B)
    nb, na = V.shape
    flat = L.ravel(); m = flat >= 0; lb = flat[m]
    cols = np.broadcast_to(np.arange(na, dtype=np.int32), (nb, na)).ravel()[m]
    cmax = np.full(ncomp, -1, np.int32); cmin = np.full(ncomp, na, np.int32)
    np.maximum.at(cmax, lb, cols); np.minimum.at(cmin, lb, cols)
    c = int(np.argmax(cmax - cmin))          # largest a-span, not rightmost
    w = np.argwhere(L == c)
    j, i = w[np.argmin(w[:, 1])]
    a0, b0 = int(aa[i]), int(bb[j])
    a, rows, _ = sweep(B, AMAX, a0, [b0])
    print(f"{B:>6} {str((a0,b0)):>16} {a:>14} {np.log2(a):>11.2f}", flush=True)
