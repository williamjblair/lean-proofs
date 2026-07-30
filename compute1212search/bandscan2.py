import sys
import numpy as np
from strip import components

A = int(sys.argv[1])
for B in [int(t) for t in sys.argv[2].split(',')]:
    L, ncomp, V, aa, bb = components(A, B)
    nb, na = V.shape
    flat = L.ravel(); m = flat >= 0; lb = flat[m]
    cols = np.broadcast_to(np.arange(na, dtype=np.int32), (nb, na)).ravel()[m]
    rows = np.broadcast_to(np.arange(nb, dtype=np.int32)[:, None], (nb, na)).ravel()[m]
    cmax = np.full(ncomp, -1, np.int32); cmin = np.full(ncomp, na, np.int32)
    rmax = np.full(ncomp, -1, np.int32); rmin = np.full(ncomp, nb, np.int32)
    np.maximum.at(cmax, lb, cols); np.minimum.at(cmin, lb, cols)
    np.maximum.at(rmax, lb, rows); np.minimum.at(rmin, lb, rows)
    size = np.bincount(lb, minlength=ncomp)
    kleft = int(np.searchsorted(aa, 2000))
    good = (cmin < kleft)
    if not good.any():
        print(f"B={B:>6}: nothing starts left of 2000"); continue
    best = int(np.argmax(np.where(good, cmax, -1)))
    reach = int(aa[cmax[best]])
    tag = "SPANS" if cmax[best] == na - 1 else "stops"
    print(f"B={B:>6}: {tag} a {int(aa[cmin[best]])}..{reach}, "
          f"b {int(bb[rmin[best]])}..{int(bb[rmax[best]])}, size {int(size[best])}")
