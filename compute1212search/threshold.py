"""B*(A) = least band ceiling admitting a path from a column <= 2000 out to
column A.  Bisection on B (monotone in B: a taller strip contains the shorter
one, so spanning is monotone)."""
import sys
import numpy as np
from strip import components


def spans(A, B):
    L, ncomp, V, aa, bb = components(A, B)
    nb, na = V.shape
    flat = L.ravel(); m = flat >= 0; lb = flat[m]
    cols = np.broadcast_to(np.arange(na, dtype=np.int32), (nb, na)).ravel()[m]
    cmax = np.full(ncomp, -1, np.int32); cmin = np.full(ncomp, na, np.int32)
    np.maximum.at(cmax, lb, cols); np.minimum.at(cmin, lb, cols)
    kleft = int(np.searchsorted(aa, 2000))
    good = (cmin < kleft) & (cmax == na - 1)
    return bool(good.any())


if __name__ == "__main__":
    As = [int(t) for t in sys.argv[1].split(',')]
    LO, HI = int(sys.argv[2]), int(sys.argv[3])
    print(f"{'target A':>10} {'B*(A)':>8} {'B*/log2(A)':>12} {'B*/A^(1/2)':>12}")
    lo0 = LO
    for A in As:
        lo, hi = lo0, HI
        if not spans(A, hi):
            print(f"{A:>10} {'>' + str(hi):>8}")
            continue
        while hi - lo > 2:
            mid = ((lo + hi) // 4) * 2
            if spans(A, mid):
                hi = mid
            else:
                lo = mid
        lo0 = max(LO, lo - 200)
        print(f"{A:>10} {hi:>8} {hi/np.log2(A):>12.1f} {hi/A**0.5:>12.2f}",
              flush=True)
