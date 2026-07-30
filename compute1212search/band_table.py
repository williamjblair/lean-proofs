"""Least band ceiling B such that ONE component of the strip a<=A, b<=B spans
from a small column out to column A."""
import sys
import numpy as np
from strip import components


def spans_to(A, B, left=5000):
    """Is there a component with a vertex at a<=left and one in the last column?"""
    L, ncomp, V, aa, bb = components(A, B)
    kleft = int(np.searchsorted(aa, left))
    lo = np.unique(L[:, :kleft]); lo = lo[lo >= 0]
    hi = np.unique(L[:, -1]);     hi = hi[hi >= 0]
    both = np.intersect1d(lo, hi)
    if both.size == 0:
        return None
    best = None
    for c in both:
        m = (L == c)
        cols = np.flatnonzero(m.any(axis=0))
        rows = np.flatnonzero(m.any(axis=1))
        cand = (int(aa[cols.min()]), int(bb[rows.min()]), int(bb[rows.max()]),
                int(m.sum()))
        if best is None or cand[0] < best[0]:
            best = cand
    return best


if __name__ == "__main__":
    targets = [int(t) for t in sys.argv[1].split(',')]
    cands = [int(t) for t in sys.argv[2].split(',')]
    print(f"{'target A':>10} {'least B (of those tried)':>26} "
          f"{'a-min':>8} {'b range used':>18} {'comp size':>12}")
    for A in targets:
        found = None
        for B in cands:
            r = spans_to(A, B)
            if r is not None:
                found = (B, r); break
        if found is None:
            print(f"{A:>10} {'none of ' + str(cands):>26}")
        else:
            B, (amin, bmin, bmax, sz) = found
            print(f"{A:>10} {B:>26} {amin:>8} {str((bmin,bmax)):>18} {sz:>12}")
