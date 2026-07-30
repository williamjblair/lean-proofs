"""Monotone forward sweep in H: build a genuine path with a strictly increasing
column, allowed to move vertically inside a column.

R(a) = set of rows b <= Bmax such that (a,b) is reachable from the start by a
path whose column never decreases.  This is an UNDER-approximation of
reachability (no backtracking), so anything it finds is a real path.

    R(a+2) = vclose_{a+2}( { b in R(a) : gcd(a+1,b) = 1 and (a+2,b) is a hub } )

vclose_c(T) = union of the maximal vertical runs of column c that meet T.
"""
import numpy as np
from h1212 import prime_mask


class Sweeper:
    def __init__(self, Bmax, Amax):
        self.Bmax = Bmax
        self.nb = (Bmax - 1) // 2 + 1
        self.bb = 2 * np.arange(self.nb, dtype=np.int64) + 1
        self.pr = prime_mask(max(Bmax, Amax) + 2)
        self.pb = self.pr[self.bb]
        self.valid = self.bb >= 3

    def hubs(self, a):
        """boolean over rows: (a,b) is a hub of H."""
        h = (np.gcd(self.bb, a) == 1) & self.valid
        if self.pr[a]:
            h &= ~self.pb
        return h

    def vruns(self, a, h=None):
        """run ids of the maximal vertical runs of column a (h = hub mask)."""
        if h is None:
            h = self.hubs(a)
        ve = h[:-1] & h[1:] & (np.gcd(a, self.bb[:-1] + 1) == 1)
        rid = np.empty(self.nb, dtype=np.int64)
        rid[0] = 0
        np.cumsum(~ve, out=rid[1:])
        return rid, h

    def vclose(self, a, T, h=None):
        rid, h = self.vruns(a, h)
        if not T.any():
            return T, h
        keep = np.zeros(rid.max() + 2, dtype=bool)
        keep[rid[T]] = True
        return h & keep[rid], h

    def run(self, a0, b0, Amax, keep_sets=False):
        """Sweep from the vertical run of (a0,b0).  Returns (last_a, sets)."""
        h = self.hubs(a0)
        assert h[(b0 - 1) // 2], f"({a0},{b0}) is not a hub"
        T = np.zeros(self.nb, dtype=bool)
        T[(b0 - 1) // 2] = True
        R, h = self.vclose(a0, T, h)
        sets = {a0: np.packbits(R)} if keep_sets else None
        a = a0
        while a + 2 <= Amax:
            mid = np.gcd(a + 1, self.bb) == 1
            hn = self.hubs(a + 2)
            T = R & mid & hn
            if not T.any():
                return a, sets, None
            R, _ = self.vclose(a + 2, T, hn)
            a += 2
            if keep_sets:
                sets[a] = np.packbits(R)
        return a, sets, R

    def reconstruct(self, a0, b0, a_end, sets):
        """Walk the stored sets backwards into an explicit vertex list in H."""
        R = np.unpackbits(sets[a_end], count=self.nb).astype(bool)
        cur_j = int(np.flatnonzero(R)[0])
        out = [(a_end, int(self.bb[cur_j]))]
        a = a_end
        while a > a0:
            Rp = np.unpackbits(sets[a - 2], count=self.nb).astype(bool)
            mid = np.gcd(a - 1, self.bb) == 1
            h = self.hubs(a)
            T = Rp & mid & h
            rid, _ = self.vruns(a, h)
            # slide vertically inside column a from cur_j to some j in T
            tj = np.flatnonzero(T & (rid == rid[cur_j]))
            assert tj.size, f"reconstruction failed at column {a}"
            j = int(tj[np.argmin(np.abs(tj - cur_j))])
            step = 1 if j > cur_j else -1
            for k in range(cur_j + step, j + step, step):
                out.append((a, int(self.bb[k])))
            out.append((a - 2, int(self.bb[j])))
            cur_j = j
            a -= 2
        out.reverse()
        return out
