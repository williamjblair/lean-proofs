"""Erdos #1212 -- hub graph H, built from scratch (independent of compute1212*).

G:  V(G) = {(x,y) in N^2 : gcd(x,y)=1, min(x,y)>1, (x composite or y composite)}
    edges: differ by exactly 1 in exactly one coordinate.

H:  V(H) = {(a,b) : a,b odd >= 3, gcd(a,b)=1, not (a prime and b prime)}
    (a,b)~(a+2,b) iff both in V(H) and gcd(a+1,b)=1
                  <=> gcd(b, a(a+1)(a+2)) = 1 and the prime-pair rule
    (a,b)~(a,b+2) iff both in V(H) and gcd(a,b+1)=1

Indexing: a = a_lo + 2*i (columns), b = 2*j+1 (rows).  Arrays are [j, i].

Block construction uses residue-slice sieving (not per-element gcd): for a
prime p the columns with p | (a+off) form an arithmetic progression in i,
so they are marked with a strided slice.
"""
import numpy as np

# ---------------------------------------------------------------- primes


def prime_mask(n):
    p = np.ones(n + 1, dtype=bool)
    p[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if p[i]:
            p[i * i:: i] = False
    return p


def odd_prime_factors(m):
    """Distinct odd primes dividing m."""
    out = []
    while m % 2 == 0:
        m //= 2
    d = 3
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 2
    if m > 1:
        out.append(m)
    return out


def _start(a_lo, p, off):
    """Smallest i >= 0 with (a_lo + off + 2i) == 0 (mod p).  p odd prime."""
    inv2 = (p + 1) // 2
    return ((-(a_lo + off)) % p) * inv2 % p


# ---------------------------------------------------------------- blocks


class Builder:
    """Builds strips of H for rows b = 1,3,...,<=Ycap."""

    def __init__(self, Ycap, pr):
        self.nb = (Ycap - 1) // 2 + 1
        self.bb = 2 * np.arange(self.nb, dtype=np.int64) + 1
        self.pr = pr
        self.fb = [odd_prime_factors(int(b)) for b in self.bb]
        self.fb1 = [odd_prime_factors(int(b) + 1) for b in self.bb]
        self.bprime = pr[self.bb]

    def build(self, a_lo, na, nb=None):
        """Returns aa, V, Hm, Vm for columns a_lo, a_lo+2, ... (na of them)."""
        if nb is None:
            nb = self.nb
        aa = a_lo + 2 * np.arange(na, dtype=np.int64)
        pa = self.pr[aa]
        V = np.ones((nb, na), dtype=bool)
        Hm = np.zeros((nb, na), dtype=bool)
        Vm = np.zeros((nb, na), dtype=bool)
        if aa[0] < 3:
            V[:, aa < 3] = False
        for j in range(nb):
            b = int(self.bb[j])
            if b < 3:
                V[j] = False
                continue
            row = V[j]
            for p in self.fb[j]:
                row[_start(a_lo, p, 0):: p] = False
            if self.bprime[j]:
                row &= ~pa
        for j in range(nb):
            b = int(self.bb[j])
            if b < 3:
                continue
            mid = np.ones(na, dtype=bool)
            for p in self.fb[j]:
                mid[_start(a_lo, p, 1):: p] = False
            Hm[j, :-1] = V[j, :-1] & V[j, 1:] & mid[:-1]
        for j in range(nb - 1):
            b = int(self.bb[j])
            if b < 3:
                continue
            mid = np.ones(na, dtype=bool)
            for q in self.fb1[j]:
                mid[_start(a_lo, q, 0):: q] = False
            Vm[j] = V[j] & V[j + 1] & mid
        return aa, V, Hm, Vm


# ---------------------------------------------------------------- reach


class TBlock:
    """Column-contiguous transpose of a block: arrays indexed [i, j].

    Vt[i]   vertices of column i
    Ht[i]   horizontal edge column i -> i+1, per row
    Mt[i]   vertical edge row j -> j+1 inside column i (length nb-1)
    St[i]   segment id of row j in the vertical-run decomposition of column i
    nv[i]   number of vertical edges in column i (0 => closure is the identity)
    """

    def __init__(self, aa, V, Hm, Vm):
        nb, na = V.shape
        self.aa = aa
        self.na, self.nb = na, nb
        self.Vt = np.ascontiguousarray(V.T)
        self.Ht = np.ascontiguousarray(Hm.T)
        self.Mt = np.ascontiguousarray(Vm[:nb - 1].T)
        self.St = np.zeros((na, nb), dtype=np.int32)
        np.cumsum(~self.Mt, axis=1, out=self.St[:, 1:])
        self.nvert = self.Mt.sum(axis=1)


def reach_t(T, seed_rows, nbq, col0=0, sweeps=64):
    """Exact reachable set inside the block using only rows j < nbq.
    Returns bool R[na, nbq]."""
    na = T.na
    Vt, Ht, Mt, St = T.Vt, T.Ht, T.Mt, T.St
    R = np.zeros((na, nbq), dtype=bool)
    sr = np.asarray(seed_rows, dtype=np.int64)
    sr = sr[sr < nbq]
    sr = sr[Vt[col0, sr]]
    if sr.size == 0:
        return R
    R[col0, sr] = True
    nseg = int(St[:, nbq - 1].max()) + 2
    hit = np.zeros(nseg, dtype=bool)

    def vclose(i):
        col = R[i]
        if T.nvert[i] == 0 or not col.any():
            return
        s = St[i, :nbq]
        idx = s[col]
        hit[idx] = True
        np.logical_and(hit[s], Vt[i, :nbq], out=col)
        hit[idx] = False

    tot = -1
    for _ in range(sweeps):
        for i in range(na):
            if i and R[i - 1].any():
                R[i] |= R[i - 1] & Ht[i - 1, :nbq]
            vclose(i)
        for i in range(na - 2, -1, -1):
            if R[i + 1].any():
                R[i] |= R[i + 1] & Ht[i, :nbq]
            vclose(i)
        s = int(R.sum())
        if s == tot:
            break
        tot = s
    return R


def maxcol_t(R):
    c = np.flatnonzero(R.any(axis=1))
    return int(c[-1]) if c.size else -1
