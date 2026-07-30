"""Windowed exact search: slide a window of W columns along a, doing an exact
connected-component / BFS computation inside each window and carrying the
reachable row-set across the interface.

Sound (never claims a path that does not exist) and linear in A, so it scales
far past what a single box allows.  Backtracking is allowed freely inside a
window, which is all the extracted trajectory ever needs.
"""
import sys
from math import gcd
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components as scc, breadth_first_order
from h1212 import prime_mask


class Window:
    def __init__(self, Bmax, pr):
        self.B = Bmax
        self.nb = (Bmax - 1) // 2 + 1
        self.bb = 2 * np.arange(self.nb, dtype=np.int64) + 1
        self.pr = pr
        self.pb = pr[self.bb]

    def build(self, a_lo, na):
        """Strip over columns a_lo, a_lo+2, ..., a_lo+2(na-1)."""
        aa = a_lo + 2 * np.arange(na, dtype=np.int64)
        nb, bb, pr = self.nb, self.bb, self.pr
        pa = pr[aa]
        V = np.zeros((nb, na), dtype=bool)
        Hm = np.zeros((nb, na), dtype=bool)
        Vm = np.zeros((nb, na), dtype=bool)
        for j in range(nb):
            b = int(bb[j])
            if b < 3:
                continue
            ok = (np.gcd(aa, b) == 1) & (aa >= 3)
            if pr[b]:
                ok &= ~pa
            V[j] = ok
        for j in range(nb):
            b = int(bb[j])
            if b < 3:
                continue
            Hm[j, :-1] = V[j, :-1] & V[j, 1:] & (np.gcd(aa[:-1] + 1, b) == 1)
            if j + 1 < nb:
                Vm[j] = V[j] & V[j + 1] & (np.gcd(aa, b + 1) == 1)
        return aa, V, Hm, Vm

    def graph(self, na, V, Hm, Vm):
        vid = np.cumsum(V.ravel(), dtype=np.int64) - 1
        nv = int(vid[-1]) + 1
        fh = np.flatnonzero(Hm.ravel()); fv = np.flatnonzero(Vm.ravel())
        s = np.concatenate([vid[fh], vid[fv]])
        d = np.concatenate([vid[fh + 1], vid[fv + na]])
        g = coo_matrix((np.ones(s.size, dtype=np.int8), (s, d)), shape=(nv, nv))
        g = (g + g.T).tocsr()
        return g, vid, nv


def sweep(Bmax, Amax, a_start, rows_start, W=25000, want_path=False):
    pr = prime_mask(max(Amax, Bmax) + 4)
    win = Window(Bmax, pr)
    nb = win.nb
    cur_a = a_start
    cur_rows = np.array(sorted(rows_start), dtype=np.int64)
    segs = []
    while cur_a < Amax:
        na = min(W, (Amax - cur_a) // 2 + 1)
        if na < 2:
            break
        aa, V, Hm, Vm = win.build(cur_a, na)
        g, vid, nv = win.graph(na, V, Hm, Vm)
        jseed = (cur_rows - 1) // 2
        jseed = jseed[V[jseed, 0]]
        if jseed.size == 0:
            return cur_a, None, segs
        seeds = vid[jseed * na + 0]
        lab_n, lab = scc(g, directed=False)
        good = np.unique(lab[seeds])
        last = np.flatnonzero(V[:, na - 1])
        if last.size == 0:
            return cur_a, None, segs
        lastv = vid[last * na + (na - 1)]
        keep = np.isin(lab[lastv], good)
        if not keep.any():
            # how far did we get?
            colmax = -1
            flat = np.full(V.size, -1, dtype=np.int64)
            flat[V.ravel()] = lab
            L = flat.reshape(nb, na)
            hit = np.isin(L, good) & V
            cols = np.flatnonzero(hit.any(axis=0))
            return int(aa[cols.max()]) if cols.size else cur_a, None, segs
        nxt_rows = win.bb[last[keep]]
        if want_path:
            src = int(seeds[0])
            order, pred = breadth_first_order(g, src, directed=False,
                                              return_predecessors=True)
            tgt = int(lastv[keep][np.argmin(np.abs(win.bb[last[keep]] -
                                                   win.bb[jseed[0]]))])
            inv = np.flatnonzero(V.ravel())
            seq = []
            u = tgt
            while u != src:
                seq.append(u); u = pred[u]
            seq.append(src); seq.reverse()
            pts = [(int(aa[inv[k] % na]), int(win.bb[inv[k] // na]))
                   for k in seq]
            segs.append(pts)
            cur_rows = np.array([pts[-1][1]], dtype=np.int64)
        else:
            cur_rows = nxt_rows
        cur_a = int(aa[-1])
        print(f"  reached a={cur_a}  rows carried={len(cur_rows)}", flush=True)
    return cur_a, cur_rows, segs


if __name__ == "__main__":
    Bmax = int(sys.argv[1]); Amax = int(sys.argv[2])
    a0 = int(sys.argv[3]) if len(sys.argv) > 3 else 1065
    b0 = int(sys.argv[4]) if len(sys.argv) > 4 else 917
    want = len(sys.argv) > 5 and sys.argv[5] == 'path'
    print(f"band b<={Bmax}, start ({a0},{b0}), target a={Amax}, path={want}")
    a, rows, segs = sweep(Bmax, Amax, a0, [b0], want_path=want)
    print(f"FINAL: reached column a={a}")
    if want:
        # stitch segments, drop loops, verify
        pts = []
        for s in segs:
            pts.extend(s if not pts else s[1:])
        seen = {}
        out = []
        for p in pts:
            if p in seen:
                del out[seen[p] + 1:]
                for q in list(seen):
                    if seen[q] > seen[p]:
                        del seen[q]
            else:
                seen[p] = len(out)
                out.append(p)
        gp = [out[0]]
        for (x1, y1), (x2, y2) in zip(out, out[1:]):
            gp.append(((x1 + x2) // 2, (y1 + y2) // 2)); gp.append((x2, y2))
        pr = prime_mask(max(max(p) for p in gp) + 4)
        comp = lambda n: n >= 4 and not pr[n]
        bad = 0
        for x, y in gp:
            if gcd(x, y) != 1 or min(x, y) <= 1 or not (comp(x) or comp(y)):
                bad += 1
        for (x1, y1), (x2, y2) in zip(gp, gp[1:]):
            if abs(x1 - x2) + abs(y1 - y2) != 1:
                bad += 1
        xs = [p[0] for p in gp]; ys = [p[1] for p in gp]
        print(f"stitched G-path: {len(gp)} vertices, violations={bad}, "
              f"x {min(xs)}..{max(xs)}, y {min(ys)}..{max(ys)}")
        fn = f"trajectory_B{Bmax}_A{Amax}.txt"
        with open(fn, "w") as f:
            f.write(f"# Erdos 1212 witness path in G (verified, {len(gp)} vertices)\n")
            f.write(f"# x in [{min(xs)},{max(xs)}], y in [{min(ys)},{max(ys)}]\n")
            for x, y in gp:
                f.write(f"{x} {y}\n")
        np.save(fn.replace('.txt', '_hub.npy'), np.array(out))
        print("wrote", fn)
