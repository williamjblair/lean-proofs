"""Extract an explicit band-extension path and verify it from the RAW G.

Phase 1: band [3,1399], from the seed-box start to a column just short of the
         confirmed trap at a=868869.
Phase 2: band [3,1685] (the measured escape band), across the trap and onward.

The stitched hub path is subdivided into a G-path and every vertex / step is
checked against the definition of G with no reuse of the H machinery.
"""
import sys
from math import gcd
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import breadth_first_order
from hub import prime_mask, Builder, TBlock, reach_t, maxcol_t
from census import best_start

A_MID = int(sys.argv[1]) if len(sys.argv) > 1 else 866001
A_END = int(sys.argv[2]) if len(sys.argv) > 2 else 1200001
Y1, Y2, W = 1399, 1685, 5000

pr = prime_mask(A_END + 300000)
B = Builder(Y2, pr)
nb1, nb2 = (Y1 - 1) // 2 + 1, (Y2 - 1) // 2 + 1


def block_path(a_lo, na, nb, j0, i_target, i_src=0):
    """Explicit path inside one block from row j0 at column 0 to a reachable
    vertex at column index i_target."""
    aa, V, Hm, Vm = B.build(a_lo, na, nb=nb)
    Vm = Vm.copy()
    Vm[nb - 1] = False
    vid = (np.cumsum(V.ravel(), dtype=np.int64) - 1).reshape(nb, na)
    nv = int(vid[-1, -1]) + 1
    vf = vid.ravel()
    fh = np.flatnonzero(Hm.ravel())
    fv = np.flatnonzero(Vm.ravel())
    s = np.concatenate([vf[fh], vf[fv]])
    d = np.concatenate([vf[fh + 1], vf[fv + na]])
    g = coo_matrix((np.ones(s.size, np.int8), (s, d)), shape=(nv, nv))
    g = (g + g.T).tocsr()
    src = int(vid[j0, i_src])
    order, pred = breadth_first_order(g, src, directed=False,
                                      return_predecessors=True)
    seen = np.zeros(nv, bool)
    seen[order[order >= 0]] = True
    cand = np.flatnonzero(V[:, i_target])
    cand = cand[seen[vid[cand, i_target]]]
    if cand.size == 0:
        return None
    tgt = int(vid[cand[cand.size // 2], i_target])
    inv = np.flatnonzero(V.ravel())
    seq, u = [], tgt
    while u != src:
        seq.append(u)
        u = int(pred[u])
    seq.append(src)
    seq.reverse()
    return [(int(aa[inv[k] % na]), int(2 * (inv[k] // na) + 1)) for k in seq]


def advance(a, j, nb, step, look, back):
    """Move `step` columns right.  The block also covers `back` columns to the
    LEFT of a, so the extracted segment may backtrack; and `look` columns of
    lookahead past the target, so the vertex we land on provably continues
    (everything reachable inside a block lies in one component, and that
    component touches the block's last column)."""
    a_lo = max(3, a - 2 * back)
    isrc = (a - a_lo) // 2
    na = isrc + step + look
    T = TBlock(*B.build(a_lo, na, nb=nb))
    R = reach_t(T, [j], nb, col0=isrc)
    if not R[na - 1].any() or not R[isrc + step].any():
        return None
    return block_path(a_lo, na, nb, j, isrc + step, isrc)


a0, j0v, _ = best_start(B, nb1, 1, 16000)
j0 = int(j0v[0])
print(f"start ({a0},{2*j0+1})", flush=True)

pts = []
a, j, nb = a0, j0, nb1
STEP, LOOK = 4000, 6000
while a < A_END:
    if a >= A_MID and nb == nb1:
        nb = nb2
        print(f"  BAND EXTENDED to {2*nb-1} at a={a}", flush=True)
    step = STEP
    if nb == nb1:
        step = min(step, (A_MID - a) // 2)
    if step < 1:
        nb = nb2
        continue
    seg = None
    for look, back in ((LOOK, STEP), (2 * LOOK, 3 * STEP), (6 * LOOK, 8 * STEP)):
        seg = advance(a, j, nb, step, look, back)
        if seg is not None:
            break
    if seg is None:
        if nb == nb1:
            nb = nb2
            print(f"  BAND EXTENDED to {2*nb-1} at a={a} (stall)", flush=True)
            continue
        raise SystemExit(f"stuck at a={a} band={2*nb-1}")
    pts.extend(seg if not pts else seg[1:])
    a, b = seg[-1]
    j = (b - 1) // 2
    if (a // (2 * STEP)) % 20 == 0:
        print(f"  a={a} b={b} band={2*nb-1} hubverts={len(pts)}", flush=True)

# ---- de-loop
seen, out = {}, []
for p in pts:
    if p in seen:
        for q in [q for q, k in seen.items() if k > seen[p]]:
            del seen[q]
        del out[seen[p] + 1:]
    else:
        seen[p] = len(out)
        out.append(p)

# ---- subdivide to a G-path
gp = [out[0]]
for (x1, y1), (x2, y2) in zip(out, out[1:]):
    assert abs(x1 - x2) + abs(y1 - y2) == 2
    gp.append(((x1 + x2) // 2, (y1 + y2) // 2))
    gp.append((x2, y2))

# ---- verify from the raw definition of G
P = prime_mask(max(max(p) for p in gp) + 2)


def composite(n):
    return n >= 4 and not P[n]


bad_v = bad_e = 0
for (x, y) in gp:
    if not (gcd(x, y) == 1 and min(x, y) > 1 and (composite(x) or composite(y))):
        bad_v += 1
for (x1, y1), (x2, y2) in zip(gp, gp[1:]):
    if abs(x1 - x2) + abs(y1 - y2) != 1:
        bad_e += 1
xs = [p[0] for p in gp]
ys = [p[1] for p in gp]
print(f"G-path: {len(gp)} vertices, bad_vertices={bad_v} bad_steps={bad_e}")
print(f"  x in [{min(xs)},{max(xs)}]  y in [{min(ys)},{max(ys)}]")
half = [p for p in gp if p[0] <= A_MID]
print(f"  max y before a={A_MID}: {max(p[1] for p in half)}")
print(f"  max y after : {max(p[1] for p in gp if p[0] > A_MID)}")
with open("witness_path.txt", "w") as f:
    f.write(f"# Erdos 1212 band-extension witness, {len(gp)} vertices, "
            f"verified from the raw definition of G\n")
    for x, y in gp:
        f.write(f"{x} {y}\n")
print("wrote witness_path.txt")
