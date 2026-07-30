"""Two-pass windowed witness extraction.

Pass 1 (forward): carry the FULL set of reachable rows across each window
interface, so nothing is thrown away.
Pass 2 (backward): re-solve each window and pin down one concrete vertex at
each interface, giving a single genuine path.

The result is verified against the raw definition of the problem.
"""
import sys
from math import gcd
import numpy as np
from scipy.sparse.csgraph import connected_components as scc, breadth_first_order
from windowed import Window
from h1212 import prime_mask

Bmax = int(sys.argv[1]); Amax = int(sys.argv[2])
a0 = int(sys.argv[3]); b0 = int(sys.argv[4])
W = int(sys.argv[5]) if len(sys.argv) > 5 else 25000

pr = prime_mask(max(Amax, Bmax) + 4)
win = Window(Bmax, pr)
nb = win.nb

# ---------------- pass 1: forward, full reachable sets
bounds = []
sets = [np.array([b0], dtype=np.int64)]
cur_a = a0
while cur_a < Amax:
    na = min(W, (Amax - cur_a) // 2 + 1)
    if na < 2:
        break
    aa, V, Hm, Vm = win.build(cur_a, na)
    g, vid, nv = win.graph(na, V, Hm, Vm)
    j0 = (sets[-1] - 1) // 2
    j0 = j0[V[j0, 0]]
    if j0.size == 0:
        break
    lab_n, lab = scc(g, directed=False)
    good = np.unique(lab[vid[j0 * na + 0]])
    last = np.flatnonzero(V[:, na - 1])
    keep = last[np.isin(lab[vid[last * na + (na - 1)]], good)] if last.size else last
    if keep.size == 0:
        break
    bounds.append((cur_a, na))
    sets.append(win.bb[keep])
    cur_a = int(aa[-1])
print(f"forward: {len(bounds)} windows, reached column a={cur_a}", flush=True)

# ---------------- pass 2: backward, pin one vertex per interface
target_row = int(sets[-1][len(sets[-1]) // 2])
hub_path = []
for k in range(len(bounds) - 1, -1, -1):
    lo, na = bounds[k]
    aa, V, Hm, Vm = win.build(lo, na)
    g, vid, nv = win.graph(na, V, Hm, Vm)
    inv = np.flatnonzero(V.ravel())
    tj = (target_row - 1) // 2
    tgt = int(vid[tj * na + (na - 1)])
    order, pred = breadth_first_order(g, tgt, directed=False,
                                      return_predecessors=True)
    j0 = (sets[k] - 1) // 2
    j0 = j0[V[j0, 0]]
    cand = vid[j0 * na + 0]
    reach = cand[pred[cand] != -9999]
    if k == 0:
        reach = np.array([vid[((b0 - 1) // 2) * na + 0]])
    assert reach.size, f"window {k}: no seed reaches the target"
    s = int(reach[0])
    seq = []
    u = s
    while u != tgt:
        seq.append(u); u = pred[u]
    seq.append(tgt)
    pts = [(int(aa[inv[q] % na]), int(win.bb[inv[q] // na])) for q in seq]
    hub_path = pts + hub_path[1:] if hub_path else pts
    target_row = pts[0][1]
    print(f"  window {k}: a {lo}..{int(aa[-1])}, entered at row {target_row}",
          flush=True)

# ---------------- lift to G and verify from the definition
gp = [hub_path[0]]
for (x1, y1), (x2, y2) in zip(hub_path, hub_path[1:]):
    assert abs(x1 - x2) + abs(y1 - y2) == 2, ((x1, y1), (x2, y2))
    gp.append(((x1 + x2) // 2, (y1 + y2) // 2)); gp.append((x2, y2))

pr2 = prime_mask(max(max(p) for p in gp) + 4)
comp = lambda n: n >= 4 and not pr2[n]
bad = []
for x, y in gp:
    if gcd(x, y) != 1 or min(x, y) <= 1 or not (comp(x) or comp(y)):
        bad.append((x, y))
for (x1, y1), (x2, y2) in zip(gp, gp[1:]):
    if abs(x1 - x2) + abs(y1 - y2) != 1:
        bad.append(((x1, y1), (x2, y2)))
xs = [p[0] for p in gp]; ys = [p[1] for p in gp]
print(f"G-path: {len(gp)} vertices, violations={len(bad)}, "
      f"x {min(xs)}..{max(xs)}, y {min(ys)}..{max(ys)}, "
      f"distinct vertices={len(set(gp))}")
if bad:
    print(bad[:5]); sys.exit(1)

fn = f"trajectory_B{Bmax}_to{max(xs)}.txt"
with open(fn, "w") as f:
    f.write("# Erdos 1212: path in G with gcd(x,y)=1, min(x,y)>1, "
            "x or y composite, unit steps.  Verified from the definition.\n")
    f.write(f"# {len(gp)} vertices; x in [{min(xs)},{max(xs)}]; "
            f"y in [{min(ys)},{max(ys)}]\n")
    for x, y in gp:
        f.write(f"{x} {y}\n")
np.save(fn.replace('.txt', '_hub.npy'), np.array(hub_path))
print("wrote", fn)
