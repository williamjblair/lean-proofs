"""Read the rule off an extracted hub trajectory."""
import sys
import collections
import numpy as np
from sympy import factorint
from h1212 import prime_mask

P = np.load(sys.argv[1])
pts = [tuple(int(v) for v in p) for p in P]
pr = prime_mask(max(max(p) for p in pts) + 4)

# maximal straight runs
runs = []
k = 'H' if pts[0][1] == pts[1][1] else 'V'
start = pts[0]
for p, q in zip(pts, pts[1:]):
    kk = 'H' if p[1] == q[1] else 'V'
    if kk != k:
        runs.append((k, start, p)); start = p; k = kk
runs.append((k, start, pts[-1]))

H = [r for r in runs if r[0] == 'H']
Vr = [r for r in runs if r[0] == 'V']
print(f"{len(runs)} maximal runs: {len(H)} horizontal, {len(Vr)} vertical")

nright = sum(1 for k, p, q in H if q[0] > p[0])
nleft = sum(1 for k, p, q in H if q[0] < p[0])
hops_r = sum((q[0] - p[0]) // 2 for k, p, q in H if q[0] > p[0])
hops_l = sum((p[0] - q[0]) // 2 for k, p, q in H if q[0] < p[0])
print(f"horizontal runs: {nright} rightward ({hops_r} hops), "
      f"{nleft} leftward ({hops_l} hops)  -> backtracking fraction "
      f"{hops_l/(hops_r+hops_l):.3f}")

hl = collections.Counter(abs(q[0] - p[0]) // 2 for k, p, q in H)
vl = collections.Counter(abs(q[1] - p[1]) // 2 for k, p, q in Vr)
print("horizontal run-length histogram (hops):",
      dict(sorted(hl.items())[:12]), "... max", max(hl))
print("vertical   run-length histogram (hops):",
      dict(sorted(vl.items())[:12]), "... max", max(vl))

# rows used for travel, and their least prime factor
rows = collections.Counter(p[1] for k, p, q in H)
print(f"\n{len(rows)} distinct travel rows used. Top 15 by hops:")
byhops = collections.Counter()
for k, p, q in H:
    byhops[p[1]] += abs(q[0] - p[0]) // 2
print(f"{'row b':>7} {'hops':>7} {'lpf':>5} {'factorisation':>26}")
for b, h in byhops.most_common(15):
    f = factorint(b)
    print(f"{b:>7} {h:>7} {min(f):>5} {str(dict(f)):>26}")

# the governing quantity: least prime factor of the travel row
lpf = collections.Counter()
for k, p, q in H:
    lpf[min(factorint(p[1]))] += abs(q[0] - p[0]) // 2
print("\nhops travelled, by least prime factor of the row:",
      dict(sorted(lpf.items())))

# check the rule: a horizontal run on row b from a1 to a2 must have
# gcd(b, a(a+1)(a+2)) = 1 throughout, and must STOP because that fails
stop_ok = 0
stop_other = 0
for k, p, q in H:
    if q[0] < p[0]:
        a = q[0] - 2
    else:
        a = q[0]
    b = q[1]
    from math import gcd
    if q[0] > p[0]:
        blocked = gcd(b, (a + 1) * (a + 2)) > 1
    else:
        blocked = gcd(b, (a + 1) * (a + 2)) > 1
    stop_ok += blocked
    stop_other += (not blocked)
print(f"\nhorizontal runs that stop at an arithmetic block: {stop_ok}; "
      f"that stop for another reason (shortest-path artefact): {stop_other}")

# growth of y with x
xs = np.array([p[0] for p in pts]); ys = np.array([p[1] for p in pts])
print("\nrunning max of row b vs column a:")
print(f"{'a <=':>10} {'max b so far':>14} {'min b so far':>14}")
for cut in [2000, 4000, 8000, 16000, 32000, 64000]:
    m = xs <= cut
    if m.any():
        print(f"{cut:>10} {ys[m].max():>14} {ys[m].min():>14}")
