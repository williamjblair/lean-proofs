"""How far right can a path get inside a bounded band 3 <= b <= B?"""
import sys
import numpy as np
from h1212 import components, hub_matrix

A = int(sys.argv[1]) if len(sys.argv) > 1 else 300001
BS = [int(t) for t in sys.argv[2].split(',')] if len(sys.argv) > 2 else \
     [9, 15, 25, 27, 35, 49, 55, 65, 77, 91, 95, 121, 125, 143, 169, 175, 200]

START = (5, 9)      # gcd=1, 9 composite -> a hub

print(f"start = {START}, box a <= {A}")
print(f"{'B':>6} {'ncomp':>9} {'maxA(start comp)':>18} {'maxA(any comp from a<=51)':>26}")
for B in BS:
    lab, ncomp, V, aa, bb = components(A, B)
    si, sj = (START[0] - 1) // 2, (START[1] - 1) // 2
    c = lab[sj, si]
    if c < 0:
        print(f"{B:>6}  start not a vertex")
        continue
    cols = np.nonzero((lab == c).any(axis=0))[0]
    maxa = aa[cols.max()]
    # any component that touches a <= 51
    left = np.unique(lab[:, : 26][lab[:, : 26] >= 0])
    reach = 0
    for cc in left:
        cols2 = np.nonzero((lab == cc).any(axis=0))[0]
        reach = max(reach, aa[cols2.max()])
    print(f"{B:>6} {ncomp:>9} {maxa:>18} {reach:>26}")
