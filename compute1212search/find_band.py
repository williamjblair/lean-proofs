"""For a range of band ceilings Bmax, how far right does the monotone sweep get?

Also: binary-search the least Bmax that reaches a given target column.
"""
import sys
import numpy as np
from sweep import Sweeper
from h1212 import prime_mask

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100001
A0 = int(sys.argv[2]) if len(sys.argv) > 2 else 1261
B0 = int(sys.argv[3]) if len(sys.argv) > 3 else 535

print(f"start hub (a,b) = ({A0},{B0}), target column {AMAX}")
print(f"{'Bmax':>8} {'reached column a':>18} {'a/start':>10}")
for Bmax in [200, 400, 800, 1200, 1600, 2400, 3200, 4800, 6400, 9600]:
    if Bmax < B0:
        continue
    sw = Sweeper(Bmax, AMAX)
    if not sw.hubs(A0)[(B0 - 1) // 2]:
        print(f"{Bmax:>8}  start not a hub"); continue
    a, _, R = sw.run(A0, B0, AMAX)
    print(f"{Bmax:>8} {a:>18} {a / A0:>10.1f}")
