"""For a fixed set of rows, count how many are open for the hop a -> a+2 at
each column a, and locate the wall columns (where none is open).

Row b is open at a  iff  (a,b) and (a+2,b) are hubs and gcd(a+1,b)=1, i.e.
    gcd(b, a(a+1)(a+2)) = 1,   plus  a and a+2 composite when b is prime.
"""
import sys
import numpy as np
from sympy import factorint
from h1212 import prime_mask

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
LO, HI = (int(t) for t in (sys.argv[2].split(',') if len(sys.argv) > 2
                           else ['1327', '1399']))
CH = 2_000_000

rows = [b for b in range(LO | 1, HI + 1, 2)]
pr_small = prime_mask(HI + 4)
info = []
for b in rows:
    f = factorint(b)
    info.append((b, sorted(f), bool(pr_small[b])))
print(f"row set: {len(rows)} rows in [{LO},{HI}]")
print("  " + ", ".join(f"{b}{'(p)' if isp else '=' + '*'.join(map(str, ps))}"
                       for b, ps, isp in info))

pr = prime_mask(AMAX + 4)
comp = np.zeros(AMAX + 5, dtype=bool)
comp[4:AMAX + 5] = ~pr[4:AMAX + 5]

mincount = 1 << 30
worst = []
hist = np.zeros(len(rows) + 1, dtype=np.int64)
lo = 3
while lo <= AMAX:
    hi = min(lo + CH, AMAX)
    aa = np.arange(lo, hi + 1, 2, dtype=np.int64)
    cnt = np.zeros(aa.size, dtype=np.int16)
    for b, ps, isp in info:
        ok = np.ones(aa.size, dtype=bool)
        for p in ps:
            ok &= (aa % p != 0) & ((aa + 1) % p != 0) & ((aa + 2) % p != 0)
        if isp:
            ok &= comp[aa] & comp[aa + 2]
        cnt += ok
    hist += np.bincount(cnt, minlength=len(rows) + 1)[:len(rows) + 1]
    m = cnt.min()
    if m < mincount:
        mincount = int(m)
        worst = [int(v) for v in aa[cnt == m][:10]]
    elif m == mincount:
        worst += [int(v) for v in aa[cnt == m][:5]]
    lo = hi + 1

print(f"\ncolumns a <= {AMAX}: minimum number of simultaneously open rows = "
      f"{mincount}")
print("first columns attaining it:", worst[:10])
print("\nhistogram of #open rows:")
for k in range(min(12, len(rows) + 1)):
    if hist[k]:
        print(f"  {k:>3} open : {hist[k]:>12} columns "
              f"({100*hist[k]/hist.sum():.4f}%)")
print(f"  total columns: {hist.sum()}")
