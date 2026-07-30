"""Independent re-check of witness_path.txt straight from the definition of G."""
import sys
from math import gcd, isqrt

pts = []
for ln in open(sys.argv[1] if len(sys.argv) > 1 else "witness_path.txt"):
    if ln.startswith("#"):
        continue
    x, y = ln.split()
    pts.append((int(x), int(y)))

N = max(max(p) for p in pts)
sieve = bytearray([1]) * (N + 1)
sieve[0] = sieve[1] = 0
for i in range(2, isqrt(N) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))

bad_v = [p for p in pts
         if not (gcd(p[0], p[1]) == 1 and min(p) > 1
                 and ((p[0] >= 4 and not sieve[p[0]]) or
                      (p[1] >= 4 and not sieve[p[1]])))]
bad_e = [(u, v) for u, v in zip(pts, pts[1:])
         if abs(u[0] - v[0]) + abs(u[1] - v[1]) != 1]
dup = len(pts) - len(set(pts))
print(f"vertices={len(pts)} duplicates={dup} bad_vertices={len(bad_v)} "
      f"bad_steps={len(bad_e)}")
print(f"x from {pts[0][0]} to {max(p[0] for p in pts)}; "
      f"y in [{min(p[1] for p in pts)},{max(p[1] for p in pts)}]")
print("VERIFIED" if not (bad_v or bad_e or dup) else "FAILED")
