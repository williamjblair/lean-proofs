import numpy as np

XMAX = 10**7
H = 20
N = XMAX + H + 1

# sieve phi
phi = np.arange(N, dtype=np.int64)
for p in range(2, N):
    if phi[p] == p:  # p prime
        phi[p::p] -= phi[p::p] // p

print("phi sieve done. spot checks:", phi[1], phi[10], phi[5186], phi[5187], phi[5188])

# collision counts P(x;h) = #{m <= x : phi(m)=phi(m+h)}
for x in (10**6, 10**7):
    print(f"\nx = {x}")
    for h in range(1, H+1):
        cnt = int(np.count_nonzero(phi[1:x+1] == phi[1+h:x+1+h]))
        print(f"  h={h:2d}  P(x;h)={cnt}")

# longest window of pairwise-distinct phi values within [1, 10^7]
# classic sliding window (longest run of consecutive integers with distinct phi)
last = {}
start = 1
best = 0; bestn = 1
for m in range(1, XMAX+1):
    v = int(phi[m])
    if v in last and last[v] >= start:
        start = last[v] + 1
    last[v] = m
    if m - start + 1 > best:
        best = m - start + 1; bestn = start
print(f"\nlongest pairwise-distinct-phi run in [1,1e7]: length {best} starting at n+1={bestn}")
import math
lg = math.log(XMAX)
print(f"log x = {lg:.3f}, (log x)^2 = {lg*lg:.1f}, (log x)^3 = {lg**3:.0f}")
