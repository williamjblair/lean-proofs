"""Measurement 3 (global): is a Wall-Lemma column ever within reach?

For band [3,Y] and every odd column a in a range, count the OPEN rows

    open(a,Y) = #{ b odd, 3<=b<=Y : (a,b) and (a+2,b) are vertices of H
                                    and gcd(a+1,b)=1 }

A Wall-Lemma column is exactly open(a,Y) = 0.  We report min, the histogram
of the smallest values, and the column achieving the min.

Also prints the CRT modulus that a wall column must satisfy, which bounds how
far the first wall can be:
  * if a and a+2 are both composite, every odd prime p <= Y must divide
    a(a+1)(a+2)  (prime rows b=p are otherwise open), so
    a(a+1)(a+2) >= prod_{3<=p<=Y} p = exp(theta(Y)) and a >~ exp(theta(Y)/3).
  * if a or a+2 is prime, all prime rows die for free and it is enough that
    every odd prime p <= sqrt(Y) divides a(a+1)(a+2)  (every odd composite
    b <= Y has a prime factor <= sqrt(Y)); modulus exp(theta(sqrt(Y))).
"""
import sys
from math import log, exp
import numpy as np
from hub import prime_mask, Builder

Y = int(sys.argv[1])
A0 = int(sys.argv[2]) if len(sys.argv) > 2 else 3
A1 = int(sys.argv[3]) if len(sys.argv) > 3 else 10_000_001
CH = 200_000

pr = prime_mask(A1 + 8)
B = Builder(Y, pr)
nb = B.nb

best = (10 ** 9, 0)
hist = np.zeros(64, dtype=np.int64)
tot = 0
a = A0 + (A0 % 2 == 0)
while a < A1:
    na = min(CH, (A1 - a) // 2 + 1)
    aa, V, Hm, Vm = B.build(a, na, nb=nb)
    cnt = Hm.sum(axis=0, dtype=np.int32)
    cnt = cnt[:-1]                      # last column's H-edge is truncated
    m = int(cnt.min())
    if m < best[0]:
        best = (m, int(aa[int(cnt.argmin())]))
    np.add.at(hist, np.minimum(cnt, 63), 1)
    tot += cnt.size
    a = int(aa[-1])

theta = lambda x: sum(log(p) for p in range(3, int(x) + 1) if pr[p])
tY, tS = theta(Y), theta(Y ** 0.5)
print(f"band Y={Y}   columns scanned: {tot}  (a in [{A0},{A1}])")
print(f"  min open(a,Y) = {best[0]}  at a = {best[1]}")
print(f"  histogram of open counts 0..15: {list(hist[:16])}")
print(f"  columns with open <= 40: {int(hist[:41].sum())}")
print(f"  theta(Y)={tY:.1f} -> both-composite wall needs a >~ 10^{tY/3/log(10):.1f}")
print(f"  theta(sqrt(Y))={tS:.1f} -> prime-neighbour wall modulus 10^{tS/log(10):.1f}"
      f", so density ~ 3^{len([p for p in range(3,int(Y**0.5)+1) if pr[p]])}"
      f"/10^{tS/log(10):.1f}")
