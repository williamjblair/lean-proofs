"""Standalone re-verification of a trajectory file against the raw problem
statement.  Reads only the file; recomputes primality independently."""
import sys
from math import gcd
from sympy import isprime

pts = []
for line in open(sys.argv[1]):
    if line.startswith('#'):
        continue
    x, y = line.split()
    pts.append((int(x), int(y)))

bad = 0
for x, y in pts:
    if gcd(x, y) != 1:                      bad += 1; print("gcd", x, y)
    if min(x, y) <= 1:                      bad += 1; print("min", x, y)
    if isprime(x) and isprime(y):           bad += 1; print("both prime", x, y)
for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
    if abs(x1-x2) + abs(y1-y2) != 1:        bad += 1; print("step", x1,y1,x2,y2)
if len(set(pts)) != len(pts):               bad += 1; print("repeated vertex")
xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
print(f"{len(pts)} vertices, x {min(xs)}..{max(xs)}, y {min(ys)}..{max(ys)}, "
      f"violations = {bad}")
