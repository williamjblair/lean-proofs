import sys
from math import gcd
from sympy import factorint, isprime
a = int(sys.argv[1]); B = int(sys.argv[2])
print(f"a   = {a} = {factorint(a)}")
print(f"a+1 = {a+1} = {factorint(a+1)}")
print(f"a+2 = {a+2} = {factorint(a+2)}")
P = a*(a+1)*(a+2)
open_rows = []
for b in range(3, B+1, 2):
    if gcd(b, P) != 1: continue
    if isprime(b) and (isprime(a) or isprime(a+2)): continue
    open_rows.append(b)
print(f"\nrows b <= {B} open for the hop a -> a+2: {len(open_rows)}")
print(open_rows[:40])
print("\nleast prime factor of each open row:",
      [min(factorint(b)) for b in open_rows[:40]])
# which primes kill everything
pf = set(factorint(a)) | set(factorint(a+1)) | set(factorint(a+2))
print(f"\nprimes dividing a(a+1)(a+2): {sorted(p for p in pf if p < 200)} ... "
      f"(and larger: {sorted(p for p in pf if p >= 200)})")
