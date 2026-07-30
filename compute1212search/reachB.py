import sys
from windowed import sweep
B = int(sys.argv[1]); A = int(sys.argv[2]); W = int(sys.argv[3])
a, rows, _ = sweep(B, A, 1065, [917], W=W)
print(f"RESULT B={B} W={W}: reach a={a}")
