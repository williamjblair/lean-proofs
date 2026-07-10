"""T2 second pass — cross-survivor statistics in the u-coordinate.

For each of the 45 banked survivors:
  u = lambda*d - A, w = d - u  (so A = q*d + w = lambda*d - u)
  ROW_lam(t) <=> (A+t) | prod_s (u + lambda*s - (lambda+1)*t)
  ROW_q(t)   <=> (A+t) | prod_s (q*s - w - (q+1)*t)
Stats: largest prime of A+t and which small affine term it divides;
u mod lambda, w mod q; how M splits across affine terms; whether
M = product of exactly 2 or 3 'aligned' divisors.
"""
import json
import os
import sys
from math import gcd

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import factorize

ART = "/Users/williamblair/personal/lean-proofs/compute/artifacts"
OUT = os.path.join(ART, "structure_hunt")


def main():
    surv = json.load(open(os.path.join(ART, "constant_prefix3_survivors.json")))
    lines = []
    for s in surv["survivors"]:
        k, q, d, A = s["k"], s["q"], s["d"], s["A"]
        lam = q + 1
        u = lam * d - A
        w = d - u
        lines.append(f"k={k} d={d} A={A} u={u} w={w} u/d={u/d:.4f} "
                     f"u%lam={u % lam} w%q={w % q} "
                     f"A%lam={A % lam} A%q={A % q}")
        for t in range(3):
            M = A + t
            terms = [u + lam * s - (lam + 1) * t for s in range(k)]
            gs = [gcd(M, x) for x in terms]
            fM = factorize(M)
            P = fM[-1][0]
            # which affine terms the biggest prime divides
            hits = [s_i for s_i, x in enumerate(terms) if x % P == 0]
            cover = []
            rem = M
            for s_i, g in sorted(enumerate(gs), key=lambda z: -z[1]):
                if rem == 1:
                    break
                gg = gcd(rem, g)
                if gg > 1:
                    cover.append((s_i, gg))
                    rem //= gg
            lines.append(
                f"  t={t} M={M} P(M)={P} P-hits-affine-terms={hits} "
                f"affine gcds>{1}: "
                + " ".join(f"s={i}:{g}" for i, g in enumerate(gs) if g > 1)
                + f"  greedy-cover={cover} rem={rem}")
    path = os.path.join(OUT, "t2_u_coordinate_stats.txt")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines[:40]))
    print(f"... wrote {path}")


if __name__ == "__main__":
    main()
