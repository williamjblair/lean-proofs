"""Exceptional-nine box scan (Erdos #686, N = 4 branch, k = 9).

Closes the k = 9, row-1-quotient-5 branch: a hypothetical N = 4 gap solution
with k = 9, d >= 221, exact ratio window

    (n+d+9)^9 <= 4*(n+9)^9        (hup)
    4*(n+1)^9 <= (n+d+1)^9        (hlo)

and (n+1) // d = 5, i.e. n+1 = 6d - u with u = 6d - (n+1) in [1, d].

Step 1 (exact linearization, mirrors the Lean derivation):
  Rational bracket for 4^(1/9):  B = 10^6, A = 1166530, certified by the
  integer inequality  4*B^9 < A^9  (and A is minimal: 4*B^9 >= (A-1)^9).
  `ratio_window_linearize_of_pow_bracket` turns hup into
      B*(n+d+9) < A*(n+9).
  Substituting n+1 = 6d - u and rearranging over the integers:
      (A-B)*u + (7B-6A)*d < 8*(A-B),   with 7B-6A = 820 > 0.
  With u >= 1:      820*d < 7*(A-B)             =>  d <= D = 1421.
  With d >= 221:    (A-B)*u < 8*(A-B) - 221*820 =>  u <= U = 6.

Step 2 (this scan): for every point of the box d in [221, D], u in [1, U],
n = 6d - u - 1, check the exact window (both inequalities, exact integers)
and, for each window-passing point, find the smallest j in [1, 9] with

    not (n+j) | shiftedDiffProductAt(9, d, j) = prod_{i=1..9} (d+i-j).

Every window point must fail some row j (else: counterexample-adjacent, abort
loudly).  Records the first-failing-j histogram; the Lean kernel certificate
`k_nine_q5_box_cert` in ErdosProblems/Erdos686ExceptionalNine.lean decides the
same box exhaustively.

All arithmetic is exact integer arithmetic; no floats.
"""

K = 9
N = 4

# ---------------------------------------------------------------------------
# Step 1: bracket and exact bounds
# ---------------------------------------------------------------------------

B = 10**6
A = 1166530

assert N * B**K < A**K, "bracket 4*B^9 < A^9 fails"
assert not (N * B**K < (A - 1) ** K), "A is not minimal for this B"

AB = A - B          # 166530
EPS = 7 * B - 6 * A  # 820
assert EPS > 0

# (A-B)*u + EPS*d < 8*(A-B); strict integer inequalities:
D = (7 * AB - 1) // EPS            # u >= 1  =>  d <= D
U = (8 * AB - 221 * EPS - 1) // AB  # d >= 221  =>  u <= U
assert D == 1421 and U == 6, (D, U)

D_MIN = 221


def shifted_diff_product_at(k, d, j):
    """prod_{i=1..k} (d+i-j)  (all factors positive for d >= 221, i,j <= 9)."""
    p = 1
    for i in range(1, k + 1):
        assert d + i - j > 0
        p *= d + i - j
    return p


def window(n, d):
    hup = (n + d + K) ** K <= N * (n + K) ** K
    hlo = N * (n + 1) ** K <= (n + d + 1) ** K
    return hup, hlo


def main():
    total = 0
    passing = 0
    hist = {}
    max_first_j = 0
    for d in range(D_MIN, D + 1):
        for u in range(1, U + 1):
            n = 6 * d - u - 1
            total += 1
            # consistency: (n+1) // d == 5 and u == 6d - (n+1)
            assert (n + 1) // d == 5
            assert 6 * d - (n + 1) == u
            hup, hlo = window(n, d)
            if not (hup and hlo):
                continue
            passing += 1
            # linearized inequality must hold (sanity for the Lean route)
            assert B * (n + d + K) < A * (n + K)
            first_j = None
            for j in range(1, K + 1):
                if shifted_diff_product_at(K, d, j) % (n + j) != 0:
                    first_j = j
                    break
            if first_j is None:
                raise SystemExit(
                    f"!!! NO ROW ESCAPE at d={d}, u={u}, n={n} — "
                    "window point satisfies ALL row divisibilities "
                    "(counterexample-adjacent event, STOP)"
                )
            hist[first_j] = hist.get(first_j, 0) + 1
            max_first_j = max(max_first_j, first_j)

    print(f"box: d in [{D_MIN}, {D}], u in [1, {U}]  ({total} points)")
    print(f"window-passing points: {passing}")
    print(f"first-failing-j histogram: {dict(sorted(hist.items()))}")
    print(f"max first-failing j: {max_first_j}")
    print("OK: every window point escapes some row j in [1, 9]")


if __name__ == "__main__":
    main()
