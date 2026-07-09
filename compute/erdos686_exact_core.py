"""Shared exact-integer core for the Erdos #686 certificate regeneration.

Everything in this module is exact: Python ints and fractions.Fraction only.
No floats appear anywhere in decision logic.

Definitions (k, n, d natural numbers unless stated):

  Gap-solution ratio window (n-form):
      (n+d+k)^k <= 4*(n+k)^k   and   4*(n+1)^k <= (n+d+1)^k
  With A = n+1 the same window in (A,d,k)-form:
      (A+d+k-1)^k <= 4*(A+k-1)^k   and   4*A^k <= (A+d)^k

  shiftedDiffProductAt(k,d,j) = prod_{i=1..k} (d+i-j)   [nat subtraction]
  residualRowPoly(k,q,r)      = prod_{s=0..k-1} (q*s - r)          [signed]
  affineResidualPoly(k,q,u,t) = prod_{s=0..k-1} (u + (q+1)*s - (q+2)*t)
  liftedAffineResidualPoly(k,q,u,t,M)
                              = prod_{s=0..k-1} (q*(u + (q+1)*s - (q+2)*t) - M)

Key per-factor identity (verified by verify_per_factor_identity below):
  with A = (q+1)*d - u and M = A + t,
      (q+1)*(q*s - (d-u+(q+1)*t)) == q*(u + (q+1)*s - (q+2)*t) - M
so, taking products over s = 0..k-1,
      (q+1)^k * residualRowPoly(k,q,d-u+(q+1)*t)
          == liftedAffineResidualPoly(k,q,u,t,M)
and modulo M the lifted poly is congruent to q^k * affineResidualPoly(k,q,u,t).
"""

from fractions import Fraction


# ---------------------------------------------------------------------------
# polynomials / products
# ---------------------------------------------------------------------------

def shifted_diff_product_at(k: int, d: int, j: int) -> int:
    """prod_{i=1..k} (d+i-j) with natural (truncated) subtraction."""
    out = 1
    for i in range(1, k + 1):
        term = d + i - j
        if term < 0:
            term = 0  # ℕ subtraction truncates at zero
        out *= term
    return out


def residual_row_poly(k: int, q: int, r: int) -> int:
    """prod_{s=0..k-1} (q*s - r), signed integer."""
    out = 1
    for s in range(k):
        out *= q * s - r
    return out


def affine_residual_poly(k: int, q: int, u: int, t: int) -> int:
    """prod_{s=0..k-1} (u + (q+1)*s - (q+2)*t), signed integer."""
    out = 1
    for s in range(k):
        out *= u + (q + 1) * s - (q + 2) * t
    return out


def lifted_affine_residual_poly(k: int, q: int, u: int, t: int, M: int) -> int:
    """prod_{s=0..k-1} (q*(u + (q+1)*s - (q+2)*t) - M), signed integer."""
    out = 1
    for s in range(k):
        out *= q * (u + (q + 1) * s - (q + 2) * t) - M
    return out


# ---------------------------------------------------------------------------
# ratio window predicates
# ---------------------------------------------------------------------------

def window_n(k: int, n: int, d: int) -> bool:
    """Exact ratio window in n-form."""
    return ((n + d + k) ** k <= 4 * (n + k) ** k
            and 4 * (n + 1) ** k <= (n + d + 1) ** k)


def window_upper_A(k: int, A: int, d: int) -> bool:
    """(A+d+k-1)^k <= 4*(A+k-1)^k  (true for A large; monotone in A)."""
    return (A + d + k - 1) ** k <= 4 * (A + k - 1) ** k


def window_lower_A(k: int, A: int, d: int) -> bool:
    """4*A^k <= (A+d)^k  (true for A small; monotone in A)."""
    return 4 * A ** k <= (A + d) ** k


def window_A(k: int, A: int, d: int) -> bool:
    return window_upper_A(k, A, d) and window_lower_A(k, A, d)


# ---------------------------------------------------------------------------
# exact interval extraction via monotone bisection
# ---------------------------------------------------------------------------

def _first_true(pred, lo: int, hi: int) -> int:
    """Smallest x in [lo,hi] with pred(x).  Requires pred(hi) True and pred
    monotone (False..False True..True).  Exact integer bisection."""
    if pred(lo):
        return lo
    # invariant: pred(lo) False, pred(hi) True
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if pred(mid):
            hi = mid
        else:
            lo = mid
    return hi


def _last_true(pred, lo: int, hi: int) -> int:
    """Largest x in [lo,hi] with pred(x).  Requires pred(lo) True and pred
    monotone (True..True False..False)."""
    if pred(hi):
        return hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if pred(mid):
            lo = mid
        else:
            hi = mid
    return lo


def A_window_interval(k: int, d: int, A_floor: int = 2):
    """Exact interval [A_min, A_max] of A >= A_floor satisfying both window
    inequalities in (A,d,k)-form, or None if empty.

    window_upper_A is monotone increasing (once true, stays true as A grows);
    window_lower_A is monotone decreasing (once false, stays false).
    """
    hi = 20 * d + 4 * k + 16  # safe: A <= d/(4^(1/k)-1) < 11*d for k <= 15
    if not window_upper_A(k, hi, d):
        raise AssertionError(f"upper-window search cap too small k={k} d={d}")
    A_min = _first_true(lambda A: window_upper_A(k, A, d), A_floor, hi)
    if not window_lower_A(k, A_floor, d):
        return None
    A_max = _last_true(lambda A: window_lower_A(k, A, d), A_floor, hi)
    if window_lower_A(k, hi, d):
        raise AssertionError(f"lower-window search cap too small k={k} d={d}")
    if A_min > A_max:
        return None
    return A_min, A_max


def n_window_interval(k: int, d: int, n_floor: int = 1):
    """Exact interval [n_min, n_max] of n >= n_floor satisfying the ratio
    window in n-form, or None if empty."""
    res = A_window_interval(k, d, A_floor=n_floor + 1)
    if res is None:
        return None
    A_min, A_max = res
    return A_min - 1, A_max - 1


# ---------------------------------------------------------------------------
# integer k-th roots and exact rational bounds on 1/(4^(1/k)-1)
# ---------------------------------------------------------------------------

def integer_kth_root(x: int, k: int) -> int:
    """Largest r >= 0 with r^k <= x.  Exact Newton iteration on ints."""
    if x < 0:
        raise ValueError("negative radicand")
    if x in (0, 1):
        return x
    r = 1 << ((x.bit_length() + k - 1) // k)
    while True:
        nr = ((k - 1) * r + x // r ** (k - 1)) // k
        if nr >= r:
            break
        r = nr
    while r ** k > x:
        r -= 1
    while (r + 1) ** k <= x:
        r += 1
    return r


def fourth_root_bounds(k: int, scale_pow: int = 30):
    """Exact rational bracket of 4^(1/k):  r/S <= 4^(1/k) < (r+1)/S with
    S = 10^scale_pow.  Returns (r, S).  Both inequalities are certified by
    integer comparisons r^k <= 4*S^k < (r+1)^k."""
    S = 10 ** scale_pow
    r = integer_kth_root(4 * S ** k, k)
    assert r ** k <= 4 * S ** k < (r + 1) ** k
    return r, S


def c_bounds(k: int, scale_pow: int = 30):
    """Exact rational bracket (c2, c1) of c_k = 1/(4^(1/k)-1):
       c2 = S/(r+1-S) < c_k <= S/(r-S) = c1.
    Any window pair then satisfies  c2*d - (k-1) < A <= c1*d."""
    r, S = fourth_root_bounds(k, scale_pow)
    c1 = Fraction(S, r - S)
    c2 = Fraction(S, r + 1 - S)
    assert c2 < c1
    return c2, c1, r, S


# ---------------------------------------------------------------------------
# factorization helpers (arguments here are small, trial division suffices)
# ---------------------------------------------------------------------------

def factorize(m: int):
    """Exact prime factorization of m >= 1 by trial division.
    Returns sorted list of (p, e)."""
    if m < 1:
        raise ValueError("factorize expects m >= 1")
    out = []
    p = 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            out.append((p, e))
        p += 1 if p == 2 else 2
    if m > 1:
        out.append((m, 1))
    return out


def padic_valuation(x: int, p: int):
    """v_p(|x|) for x != 0; returns None (infinite) for x == 0."""
    if x == 0:
        return None
    x = abs(x)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


# ---------------------------------------------------------------------------
# the per-factor sanity identity
# ---------------------------------------------------------------------------

def per_factor_identity_holds(q: int, s: int, d: int, u: int, t: int) -> bool:
    """(q+1)*(q*s - (d-u+(q+1)*t)) == q*(u+(q+1)*s-(q+2)*t) - ((q+1)*d - u + t)
    with all quantities signed integers (no truncation)."""
    lhs = (q + 1) * (q * s - (d - u + (q + 1) * t))
    rhs = q * (u + (q + 1) * s - (q + 2) * t) - ((q + 1) * d - u + t)
    return lhs == rhs


def verify_per_factor_identity() -> bool:
    """Both sides are polynomials of degree <= 2 in q and degree <= 1 in each
    of s, d, u, t.  Agreement on a 4 x 3 x 3 x 3 x 3 integer grid (4 > 2+1
    values of q, 3 > 1+1 values of the others) proves the polynomial identity.
    A large-value spot check is added for good measure."""
    for q in range(4):
        for s in range(3):
            for d in range(3):
                for u in range(3):
                    for t in range(3):
                        if not per_factor_identity_holds(q, s, d, u, t):
                            return False
    big = [10 ** 12 + 7, 3 ** 40, 2 ** 61 - 1]
    for q in (6, 10 ** 9 + 7):
        for s, d, u, t in [(big[0], big[1], big[2], 12345),
                           (7, big[2], big[0], big[1])]:
            if not per_factor_identity_holds(q, s, d, u, t):
                return False
    return True


def verify_lifted_product_identity(k: int, q: int, d: int, u: int, t: int) -> bool:
    """(q+1)^k * residualRowPoly(k,q,d-u+(q+1)t) == liftedAffineResidualPoly
    with M = (q+1)*d - u + t.  Consequence of the per-factor identity."""
    M = (q + 1) * d - u + t
    lhs = (q + 1) ** k * residual_row_poly(k, q, d - u + (q + 1) * t)
    rhs = lifted_affine_residual_poly(k, q, u, t, M)
    return lhs == rhs


# constant-quotient (k,q) table and prefix-three enumeration bounds
CONSTANT_KQ_TABLE = [(5, 3), (6, 3), (7, 4), (8, 5), (9, 6), (10, 6),
                     (11, 7), (12, 8), (13, 8), (14, 9), (15, 10)]

CONSTANT_PREFIX_THREE_BOUND = {
    (5, 3): 220, (6, 3): 220, (7, 4): 220, (8, 5): 220, (9, 6): 220,
    (10, 6): 266, (11, 7): 7029, (12, 8): 2695, (13, 8): 4467,
    (14, 9): 2811, (15, 10): 2915,
}


if __name__ == "__main__":
    assert verify_per_factor_identity(), "per-factor identity FAILED"
    # lifted product identity spot checks
    for (k, q) in CONSTANT_KQ_TABLE:
        for d in (221, 1000):
            for u in (0, 5, d - 1):
                for t in (0, 1, 2, 3):
                    assert verify_lifted_product_identity(k, q, d, u, t)
    # window interval sanity: brute force comparison on a small box
    for k in (5, 9, 15):
        for d in (221, 300):
            iv = A_window_interval(k, d)
            brute = [A for A in range(2, 20 * d) if window_A(k, A, d)]
            if iv is None:
                assert brute == []
            else:
                assert brute == list(range(iv[0], iv[1] + 1))
    # integer k-th root sanity
    for x in (0, 1, 2, 63, 64, 65, 10 ** 30, 4 * 10 ** 90):
        for k in (2, 3, 11, 15):
            r = integer_kth_root(x, k)
            assert r ** k <= x < (r + 1) ** k
    print("erdos686_exact_core self-tests PASS")
