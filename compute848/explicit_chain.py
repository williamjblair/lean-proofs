"""Explicit error-chain recomputation for Sothanaphan, "An Explicit Threshold in
Erdos Problem #848" (Mar 24 preprint).

All arithmetic is exact (Fraction / int); mpmath is used only to produce
*certified upper bounds* on logarithms, which is the direction we need since
every log appears with a positive coefficient in an upper bound.

Structure:
  * E_q0(N)  -- Section 2 display defining kappa_{q0} (lam < 6.876, a25=25/8, a100=7/2)
  * dens_err(N,q,pell_factor) -- Corollary 2 density error, R = ceil((259/200) N^{2/3})
  * total(N, pell_factor) = dens_err + 2*E_25(N)*N^{-1/4}
  * slack = 1/25 - (23/25) Cquad - (2/25) C_{2,5}
"""

from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 120
EPS = F(1, 10**60)  # safety pad on every mpmath-derived bound


def _up(x) -> F:
    """Certified upper bound (as an exact Fraction) on the mpf value x."""
    f = F(mp.nstr(x, 60, strip_zeros=False))
    return f * (1 + EPS) + EPS


def _dn(x) -> F:
    f = F(mp.nstr(x, 60, strip_zeros=False))
    return f * (1 - EPS) - EPS


def log_up(n) -> F:
    """Upper bound on log(n)."""
    return _up(mp.log(mp.mpf(int(n))) if isinstance(n, int) else mp.log(mp.mpf(str(n))))


def ipow_root_up(N: int, num: int, den: int) -> F:
    """Upper bound on N^(num/den)."""
    return _up(mp.power(mp.mpf(N), mp.mpf(num) / mp.mpf(den)))


def ipow_root_dn(N: int, num: int, den: int) -> F:
    return _dn(mp.power(mp.mpf(N), mp.mpf(num) / mp.mpf(den)))


# ---------------------------------------------------------------- constants
LAM = F(6876, 1000)          # lambda < 6.876
ALPHA = {25: F(25, 8), 100: F(7, 2)}
CQUAD_UP = F(2734669, 10**8)  # Lemma 2: Cquad < 0.02734669


def c25_up() -> F:
    """Upper bound on C_{2,5} = 1 - 25/(3 pi^2)."""
    return 1 - _dn(mp.mpf(25) / (3 * mp.pi**2))


SLACK = F(1, 25) - F(23, 25) * CQUAD_UP - F(2, 25) * c25_up()


# ---------------------------------------------------------------- E_q0(N)
def E(q0: int, N: int) -> F:
    """Section 2 display: kappa_{q0} admissible value at N (an upper bound)."""
    a = ALPHA[q0]
    N34 = ipow_root_dn(N, 3, 4)     # divide by -> use lower bound
    N32 = ipow_root_dn(N, 3, 2)
    N54 = ipow_root_dn(N, 5, 4)
    q14 = ipow_root_up(q0, 1, 4)
    q54 = ipow_root_up(q0, 5, 4)
    q12 = ipow_root_dn(q0, 1, 2)
    q38 = ipow_root_dn(q0, 3, 8)
    X = F(N, q0) + 1                # X <= N/q0 + 1
    return (F(2367, 1000) / N34
            + a
            + 1 / N34
            + X / (a * N32)
            + 1 / (a * q12 * N32)
            + 2 * LAM * q14 * X / (a * N54)
            + 2 * LAM / (a * q38 * N32)
            + LAM * q54 * X / (a * a * F(N))
            + LAM * q14 / (a * a * F(N) ** 2))


# ---------------------------------------------------------------- Corollary 2
def R_of(N: int) -> int:
    """R = ceil((259/200) N^{2/3}), exact: least R with (200R)^3 >= 259^3 N^2."""
    tgt = 259**3 * N * N
    lo, hi = 1, int(mp.floor(mp.power(mp.mpf(N), mp.mpf(2) / 3) * mp.mpf("1.3"))) + 10
    while lo < hi:
        mid = (lo + hi) // 2
        if (200 * mid) ** 3 >= tgt:
            hi = mid
        else:
            lo = mid + 1
    return lo


LOG_BASE = None  # lower bound on log(2+sqrt(3))


def _init_base():
    global LOG_BASE
    LOG_BASE = _dn(mp.log(2 + mp.sqrt(3)))


_init_base()


def dens_terms(N: int, q: int):
    """The three Corollary-2 per-class terms (upper bounds), unweighted."""
    R = R_of(N)
    lR = log_up(R)
    lN = log_up(N)
    t1 = F(R) * (1 + lR) / F(N)
    t2 = 2 * (F(N, q) + 1) * (lR + 2) / (F(N) * F(R))
    t3 = (F(N) ** 2 + 1) * (1 + lN / LOG_BASE) / (F(N) * F(R) ** 2)
    return t1, t2, t3


def dens_err(N: int, q: int, pell_factor: int = 23) -> F:
    t1, t2, t3 = dens_terms(N, q)
    return 23 * (t1 + t2) + pell_factor * t3


def kappa_term(N: int) -> F:
    """2 * kappa_25(N) * N^{-1/4}."""
    return 2 * E(25, N) / ipow_root_dn(N, 1, 4)


def total(N: int, pell_factor: int = 23) -> F:
    # q=25 is the worse (larger) of q in {25,50}
    return max(dens_err(N, q, pell_factor) for q in (25, 50)) + kappa_term(N)


def fmt(x: F, sig=6) -> str:
    return mp.nstr(mp.mpf(x.numerator) / mp.mpf(x.denominator), sig)


def minimal_N0(pell_factor: int) -> int:
    lo, hi = 10**9, 10**19
    assert total(hi, pell_factor) < SLACK
    while lo < hi:
        mid = (lo + hi) // 2
        if total(mid, pell_factor) < SLACK:
            hi = mid
        else:
            lo = mid + 1
    return lo


if __name__ == "__main__":
    NP = 264 * 10**15  # 2.64e17

    print("=== constants ===")
    print("C_{2,5} <=", fmt(c25_up(), 12))
    print("slack    =", fmt(SLACK, 8))
    print()

    print("=== GATE 1: kappa_q0 (Section 2) at N = 2.64e17 ===")
    print("E_25  =", fmt(E(25, NP), 8), " (paper: < 4.700)")
    print("E_100 =", fmt(E(100, NP), 8), " (paper: < 5.275)")
    print()

    print("=== GATE 2: Corollary 2 at N = 2.64e17 ===")
    print("R =", R_of(NP))
    for q in (25, 50):
        t1, t2, t3 = dens_terms(NP, q)
        s = t1 + t2 + t3
        print(f" q={q}: t1={fmt(t1)} t2={fmt(t2)} t3={fmt(t3)}  per-class={fmt(s)}"
              f"   23x = {fmt(23*s)}")
    print(" paper: per-class < 8.577e-5, total < 1.973e-3")
    print()

    print("=== table: total error (density + 2*kappa25*N^-1/4) ===")
    print(f"{'N':>12} {'23x total':>14} {'1x total':>14} {'kappa term':>14} "
          f"{'23*t1':>13} {'t3(1x)':>13}")
    Ns = [10**k for k in range(10, 17)] + [NP]
    for N in Ns:
        t1, t2, t3 = dens_terms(N, 25)
        print(f"{mp.nstr(mp.mpf(N),3):>12} {fmt(total(N,23)):>14} {fmt(total(N,1)):>14} "
              f"{fmt(kappa_term(N)):>14} {fmt(23*t1):>13} {fmt(t3):>13}")
    print("slack =", fmt(SLACK, 8))
    print()

    for pf in (23, 1):
        N0 = minimal_N0(pf)
        t1, t2, t3 = dens_terms(N0, 25)
        print(f"minimal N0 (pell factor {pf}) = {N0}  ~ {mp.nstr(mp.mpf(N0),4)}")
        print(f"   at N0: total={fmt(total(N0,pf))} slack={fmt(SLACK)} | "
              f"23*t1={fmt(23*t1)} 23*t2={fmt(23*t2)} "
              f"pell={fmt(pf*t3)} kappa={fmt(kappa_term(N0))}")
        print(f"   monotone check total(N0-1)={fmt(total(N0-1,pf))} >= slack:",
              total(N0 - 1, pf) >= SLACK)
