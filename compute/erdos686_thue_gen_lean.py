#!/usr/bin/env python3
"""
Erdos 686, odd k, N = 4: generator + exact verifier for the Farey/Stern-Brocot
descent certificate consumed by ErdosProblems/Erdos686ConvergentMachinery.lean
(`FareyTree` / `fareyCheck`), instantiated for k in {5, 7, 9, 11, 13, 15}.

Mathematical shape (all integer arithmetic, no reals anywhere):

  A solution of (n+d+1)...(n+d+k) = 4 (n+1)...(n+k) in centered coordinates
  X = n+d+h, Y = n+h (h = (k+1)/2) satisfies the exact Thue window (proved in
  the per-k instance module Erdos686<K>Thue.lean from the equation + the
  banked ratio window)

      CDEN * |X^K - N*Y^K| <= CNUM * Y^(K-2),     K = k, N = 4,

  valid for Y >= YLO (from d >= 221 via the banked confinement
  q*d <= n+1 < q'*d).  The descent walks the Stern-Brocot tree from the root
  Farey pair a/b < 4^(1/k) < c/d (det c*b - a*d = 1).  Every node of the
  certificate tree is one of

    .high            b + d > Ymax: mediant lemma forces Y >= b+d > Ymax;
    .kill            one endpoint's k-th-power side certificate contradicts
                     strict betweenness once Y >= L = max(b+d, YLO):
                       CNUM * v^K < CDEN * |u^K - N v^K| * L^2;
    .node gmax l r   split at the mediant (A,B) = (a+c, b+d); the exact
                     multiple bound CNUM * B^(K-2) < CDEN * (gmax+1)^2 * D,
                     D = |A^K - N B^K|, confines the equality case X/Y = A/B
                     to (X,Y) = g*(A,B) with g <= gmax; every such candidate
                     is refuted by the exact centered equation.

  This mirrors `fareyCheck` in Lean bit for bit; every Boolean the Lean
  kernel will decide is asserted here first.

Determinism: pure integer arithmetic, no sets/dicts iterated, no floats.
Output is byte-stable for a fixed (k, exponent) configuration.

Usage:  python3 compute/erdos686_thue_gen_lean.py [YMAX_EXP] [K]
        YMAX_EXP defaults to 60, K defaults to 5;
        Ymax = QHI * 10^YMAX_EXP (covers d < 10^YMAX_EXP via
        Y = n+h < QHI*d + h - 1, QHI from the banked upper confinement).
        Writes the Lean certificate fragment to
        compute/artifacts/erdos686_k<K>_farey_cert_e<EXP>.lean and prints stats.
"""

import sys
from fractions import Fraction

sys.setrecursionlimit(4_000_000)

# ------------------------------------------------------------- per-k configs
#
# Shared fields:
#   K       block width k (odd); E = K - 2 is the machinery parameter e
#   CNUM/CDEN   certified Thue window |X^K - 4 Y^K| <= (CNUM/CDEN) Y^(K-2)
#   YLO     lower Y bound from the banked handoff (Y = n+h >= QLO*221 + h-1)
#   QLO/QHI banked row-1 confinement quotients: QLO*d <= n+1 < QHI*d (d >= 221)
#   ROOT    Farey pair a/b < 4^(1/k) < c/d with c*b = a*d + 1
#   eq      the exact centered equation, in the same N-safe arrangement as the
#           Lean instance module (P_k(X) = 4 P_k(Y) at X = n+d+h, Y = n+h)
#
# k >= 7 fields (banked-window bracket route; k = 5 keeps its own constants):
#   ALO/CHI  power bracket at scale S = 10^5: ALO^k < 4*S^k < CHI^k
#   SLO/SHI  offset-absorbed scaled bracket: SLO*Y < S*X < SHI*Y for Y >= YLO
#   ES       elementary symmetric functions of {1,4,...,((k-1)/2)^2}
#            (P_k(T) = T^k + sum_i (-1)^i ES[i-1] T^(k-2i))
#   TELESCOPE  the d=1 telescope (Y,X) of the raw centered equation, if any
#            (k = 9: (7,8); k = 15: (12,13)); must satisfy eq and lie < YLO.

CONFIGS = {
    5: dict(
        K=5, CNUM=44, CDEN=5, YLO=665, QLO=3, QHI=4, ROOT=(1, 1, 4, 3),
        eq=lambda X, Y: X**5 + 4 * X + 20 * Y**3 == 4 * Y**5 + 16 * Y + 5 * X**3,
        ES=[5, 4], ALO=None, CHI=None, SLO=None, SHI=None, TELESCOPE=None,
    ),
    7: dict(
        K=7, CNUM=93, CDEN=5, YLO=887, QLO=4, QHI=5, ROOT=(1, 1, 5, 4),
        eq=lambda X, Y: X**7 + 49 * X**3 + 56 * Y**5 + 144 * Y ==
            4 * Y**7 + 196 * Y**3 + 14 * X**5 + 36 * X,
        ES=[14, 49, 36], ALO=121901, CHI=121902, SLO=121826, SHI=121977,
        TELESCOPE=None,
    ),
    9: dict(
        K=9, CNUM=162, CDEN=5, YLO=1109, QLO=5, QHI=7, ROOT=(1, 1, 6, 5),
        eq=lambda X, Y: X**9 + 273 * X**5 + 576 * X + 120 * Y**7 + 3280 * Y**3 ==
            4 * Y**9 + 1092 * Y**5 + 2304 * Y + 30 * X**7 + 820 * X**3,
        ES=[30, 273, 820, 576], ALO=116652, CHI=116653, SLO=116591, SHI=116714,
        TELESCOPE=(7, 8),
    ),
    11: dict(
        K=11, CNUM=50, CDEN=1, YLO=1552, QLO=7, QHI=8, ROOT=(1, 1, 8, 7),
        eq=lambda X, Y: X**11 + 1023 * X**7 + 21076 * X**3 + 220 * Y**9 +
            30580 * Y**5 + 57600 * Y ==
            4 * Y**11 + 4092 * Y**7 + 84304 * Y**3 + 55 * X**9 +
            7645 * X**5 + 14400 * X,
        ES=[55, 1023, 7645, 21076, 14400], ALO=113431, CHI=113432,
        SLO=113387, SHI=113476, TELESCOPE=None,
    ),
    13: dict(
        K=13, CNUM=72, CDEN=1, YLO=1774, QLO=8, QHI=9, ROOT=(1, 1, 8, 7),
        eq=lambda X, Y: X**13 + 3003 * X**9 + 296296 * X**5 + 518400 * X +
            364 * Y**11 + 177892 * Y**7 + 3092544 * Y**3 ==
            4 * Y**13 + 12012 * Y**9 + 1185184 * Y**5 + 2073600 * Y +
            91 * X**11 + 44473 * X**7 + 773136 * X**3,
        ES=[91, 3003, 44473, 296296, 773136, 518400], ALO=111253, CHI=111254,
        SLO=111214, SHI=111293, TELESCOPE=None,
    ),
    15: dict(
        K=15, CNUM=97, CDEN=1, YLO=2217, QLO=10, QHI=11, ROOT=(1, 1, 11, 10),
        eq=lambda X, Y: X**15 + 7462 * X**11 + 2475473 * X**7 +
            38402064 * X**3 + 560 * Y**13 + 766480 * Y**9 +
            61166560 * Y**5 + 101606400 * Y ==
            4 * Y**15 + 29848 * Y**11 + 9901892 * Y**7 + 153608256 * Y**3 +
            140 * X**13 + 191620 * X**9 + 15291640 * X**5 + 25401600 * X,
        ES=[140, 7462, 191620, 2475473, 15291640, 38402064, 25401600],
        ALO=109682, CHI=109683, SLO=109651, SHI=109714, TELESCOPE=(12, 13),
    ),
}

CHUNK_DEPTH = 120              # hoist subtrees into named defs beyond this depth

# module-level instance parameters, set by main() from the chosen config
K = E = N = CNUM = CDEN = YLO = None
ROOT = None
CERT_NAME = None
eq_holds = None


# ------------------------------------------------------- sanity: Lean constants
def check_lean_constants_k5():
    """Assert every literal that appears in the hand-written Lean inequalities
    of Erdos686FiveThue.lean (bracket + Thue window derivation)."""
    # bracket certificates 131/100 < 4^(1/5) < 132/100
    assert 131**5 < 4 * 100**5 < 132**5
    # N_lo(Y) = 4e10*(Y^5-5Y^3+4Y) - ((131Y)^5 - 5e4(131Y)^3 + 4e8*131Y)
    assert 4 * 10**10 - 131**5 == 1_420_510_349
    assert 4 * 10**10 * 5 - 5 * 10**4 * 131**3 == 87_595_450_000
    assert 5 * 10**4 * 131**3 == 112_404_550_000
    assert 4 * 10**10 * 4 - 4 * 10**8 * 131 == 107_600_000_000
    # N_hi(Y) = (132Y)^5 - 5e4(132Y)^3 + 4e8*132Y - 4e10*(Y^5-5Y^3+4Y)
    assert 132**5 - 4 * 10**10 == 74_642_432
    assert 2 * 10**11 - 5 * 10**4 * 132**3 == 85_001_600_000
    assert 4 * 10**10 * 4 - 4 * 10**8 * 132 == 107_200_000_000
    # Thue window cross-multiplications (x40000 forms)
    assert 25 * 132**3 == 57_499_200 and 25 * 131**3 == 56_202_275
    assert 131**3 == 2_248_091 and 132**3 == 2_299_968
    # YLO consistency with d >= 221: Y = n+3 >= 3d+2
    assert 3 * 221 + 2 == YLO


def check_lean_constants_generic(cfg):
    """Assert every fact the hand-written Lean inequalities of the k >= 7
    instance modules rely on: the banked-window power brackets, the omega
    offset-absorption margins, the exact linarith feasibility of the
    two-sided Thue window, and the root-pair strict-enclosure margins."""
    k, h = cfg["K"], (cfg["K"] + 1) // 2
    S = 10**5
    ALO, CHI, SLO, SHI = cfg["ALO"], cfg["CHI"], cfg["SLO"], cfg["SHI"]
    ES, qlo, qhi = cfg["ES"], cfg["QLO"], cfg["QHI"]
    ylo, cnum, cden = cfg["YLO"], cfg["CNUM"], cfg["CDEN"]
    # centered-equation arrangement matches P_k(X) = 4 P_k(Y) coefficientwise:
    # spot-check the polynomial identity on a grid (exact integers)
    def P(T):
        v = T**k
        for i, e in enumerate(ES, start=1):
            v += (-1) ** i * e * T ** (k - 2 * i)
        return v
    for X in range(1, 40):
        for Y in range(1, 40):
            assert cfg["eq"](X, Y) == (P(X) == 4 * P(Y)), (k, X, Y)
    # ES really are the elementary symmetric functions of {1,4,...,m^2}
    m = (k - 1) // 2
    coeffs = [1]
    for j in range(1, m + 1):
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] += c
            new[i + 1] += c * j * j
        coeffs = new
    assert coeffs[1:] == ES, k
    # banked handoff: YLO = QLO*221 + h - 1, Ymax coefficient = QHI
    assert ylo == qlo * 221 + h - 1
    # power brackets at scale 10^5 (the two norm_num facts of the module)
    assert ALO**k < 4 * S**k < CHI**k and CHI == ALO + 1
    # omega absorption margins for the scaled bracket lemmas:
    #   lower: (ALO - SLO)*YLO >= (ALO - S)*(h-1)
    #   upper: (SHI - CHI)*YLO >= (CHI - S)*(h-1)
    assert (ALO - SLO) * ylo >= (ALO - S) * (h - 1)
    assert (SHI - CHI) * ylo >= (CHI - S) * (h - 1)
    # exact two-sided window feasibility with the linarith certificate:
    #   side(+): sup (4Y^k - X^k)/Y^(k-2), side(-): sup (X^k - 4Y^k)/Y^(k-2)
    # over SLO*Y <= S*X <= SHI*Y, Y >= YLO (positive worst coefficients
    # absorbed by YLO^(e-j)*Y^j <= Y^e, negative ones dropped against Y^j >= 0)
    for sign in (+1, -1):
        tot = Fraction(0)
        for i in range(1, m + 1):
            j = k - 2 * i
            Lj, Uj = Fraction(SLO, S) ** j, Fraction(SHI, S) ** j
            assert Uj < 4, (k, j)
            sgn = (1 if i % 2 == 1 else -1) * sign
            coef = ES[i - 1] * ((4 - Lj) if sgn == 1 else -(4 - Uj))
            if coef > 0:
                tot += coef / Fraction(ylo) ** (k - 2 - j)
        assert cden * tot < cnum, (k, sign, float(tot))
    # root-pair strict enclosure from the scaled bracket (omega margins):
    a, b, c, d = cfg["ROOT"]
    assert a == 1 and b == 1  # hlow is d >= 1 via omega
    assert (c * S - d * SHI) * ylo >= d * S
    # telescope shielding: the d=1 telescope solves eq but sits below YLO
    if cfg["TELESCOPE"] is not None:
        ty, tx = cfg["TELESCOPE"]
        assert cfg["eq"](tx, ty) and ty < ylo


def check_lean_constants():
    cfg = CONFIGS[K]
    if K == 5:
        check_lean_constants_k5()
    else:
        check_lean_constants_generic(cfg)
    # root pair straddle + det (all k)
    a, b, c, d = ROOT
    assert a**K < N * b**K and c**K > N * d**K and c * b == a * d + 1


# ------------------------------------------------------------------- the tree
class Stats:
    __slots__ = ("nodes", "kills", "highs", "splits", "cands", "skipped",
                 "max_depth", "gmax_max", "gmax_sum", "spine", "maxbits")

    def __init__(self):
        self.nodes = self.kills = self.highs = self.splits = 0
        self.cands = self.skipped = 0
        self.max_depth = 0
        self.gmax_max = self.gmax_sum = 0
        self.spine = 0
        self.maxbits = 0


def build(a, b, c, d, Ymax, st, depth, mediants):
    """Returns the certificate tree as nested tuples:
    ('high',) | ('kill',) | ('node', gmax, left, right).
    Asserts exactly the Boolean conditions fareyCheck will decide."""
    st.nodes += 1
    if depth > st.max_depth:
        st.max_depth = depth
    # invariants (by construction, re-checked for safety)
    assert c * b == a * d + 1 and b >= 1 and d >= 1

    if Ymax < b + d:
        st.highs += 1
        return ("high",)

    L = max(b + d, YLO)
    cK, dK, aK, bK = c**K, d**K, a**K, b**K
    st.maxbits = max(st.maxbits, cK.bit_length(), aK.bit_length())
    kill_low = cK < N * dK and CNUM * dK < CDEN * (N * dK - cK) * L * L
    kill_high = N * bK < aK and CNUM * bK < CDEN * (aK - N * bK) * L * L
    if kill_low or kill_high:
        st.kills += 1
        return ("kill",)

    # split at the mediant
    A, B = a + c, b + d
    mediants.add((A, B))
    AK, NBK = A**K, N * B**K
    D = AK - NBK if AK > NBK else NBK - AK
    assert D >= 1, "N must not be a perfect K-th power"
    # exact multiple bound: largest g with CDEN * g^2 * D <= CNUM * B^E
    g = 0
    while CDEN * (g + 1) ** 2 * D <= CNUM * B**E:
        g += 1
    gmax = g
    assert CNUM * B**E < CDEN * (gmax + 1) ** 2 * D
    # candidate refutations (the Lean checker skips Y outside [YLO, Ymax])
    for gg in range(1, gmax + 1):
        Xc, Yc = gg * A, gg * B
        if Yc < YLO or Yc > Ymax:
            st.skipped += 1
            continue
        assert not eq_holds(Xc, Yc), f"SOLUTION FOUND?! (X,Y)=({Xc},{Yc})"
        st.cands += 1
    st.splits += 1
    st.gmax_max = max(st.gmax_max, gmax)
    st.gmax_sum += gmax
    left = build(a, b, A, B, Ymax, st, depth + 1, mediants)
    right = build(A, B, c, d, Ymax, st, depth + 1, mediants)
    return ("node", gmax, left, right)


# --------------------------------------- cross-check vs shared convergent data
def crosscheck_json(mediants, Ymax):
    """Every convergent of 4^(1/k) from the uniform campaign artifact
    compute/artifacts/thue_convergents_k<K>.json whose denominator is <= Ymax
    must occur as a mediant of the descent tree, and its (p, q, D) row must
    be internally consistent (determinant + exact straddle signs)."""
    import json
    with open(f"compute/artifacts/thue_convergents_k{K}.json") as fh:
        data = json.load(fh)
    assert data["k"] == K and data["columns"][:3] == \
        ["p_i", "q_i", f"D_i = p_i^k - 4*q_i^k", "a_{i+1}"][:3]
    rows = [(int(p), int(q), int(D), int(anext)) for p, q, D, anext in data["data"]]
    prev = None
    matched = 0
    for i, (p, q, D, _anext) in enumerate(rows):
        assert p**K - N * q**K == D, f"row {i}: D mismatch"
        assert (D > 0) == (i % 2 == 1) and D != 0, f"row {i}: alternation"
        if prev is not None:
            pp, qq = prev
            assert p * qq - pp * q in (1, -1), f"row {i}: determinant"
        prev = (p, q)
        root_endpoints = {(ROOT[0], ROOT[1]), (ROOT[2], ROOT[3])}
        if q <= Ymax and (p, q) not in root_endpoints:
            assert (p, q) in mediants, f"convergent {p}/{q} missing from tree"
            matched += 1
    return matched, len(rows)


# ------------------------------------------------------- independent re-check
def verify(t, a, b, c, d, Ymax):
    """Re-run the exact semantics of fareyCheck over the finished tree
    (independent of build's control flow)."""
    if t[0] == "high":
        return Ymax < b + d
    L = max(b + d, YLO)
    if t[0] == "kill":
        return (c**K < N * d**K and CNUM * d**K < CDEN * (N * d**K - c**K) * L**2) or \
               (N * b**K < a**K and CNUM * b**K < CDEN * (a**K - N * b**K) * L**2)
    _, gmax, left, right = t
    A, B = a + c, b + d
    D = abs(A**K - N * B**K)
    if not CNUM * B**E < CDEN * (gmax + 1) ** 2 * D:
        return False
    for gg in range(1, gmax + 1):
        if YLO <= gg * B <= Ymax and eq_holds(gg * A, gg * B):
            return False
    return verify(left, a, b, A, B, Ymax) and verify(right, A, B, c, d, Ymax)


# ------------------------------------------------------------------- emission
def emit(t, defs, counter):
    """Post-order emission with chunking: returns (expr, depth)."""
    if t[0] == "high":
        return (".high", 1)
    if t[0] == "kill":
        return (".kill", 1)
    _, gmax, left, right = t
    ls, ldep = emit(left, defs, counter)
    rs, rdep = emit(right, defs, counter)
    expr = f"(.node {gmax} {ls} {rs})"
    depth = 1 + max(ldep, rdep)
    if depth >= CHUNK_DEPTH:
        name = f"{CERT_NAME}C{counter[0]}"
        counter[0] += 1
        defs.append(f"private def {name} : FareyTree :=\n  {expr}\n")
        return (name, 1)
    return (expr, depth)


def render(t, exp):
    a, b, c, d = ROOT
    qhi = CONFIGS[K]["QHI"]
    defs = []
    counter = [0]
    expr, _ = emit(t, defs, counter)
    lines = [
        f"/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP={exp}).",
        f"   Farey/Stern-Brocot descent certificate for k = {K}, N = 4:",
        f"   root pair {a}/{b} < 4^(1/{K}) < {c}/{d}, Thue window "
        f"{CDEN}*|X^{K}-4Y^{K}| <= {CNUM}*Y^{E},",
        f"   Ylo = {YLO}, Ymax = {qhi} * 10^{exp}.  Do not edit by hand. -/",
        "",
        "-- generated single-line tree literals (repo precedent: Erdos154.lean)",
        "set_option linter.style.longLine false",
        "",
    ]
    lines.extend(defs)
    lines.append(f"def {CERT_NAME} : FareyTree :=\n  {expr}\n")
    return "\n".join(lines)


def main():
    global K, E, N, CNUM, CDEN, YLO, ROOT, CERT_NAME, eq_holds
    exp = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    cfg = CONFIGS[K]
    E, N = K - 2, 4
    CNUM, CDEN, YLO, ROOT = cfg["CNUM"], cfg["CDEN"], cfg["YLO"], cfg["ROOT"]
    CERT_NAME = f"k{K}FareyCert"
    eq_holds = cfg["eq"]
    h = (K + 1) // 2
    Ymax = cfg["QHI"] * 10**exp
    check_lean_constants()

    st = Stats()
    mediants = set()
    t = build(*ROOT, Ymax, st, 1, mediants)
    assert verify(t, *ROOT, Ymax), "independent re-check failed"
    matched, total = crosscheck_json(mediants, Ymax)

    out = render(t, exp)
    import os
    os.makedirs("compute/artifacts", exist_ok=True)
    path = f"compute/artifacts/erdos686_k{K}_farey_cert_e{exp}.lean"
    with open(path, "w") as fh:
        fh.write(out)

    print(f"[PASS] k={K} Farey descent certificate, Ymax = {cfg['QHI']}*10^{exp}")
    print(f"       covers: no solution with YLO={YLO} <= Y=n+{h} <= {cfg['QHI']}*10^{exp}"
          f"  (=> none with 221 <= d < 10^{exp})")
    print(f"       nodes={st.nodes} (splits={st.splits}, kills={st.kills}, highs={st.highs})")
    print(f"       tree depth={st.max_depth}, candidate (X,Y) pairs refuted={st.cands}, "
          f"skipped(out-of-range)={st.skipped}")
    print(f"       gmax: max={st.gmax_max}, sum={st.gmax_sum}; largest integer ~{st.maxbits} bits")
    print(f"       cross-check vs thue_convergents_k{K}.json: {matched} convergents "
          f"(of {total} rows) all present as tree mediants")
    print(f"       wrote {path} ({len(out)} bytes)")


if __name__ == "__main__":
    main()
