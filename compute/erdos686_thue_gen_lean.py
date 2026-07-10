#!/usr/bin/env python3
"""
Erdos 686, odd k, N = 4: generator + exact verifier for the Farey/Stern-Brocot
descent certificate consumed by ErdosProblems/Erdos686ConvergentMachinery.lean
(`FareyTree` / `fareyCheck`), instantiated here for k = 5.

Mathematical shape (all integer arithmetic, no reals anywhere):

  A solution of (n+d+1)...(n+d+5) = 4 (n+1)...(n+5) in centered coordinates
  X = n+d+3, Y = n+3 satisfies the exact Thue window (proved in
  Erdos686FiveThue.lean from the equation + the banked ratio window)

      CDEN * |X^K - N*Y^K| <= CNUM * Y^(K-2),     K = 5, N = 4,
      CNUM/CDEN = 44/5 = 8.8   (true constant sup|5r^3-20| on the bracket
                                131/100 < r < 132/100 is ~8.7595),

  valid for Y >= YLO = 665 (from d >= 221 via the banked confinement
  3d <= n+1 < 4d).  The descent walks the Stern-Brocot tree from the root
  Farey pair 1/1 < 4^(1/5) < 4/3 (det 4*1 - 1*3 = 1).  Every node of the
  certificate tree is one of

    .high            b + d > Ymax: mediant lemma forces Y >= b+d > Ymax;
    .kill            one endpoint's quintic side certificate contradicts
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

Usage:  python3 compute/erdos686_thue_gen_lean.py [YMAX_EXP]
        YMAX_EXP defaults to 60; Ymax = 4 * 10^YMAX_EXP  (covers d < 10^YMAX_EXP
        via Y = n+3 < 4d + 2).  Writes the Lean certificate fragment to
        compute/artifacts/erdos686_k5_farey_cert_e<EXP>.lean and prints stats.
"""

import sys

sys.setrecursionlimit(4_000_000)

# ---------------------------------------------------------------- k = 5 config
K = 5
E = K - 2                      # Thue exponent K-2 (machinery parameter e)
N = 4
CNUM, CDEN = 44, 5             # |X^K - N Y^K| <= (CNUM/CDEN) Y^(K-2) for Y >= YLO
YLO = 665                      # 3*221 + 2
ROOT = (1, 1, 4, 3)            # Farey pair a/b < 4^(1/5) < c/d, det c*b - a*d = 1
CHUNK_DEPTH = 120              # hoist subtrees into named defs beyond this depth
CERT_NAME = "k5FareyCert"


def eq_holds(X, Y):
    """The exact centered equation, in the same ℕ-safe arrangement as Lean:
    X^5 + 4X + 20Y^3 = 4Y^5 + 16Y + 5X^3  (⟺ P5(X) = 4 P5(Y))."""
    return X**5 + 4 * X + 20 * Y**3 == 4 * Y**5 + 16 * Y + 5 * X**3


# ------------------------------------------------------- sanity: Lean constants
def check_lean_constants():
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
    # root pair straddle + det
    a, b, c, d = ROOT
    assert a**K < N * b**K and c**K > N * d**K and c * b == a * d + 1
    # YLO consistency with d >= 221: Y = n+3 >= 3d+2
    assert 3 * 221 + 2 == YLO


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
    """Every convergent of 4^(1/5) from the uniform campaign artifact
    compute/artifacts/thue_convergents_k5.json whose denominator is <= Ymax
    must occur as a mediant of the descent tree, and its (p, q, D) row must
    be internally consistent (determinant + exact straddle signs)."""
    import json
    with open("compute/artifacts/thue_convergents_k5.json") as fh:
        data = json.load(fh)
    assert data["k"] == K and data["columns"][:3] == \
        ["p_i", "q_i", "D_i = p_i^k - 4*q_i^k", "a_{i+1}"][:3]
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
    defs = []
    counter = [0]
    expr, _ = emit(t, defs, counter)
    lines = [
        f"/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP={exp}).",
        f"   Farey/Stern-Brocot descent certificate for k = 5, N = 4:",
        f"   root pair 1/1 < 4^(1/5) < 4/3, Thue window 5*|X^5-4Y^5| <= 44*Y^3,",
        f"   Ylo = {YLO}, Ymax = 4 * 10^{exp}.  Do not edit by hand. -/",
        "",
        "-- generated single-line tree literals (repo precedent: Erdos154.lean)",
        "set_option linter.style.longLine false",
        "",
    ]
    lines.extend(defs)
    lines.append(f"def {CERT_NAME} : FareyTree :=\n  {expr}\n")
    return "\n".join(lines)


def main():
    exp = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    Ymax = 4 * 10**exp
    check_lean_constants()

    st = Stats()
    mediants = set()
    t = build(*ROOT, Ymax, st, 1, mediants)
    assert verify(t, *ROOT, Ymax), "independent re-check failed"
    matched, total = crosscheck_json(mediants, Ymax)

    out = render(t, exp)
    import os
    os.makedirs("compute/artifacts", exist_ok=True)
    path = f"compute/artifacts/erdos686_k5_farey_cert_e{exp}.lean"
    with open(path, "w") as fh:
        fh.write(out)

    print(f"[PASS] k=5 Farey descent certificate, Ymax = 4*10^{exp}")
    print(f"       covers: no solution with YLO={YLO} <= Y=n+3 <= 4*10^{exp}"
          f"  (=> none with 221 <= d < 10^{exp})")
    print(f"       nodes={st.nodes} (splits={st.splits}, kills={st.kills}, highs={st.highs})")
    print(f"       tree depth={st.max_depth}, candidate (X,Y) pairs refuted={st.cands}, "
          f"skipped(out-of-range)={st.skipped}")
    print(f"       gmax: max={st.gmax_max}, sum={st.gmax_sum}; largest integer ~{st.maxbits} bits")
    print(f"       cross-check vs thue_convergents_k5.json: {matched} convergents "
          f"(of {total} rows) all present as tree mediants")
    print(f"       wrote {path} ({len(out)} bytes)")


if __name__ == "__main__":
    main()
