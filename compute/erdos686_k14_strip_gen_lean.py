#!/usr/bin/env python3
"""Independent (pure-integer, no sympy) cross-check of the Erdos686 k=14
strip certificates + generator for ErdosProblems/Erdos686FourteenStrip.lean.

Reads compute/artifacts/k14_strip_cover.json (produced by
compute/erdos686_k14_strip.py) and re-verifies every fact the Lean module
relies on, with independent code paths:

  1. T = 16W^7-3640W^5+202566W^3-2656355W, D = T^2 - 256*S exact;
     7 | T identically; T odd at odd arguments.
  2. Shifted-coefficient certificates at v0 = 3991 for:
       T > 0;  Psi > 0 (the hDneg upper certificate);
       Phi(B0) > 0 (the hDlo lower certificate at B0 = 11680);
     and the two exact linarith identities with nonnegative multipliers.
  3. Per cover prime p: brute force over all (x, y) in [0,p)^2 that
     S(x) = 4 S(y) mod p implies (T(x) - 2T(y)) mod p not in badList(p).
  4. Dispatch: for every candidate a = 7(2j+1), j < 834 (odd multiples of
     7 below B0 = 11680), some cover prime p has (-a) mod p in badList(p).

Then writes the Lean module text (curve lemmas + dispatch decide + trap
certificates + main theorem) to ErdosProblems/Erdos686FourteenStrip.lean.
"""

import json
import sys

V0 = 3991
B0 = 11680
J = 834

# ---------- dense integer polynomials, index = degree ----------

def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r

def padd(*ps):
    n = max(len(p) for p in ps)
    return [sum(p[i] if i < len(p) else 0 for p in ps) for i in range(n)]

def pscale(c, p):
    return [c * a for a in p]

def peval(p, x):
    r = 0
    for a in reversed(p):
        r = r * x + a
    return r

def pshift(p, v0):
    """coefficients of p(v0 + t) in t."""
    res = [0]
    for a in reversed(p):
        res = padd(pmul(res, [v0, 1]), [a])
    return res

def plin(p, a0, a1):
    """p(a0 + a1*t) in t."""
    res = [0]
    for c in reversed(p):
        res = padd(pmul(res, [a0, a1]), [c])
    return res

def pneg(p):
    return pscale(-1, p)

def psub(p, q):
    return padd(p, pneg(q))

# ---------- 1. algebra ----------

S = [1]
for l in range(1, 14, 2):
    S = pmul(S, [-l * l, 0, 1])
T = [0, -2656355, 0, 202566, 0, -3640, 0, 16]
D = padd(pmul(T, T), pscale(-256, S))
while len(D) > 1 and D[-1] == 0:
    D.pop()
assert D == [4674935865600, 0, 1455430979401, 0, -92807039780, 0, 1318847348], D
# 7 | T identically: T = 16(W^7 - W) + 7*(-520 W^5 + 28938 W^3 - 379477 W)
assert T == padd(pscale(16, [0, -1, 0, 0, 0, 0, 0, 1]),
                 pscale(7, [0, -379477, 0, 28938, 0, -520])), "7|T witness"
# T odd at odd W: T(W) = 2*(8W^7 - 1820W^5 + 101283W^3 - 1328178W) + W
assert T == padd(pscale(2, [0, -1328178, 0, 101283, 0, -1820, 0, 8]), [0, 1])
print("[1] T, D, 7|T, parity witnesses: OK")

# ---------- 2. certificates ----------

def shifted_ok(p, v0=V0):
    sh = pshift(p, v0)
    return all(c >= 0 for c in sh) and sh[0] > 0

assert shifted_ok(T), "T > 0 at 3991"

# Psi (hDneg): 47045881*92807039780 v^4 + 4*47045881*D(v)
#   - 1318847348 (21v+24)^6 - 130321*1455430979401 (21v+24)^2
#   - 47045881*4674935865600  > 0
Psi = padd(pscale(47045881 * 92807039780, [0, 0, 0, 0, 1]),
           pscale(4 * 47045881, D),
           pneg(plin(pscale(1318847348, [0, 0, 0, 0, 0, 0, 1]), 24, 21)),
           pneg(plin(pscale(130321 * 1455430979401, [0, 0, 1]), 24, 21)),
           [-47045881 * 4674935865600])
assert shifted_ok(Psi), "Psi certificate at 3991"
# identity: 19^6 (4D(v) - D(w)) = Psi(v) + 1318847348*A6 + 92807039780*19^6*A4
#   + 1455430979401*19^4*A2   over Z[v,w]  (A6, A4, A2 the power gaps).
# Verify as an exact bivariate identity (dict {(deg_v, deg_w): coeff}).

def bv(p):
    """univariate-in-v poly -> bivariate dict."""
    return {(i, 0): c for i, c in enumerate(p) if c}

def bw(p):
    """univariate-in-w poly -> bivariate dict."""
    return {(0, i): c for i, c in enumerate(p) if c}

def badd(*ds):
    r = {}
    for d in ds:
        for k, c in d.items():
            r[k] = r.get(k, 0) + c
    return {k: c for k, c in r.items() if c}

def bscale(c, d):
    return {k: c * x for k, x in d.items()}

A6 = badd(bv(plin([0] * 6 + [1], 24, 21)), bscale(-19**6, bw([0] * 6 + [1])))
A4 = badd(bw([0] * 4 + [1]), bscale(-1, bv([0] * 4 + [1])))
A2 = badd(bv(plin([0, 0, 1], 24, 21)), bscale(-361, bw([0, 0, 1])))
lhs = badd(bscale(4 * 47045881, bv(D)), bscale(-47045881, bw(D)))
rhs = badd(bv(Psi), bscale(1318847348, A6),
           bscale(92807039780 * 47045881, A4),
           bscale(1455430979401 * 130321, A2))
assert badd(lhs, bscale(-1, rhs)) == {}, "hDneg identity"
print("[2] hDneg: Psi > 0 at 3991 and exact identity: OK")

# Phi (hDlo) at B0: with M5 = 10^7 * 19^5
M5 = 10**7 * 19**5
Tw_low = padd(plin(pscale(16 * 19**5, [0, 0, 0, 0, 0, 0, 0, 1]), -11, 11),
              pneg(plin(pscale(3640 * 10**7, [0, 0, 0, 0, 0, 1]), 24, 21)),
              pscale(202566 * M5, [0, 0, 0, 1]),
              pneg(pscale(2656355 * 10**7 * 19**4, [24, 21])))
Dw_low = pscale(190, padd(
    plin(pscale(1318847348 * 19**4, [0, 0, 0, 0, 0, 0, 1]), -11, 11),
    pneg(plin(pscale(92807039780 * 10**6, [0, 0, 0, 0, 1]), 24, 21)),
    pscale(1455430979401 * 10**6 * 19**4, [0, 0, 1]),
    [4674935865600 * 10**6 * 19**4]))
Phi = padd(pscale(B0, padd(Tw_low, pscale(2 * M5, T))),
           Dw_low, pscale(-4 * M5, D))
assert shifted_ok(Phi), "Phi(B0) certificate at 3991"
assert not shifted_ok(padd(pscale(B0 - 1, padd(Tw_low, pscale(2 * M5, T))),
                           Dw_low, pscale(-4 * M5, D))), "B0 minimal"
# identity: M5*(B0*(T(w)+2T(v)) + D(w) - 4D(v)) =
#   Phi(v) + B0*16*19^5*A7 + B0*3640*10^7*A5 + B0*202566*M5*A3
#   + B0*2656355*10^7*19^4*A1 + 190*1318847348*19^4*B6
#   + 190*92807039780*10^6*B4 + 190*1455430979401*10^6*19^4*B2
# with A7 = (10w)^7-(11v-11)^7, A5 = (21v+24)^5-(19w)^5, A3 = w^3-v^3,
#      A1 = (21v+24)-19w,       B6 = (10w)^6-(11v-11)^6,
#      B4 = (21v+24)^4-(19w)^4, B2 = w^2-v^2   (all >= 0 on the window).
A7 = badd(bscale(10**7, bw([0] * 7 + [1])), bscale(-1, bv(plin([0]*7+[1], -11, 11))))
A5 = badd(bv(plin([0]*5+[1], 24, 21)), bscale(-19**5, bw([0]*5+[1])))
A3 = badd(bw([0, 0, 0, 1]), bscale(-1, bv([0, 0, 0, 1])))
A1 = badd(bv([24, 21]), bscale(-19, bw([0, 1])))
B6 = badd(bscale(10**6, bw([0]*6+[1])), bscale(-1, bv(plin([0]*6+[1], -11, 11))))
B4 = badd(bv(plin([0]*4+[1], 24, 21)), bscale(-19**4, bw([0]*4+[1])))
B2 = badd(bw([0, 0, 1]), bscale(-1, bv([0, 0, 1])))
lhs = badd(bscale(B0 * M5, bw(T)), bscale(2 * B0 * M5, bv(T)),
           bscale(M5, bw(D)), bscale(-4 * M5, bv(D)))
rhs = badd(bv(Phi),
           bscale(B0 * 16 * 19**5, A7), bscale(B0 * 3640 * 10**7, A5),
           bscale(B0 * 202566 * M5, A3), bscale(B0 * 2656355 * 10**7 * 19**4, A1),
           bscale(190 * 1318847348 * 19**4, B6),
           bscale(190 * 92807039780 * 10**6, B4),
           bscale(190 * 1455430979401 * 10**6 * 19**4, B2))
assert badd(lhs, bscale(-1, rhs)) == {}, "hDlo identity"
print(f"[2] hDlo: Phi({B0}) > 0 at 3991 (minimal) and exact identity: OK")

# ---------- 3 + 4. cover cross-check (brute force) ----------

with open("compute/artifacts/k14_strip_cover.json") as f:
    cover = json.load(f)
assert cover["V0"] == V0 and cover["B0"] == B0 and cover["num_cands"] == J
COVER = [(c["p"], c["bad"]) for c in cover["cover"]]

CANDS = list(range(7, B0, 14))
assert len(CANDS) == J and CANDS[-1] == 11669

for p, bad in COVER:
    badset = set(bad)
    Sv = [peval(S, x) % p for x in range(p)]
    Tv = [peval(T, x) % p for x in range(p)]
    for x in range(p):
        for y in range(p):
            if Sv[x] == (4 * Sv[y]) % p:
                assert (Tv[x] - 2 * Tv[y]) % p not in badset, (p, x, y)
print(f"[3] curve lemmas: badList(p) disjoint from solvable residues for "
      f"all {len(COVER)} primes (brute force): OK")

for a in CANDS:
    assert any((-a) % p in set(bad) for p, bad in COVER), a
print(f"[4] dispatch: all {J} candidates killed: OK")

# ---------- 5. Lean module generation ----------

def wrap_list(items, indent, width=76):
    """wrap a Lean list literal body over lines at comma boundaries."""
    lines, cur = [], " " * indent
    for i, it in enumerate(items):
        tok = str(it) + ("," if i + 1 < len(items) else "")
        if len(cur) + 1 + len(tok) > width and cur.strip():
            lines.append(cur)
            cur = " " * indent + tok
        else:
            cur = cur + (" " if cur.strip() else "") + tok if cur.strip() \
                else " " * indent + tok
    lines.append(cur)
    return "\n".join(lines).lstrip()

curve_lemmas = []
for p, bad in COVER:
    lst = "[" + wrap_list(bad, 10) + "]"
    curve_lemmas.append(f"""set_option maxRecDepth 200000 in
set_option maxHeartbeats {max(8000000, p*p*1000)} in
-- Kernel enumeration of the {p}² pairs `(x, y) ∈ (ZMod {p})²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p{p} :
    ∀ x y : ZMod {p},
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([{wrap_list(bad, 10)}] : List (ZMod {p})) := by
  decide
""")

disjuncts = []
for p, bad in COVER:
    disjuncts.append(
        f"      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod {p}) ∈\n"
        f"        ([{wrap_list(bad, 10)}] : List (ZMod {p}))")
dispatch = " ∨\n".join(disjuncts)

kill_cases = "\n".join(
    f"  · exact strip_kill strip_curve_p{p} hS hm hjm hbad" for p, _ in COVER)

rcases_pat = " |\n      ".join(
    " | ".join(["hbad"] * min(8, len(COVER) - i)) for i in range(0, len(COVER), 8))

primes_str = wrap_list([p for p, _ in COVER], 0, width=70)

module = f"""/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686EvenK

/-!
# Erdős Problem 686: the `k = 14` strip for `N = 4`, `d ≥ 221`

`ErdosProblems/Erdos686EvenK.lean` banks the large-gap branch
`no_gap_solution_four_even_fourteen_of_large_gap` (`d ≥ 663000`), where the
trapped center `m = T₁₄(w) - 2T₁₄(v)` falls in `(-7, 0)` and dies by
`7 ∣ m`.  This module closes the whole range `d ≥ 221` (in particular the
strip `221 ≤ d < 663000`) for

  `blockProduct 14 (n + d) = 4 * blockProduct 14 n`.

Normalizations (identical to the EvenK module): `w = 2(n+d) + 15`,
`v = 2n + 15`, `S₁₄(W) = ∏_{{l odd, 1 ≤ l ≤ 13}} (W² - l²)`,
`T₁₄ = 16W⁷ - 3640W⁵ + 202566W³ - 2656355W`, `D₁₄ = T₁₄² - 256·S₁₄`, and on
the curve `S₁₄(w) = 4S₁₄(v)` the integers `m = T₁₄(w) - 2T₁₄(v)`,
`X = T₁₄(w) + 2T₁₄(v)` satisfy `m·X = D₁₄(w) - 4D₁₄(v)`.

The banked window linearizations give `19w ≤ 21v + 24`, `11v ≤ 10w + 11`,
and `d ≥ 221` forces `v ≥ 3991` (`row_base_lower_k14`).  Two univariate
shifted-coefficient certificates at `v₀ = 3991` (lower-bounding `T₁₄(w)`
*and* `D₁₄(w)` termwise through the window) trap `m` in `(-11680, 0)`;
`11680` is the minimal shifted-certifiable width.  Since `m` is odd (`T₁₄`
is odd at odd arguments) and `7 ∣ m` (Fermat mod 7), the candidate set is
the `834` values `m = -7(2j+1)`, `j < 834`.

Each candidate is killed modulo one of the {len(COVER)} primes
`{primes_str}`:
for each prime `p` a kernel `decide` shows that on the curve
`S₁₄(x) = 4S₁₄(y)` over `(ZMod p)²` the value `T₁₄(x) - 2T₁₄(y)` never
lands in an explicit `badList p`, while a second kernel `decide` shows
every candidate hits some `badList` (`strip_dispatch`).  The greedy
cost-weighted cover was computed and exactly verified (twice,
independently) in `compute/erdos686_k14_strip.py` and
`compute/erdos686_k14_strip_gen_lean.py`; total kernel work is
`Σ p² ≈ 1.06·10⁶` pairs.

The corollary `no_gap_solution_four_even_k` packages the five even-`k`
theorems (`k ∈ {{6, 8, 10, 12, 14}}`, `d ≥ 221`).
-/

namespace Erdos686

namespace Erdos686Variant

/-! ## Block-product expansion and centered bridge (private copies of the
EvenK lemmas, which are `private` there) -/

private lemma strip_blockProduct_fourteen_prod (x : ℕ) :
    blockProduct 14 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) *
        (x + 8) * (x + 9) * (x + 10) * (x + 11) * (x + 12) * (x + 13) *
        (x + 14) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

private lemma strip_s14_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 15) ^ 2 - 1) * ((2 * (x : ℤ) + 15) ^ 2 - 9) *
        ((2 * (x : ℤ) + 15) ^ 2 - 25) * ((2 * (x : ℤ) + 15) ^ 2 - 49) *
        ((2 * (x : ℤ) + 15) ^ 2 - 81) * ((2 * (x : ℤ) + 15) ^ 2 - 121) *
        ((2 * (x : ℤ) + 15) ^ 2 - 169) = 16384 * (blockProduct 14 x : ℤ) := by
  rw [strip_blockProduct_fourteen_prod]
  push_cast
  ring

/-- `7 ∣ T₁₄(x) = 16x⁷ - 3640x⁵ + 202566x³ - 2656355x` for every integer `x`
(`T₁₄ = 16(x⁷ - x) + 7(-520x⁵ + 28938x³ - 379477x)`). -/
private lemma strip_seven_dvd_T14 (x : ℤ) :
    (7 : ℤ) ∣ 16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x := by
  have h7 : (7 : ℤ) ∣ x ^ 7 - x := by
    have hx : ((x ^ 7 - x : ℤ) : ZMod 7) = 0 := by
      push_cast
      have hz : ∀ y : ZMod 7, y ^ 7 - y = 0 := by decide
      exact hz (x : ZMod 7)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hx
  obtain ⟨y, hy⟩ := h7
  exact ⟨16 * y - 520 * x ^ 5 + 28938 * x ^ 3 - 379477 * x,
    by linear_combination 16 * hy⟩

/-! ## Univariate shifted-coefficient certificates at `v₀ = 3991`

All three were verified exactly (all shifted coefficients nonnegative,
constant term positive) in `compute/erdos686_k14_strip.py`. -/

private lemma strip_k14_T_pos {{W : ℤ}} (hW : 3991 ≤ W) :
    0 < 16 * W ^ 7 - 3640 * W ^ 5 + 202566 * W ^ 3 - 2656355 * W := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 3991 + t :=
    ⟨W - 3991, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6, pow_nonneg ht 7]

/-- Upper certificate: through the window `19w ≤ 21v + 24`, `v⁴ ≤ w⁴` this
forces `D₁₄(w) - 4D₁₄(v) < 0` for `v ≥ 3991`. -/
private lemma strip_k14_upper {{v : ℤ}} (hv : 3991 ≤ v) :
    1318847348 * (21 * v + 24) ^ 6 +
        130321 * 1455430979401 * (21 * v + 24) ^ 2 +
        47045881 * 4674935865600 <
      47045881 * 92807039780 * v ^ 4 +
        188183524 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
          1455430979401 * v ^ 2 + 4674935865600) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 3991 + t :=
    ⟨v - 3991, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6]

/-- Lower certificate: termwise through the window
(`11v - 11 ≤ 10w ≤ 10/19·(21v + 24)`, scaled by `10⁷·19⁵ = 24760990000000`)
this forces `-11680·X < D₁₄(w) - 4D₁₄(v)` for `v ≥ 3991`; the width `11680`
is minimal for this certificate shape. -/
private lemma strip_k14_lower {{v : ℤ}} (hv : 3991 ≤ v) :
    0 < 11680 * (39617584 * (11 * v - 11) ^ 7 -
          36400000000 * (21 * v + 24) ^ 5 +
          202566 * 24760990000000 * v ^ 3 -
          2656355 * 10000000 * 130321 * (21 * v + 24) +
          2 * 24760990000000 *
            (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v)) +
        190 * (1318847348 * 130321 * (11 * v - 11) ^ 6 -
          92807039780 * 1000000 * (21 * v + 24) ^ 4 +
          1455430979401 * 1000000 * 130321 * v ^ 2 +
          4674935865600 * 1000000 * 130321) -
        4 * 24760990000000 *
          (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
            1455430979401 * v ^ 2 + 4674935865600) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 3991 + t :=
    ⟨v - 3991, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6, pow_nonneg ht 7]

/-! ## Modular curve certificates

For each cover prime `p`: on the curve `S₁₄(x) = 4S₁₄(y)` over `(ZMod p)²`
the value `T₁₄(x) - 2T₁₄(y)` avoids the listed residues (the residues of
the candidates assigned to `p`). -/

{"".join(curve_lemmas)}
/-- Transfer a curve certificate to the trapped integer center: if
`m = T₁₄(w) - 2T₁₄(v)` on the curve and `m = -a`, then `-a mod p` cannot
lie in a residue list avoided by the curve. -/
private lemma strip_kill {{p : ℕ}} {{L : List (ZMod p)}}
    (hcurve : ∀ x y : ZMod p,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉ L)
    {{w v m : ℤ}} {{a : ℕ}}
    (hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) *
        (w ^ 2 - 81) * (w ^ 2 - 121) * (w ^ 2 - 169) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49) *
        (v ^ 2 - 81) * (v ^ 2 - 121) * (v ^ 2 - 169)))
    (hm : m = (16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w) -
        2 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v))
    (ha : m = -(a : ℤ)) (hbad : -(a : ZMod p) ∈ L) : False := by
  have hS' := congrArg (fun z : ℤ => (z : ZMod p)) hS
  push_cast at hS'
  have hm' := congrArg (fun z : ℤ => (z : ZMod p)) hm
  push_cast at hm'
  have ha' := congrArg (fun z : ℤ => (z : ZMod p)) ha
  push_cast at ha'
  exact hcurve (w : ZMod p) (v : ZMod p) hS' (by rw [← hm', ha']; exact hbad)

-- The {len(COVER)}-fold disjunction of list memberships needs a larger-than-default
-- `Decidable` instance term (the default `synthInstance.maxSize` is 128).
set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 200000 in
-- Kernel scan of the 834 candidates: each evaluates at most {len(COVER)} literal
-- casts into `ZMod p` plus short list-membership scans, so the heartbeat
-- cap is sized at roughly 10⁵ heartbeats per candidate.
set_option maxHeartbeats 100000000 in
-- Dispatch: every candidate `m = -7(2j+1)`, `j < 834`, hits the bad-residue
-- list of one of the cover primes.
private theorem strip_dispatch :
    ∀ j : Fin 834,
{dispatch} := by
  decide

/-! ## `k = 14`, all `d ≥ 221` -/

set_option maxHeartbeats 16000000 in
-- The two window `linarith` certificates expand degree-7 polynomials with
-- 10²⁰-scale coefficients, and the final `omega`/`rcases` dispatch walks a
-- 31-fold disjunction, so this proof needs more than the default budget.
/-- **Erdős 686, `k = 14`, `N = 4`, `d ≥ 221`**: fourteen-blocks in quotient
`4` with gap `d ≥ 221` do not exist.  The trapped center
`m = T₁₄(w) - 2T₁₄(v)` lies in `(-11680, 0)`, is odd, and is divisible by
`7`; each of the `834` candidates `m = -7(2j+1)` dies modulo one of
{len(COVER)} primes (kernel certificates `strip_curve_p*` + `strip_dispatch`).
This covers the strip `221 ≤ d < 663000` left open by
`no_gap_solution_four_even_fourteen_of_large_gap`, and reproves the
large-gap branch along the way. -/
theorem no_gap_solution_four_even_fourteen {{n d : ℕ}} (hd : 221 ≤ d) :
    blockProduct 14 (n + d) ≠ 4 * blockProduct 14 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hnlow : 9 * d ≤ n + 1 := row_base_lower_k14 hd hup
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 21) (B := 19)
      (k := 14) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlin2 :=
    ratio_window_upper_linearize_of_pow_bracket (N := 4) (A := 11) (B := 10)
      (k := 14) (n := n) (d := d) (by norm_num) (by norm_num) hlo
  have hZ : ((blockProduct 14 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 14 n : ℕ) : ℤ) := by exact_mod_cast heq
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = 2 * ((n : ℤ) + (d : ℤ)) + 15 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℤ, v = 2 * (n : ℤ) + 15 := ⟨_, rfl⟩
  have hv0 : (3991 : ℤ) ≤ v := by omega
  have hw0 : (3991 : ℤ) ≤ w := by omega
  have hlink : 19 * w ≤ 21 * v + 24 := by omega
  have hlink2 : 11 * v ≤ 10 * w + 11 := by omega
  have h1 := strip_s14_bridge (n + d)
  have h2 := strip_s14_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 15 = w := by push_cast; omega
  have hcv : 2 * ((n : ℕ) : ℤ) + 15 = v := by omega
  rw [hcw] at h1
  rw [hcv] at h2
  have hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) *
        (w ^ 2 - 81) * (w ^ 2 - 121) * (w ^ 2 - 169) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49) *
        (v ^ 2 - 81) * (v ^ 2 - 121) * (v ^ 2 - 169)) := by
    rw [h1, h2, hZ]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      m = (16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w) -
        2 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v) :=
    ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ,
      X = (16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w) +
        2 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v) :=
    ⟨_, rfl⟩
  have hTw : 0 < 16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w :=
    strip_k14_T_pos hw0
  have hTv : 0 < 16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v :=
    strip_k14_T_pos hv0
  have hXpos : 0 < X := by rw [hX]; linarith
  have hmX : m * X =
      (1318847348 * w ^ 6 - 92807039780 * w ^ 4 + 1455430979401 * w ^ 2 +
          4674935865600) -
        4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
          1455430979401 * v ^ 2 + 4674935865600) := by
    rw [hm, hX]; linear_combination 256 * hS
  have h19w6 : (19 * w) ^ 6 ≤ (21 * v + 24) ^ 6 :=
    pow_le_pow_left₀ (by omega) (by omega) 6
  have hw4 : v ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ (by omega) (by omega) 4
  have h19w2 : (19 * w) ^ 2 ≤ (21 * v + 24) ^ 2 :=
    pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔneg : (1318847348 * w ^ 6 - 92807039780 * w ^ 4 +
      1455430979401 * w ^ 2 + 4674935865600) -
      4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 + 1455430979401 * v ^ 2 +
        4674935865600) < 0 := by
    linarith [h19w6, hw4, h19w2, strip_k14_upper hv0]
  have h10w7 : (11 * v - 11) ^ 7 ≤ (10 * w) ^ 7 :=
    pow_le_pow_left₀ (by omega) (by omega) 7
  have h10w6 : (11 * v - 11) ^ 6 ≤ (10 * w) ^ 6 :=
    pow_le_pow_left₀ (by omega) (by omega) 6
  have h19w5 : (19 * w) ^ 5 ≤ (21 * v + 24) ^ 5 :=
    pow_le_pow_left₀ (by omega) (by omega) 5
  have h19w4 : (19 * w) ^ 4 ≤ (21 * v + 24) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have hw3 : v ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by omega) (by omega) 3
  have hw2 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔlo : -11680 * X < (1318847348 * w ^ 6 - 92807039780 * w ^ 4 +
      1455430979401 * w ^ 2 + 4674935865600) -
      4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 + 1455430979401 * v ^ 2 +
        4674935865600) := by
    rw [hX]
    linarith [h10w7, h10w6, h19w5, h19w4, hw3, hw2, hlink,
      strip_k14_lower hv0]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -11680 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  -- parity: m = 2c + w with w odd, and 7 ∣ m
  obtain ⟨cpar, hcpar⟩ : ∃ c : ℤ, m = 2 * c + w :=
    ⟨8 * w ^ 7 - 1820 * w ^ 5 + 101283 * w ^ 3 - 1328178 * w -
      (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v),
      by rw [hm]; ring⟩
  have h7m : (7 : ℤ) ∣ m := by
    rw [hm]
    exact dvd_sub (strip_seven_dvd_T14 w) ((strip_seven_dvd_T14 v).mul_left 2)
  -- the candidate index: m = -7(2j+1) with j < 834
  obtain ⟨j, hj, hjm⟩ : ∃ j : ℕ, j < 834 ∧ m = -((7 * (2 * j + 1) : ℕ) : ℤ) :=
    ⟨((-m).toNat / 7 - 1) / 2, by omega, by omega⟩
  rcases strip_dispatch ⟨j, hj⟩ with
      {rcases_pat}
{kill_cases}

/-! ## Packaged even-`k` corollary -/

/-- **Erdős 686, even `k ≤ 14`, `N = 4`, `d ≥ 221`**: for
`k ∈ {{6, 8, 10, 12, 14}}` no `k`-block is `4` times another `k`-block at
gap `d ≥ 221`. -/
theorem no_gap_solution_four_even_k {{k n d : ℕ}}
    (hk : k ∈ ({{6, 8, 10, 12, 14}} : Finset ℕ)) (hd : 221 ≤ d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  fin_cases hk
  · exact no_gap_solution_four_even_six hd
  · exact no_gap_solution_four_even_eight hd
  · exact no_gap_solution_four_even_ten hd
  · exact no_gap_solution_four_even_twelve hd
  · exact no_gap_solution_four_even_fourteen hd

end Erdos686Variant

end Erdos686
"""

with open("ErdosProblems/Erdos686FourteenStrip.lean", "w") as f:
    f.write(module)
print("[5] wrote ErdosProblems/Erdos686FourteenStrip.lean")
print("    cover primes:", [p for p, _ in COVER])
print("    total kernel pairs:", sum(p * p for p, _ in COVER))
