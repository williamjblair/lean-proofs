# Gate-1 report — arXiv:2606.28041 reproduction (Erdős #23)

Date: 2026-07-10. Machine: Apple Silicon, single-threaded runs (≤ 2 cores per
budget; total compute spent: ~20 s). All exact checks in rational arithmetic.

## Verdict: PARTIALLY REPRODUCED

Everything checkable from the shipped ancillary package was verified, both by
running the author's verifier and by an independent from-scratch checker
(21/21 PASS), and the brute-force ground truth was reproduced exactly with an
independent implementation. The single most load-bearing computational step —
per-state dual feasibility over the 12,172 order-10 states (condition 4) —
is NOT verifiable from the package as shipped: the state tables and two
required Python modules are absent (the modules exist in the author's GitHub
tree; the tables would have to be regenerated, which is certificate
*generation* and out of gate-1 scope). For that step we have only the
producer's frozen log. The envelope-row and moment-row *semantics* (steps 3–4
of the chain) are likewise not independently checkable from shipped data.

## Chain status per step

| Step | Status | Evidence |
|---|---|---|
| Package integrity | VERIFIED | `shasum -c SHA256SUMS`: all 13 files OK; pickles audited opcode-level, pure data (no globals) |
| State generation (order-9/10 tables, C₅ lift) | NOT CHECKABLE from package | `cp_cache.pkl`, `c5lift_cache.npz`, `horn_cert_state_it16.pkl`, `dual_cert_n9.pkl`, `horn_Rcbh_exact.pkl` absent; `prove_cert.py`/`flag_exact.py` absent from package (present on GitHub, fetched to `upstream/`) |
| Rational dual: δ_final re-derivation from raw z | VERIFIED INDEPENDENTLY | my `independent_check.py` [A]: δ = 4.8557798001×10⁻⁵ re-derived from `horn_dual.pkl` floats under the declared rationalization, equals saved fraction bit-for-bit |
| Gram decomposition manifest-PSD (w_c ≥ 0) | VERIFIED INDEPENDENTLY | [B]: all 394 atoms ≥ 0; 87 support atoms ≥ 0 (min 9.179×10⁻⁸); structure sane |
| a7 + a8 = 1, a7, a8 ≥ 0 | VERIFIED (values not re-derivable) | [C]: exact on saved fractions; but a7 := 1 − a8 by construction, and per-type/per-root sums (conditions 2–3) need the unshipped env table |
| Per-state residual (condition 4, 12,172 states) | NOT REPRODUCED — producer log only | frozen log `upstream/complete_v2_cert.txt`: min residual −8.812×10⁻⁹ ≥ −ε = −10⁻⁶, 254 s run. The shipped "independent gate" merely reads the saved `valid=True` flag for this condition |
| Threshold/closure arithmetic (n ≤ 40 closes, 41 fails) | VERIFIED INDEPENDENTLY | [D]: δ < 1/20000 exact; (25/2)·1600·δ = 0.971156 < 1 (margin 2.8844%, paper says 2.88%); (25/2)·1681·δ = 1.020321 ≥ 1 |
| Blow-up identity β(G[t]) = t²β(G) | VERIFIED INDEPENDENTLY | proof read (multilinearity argument is correct and standard); brute-forced for all 38 triangle-free order-6 graphs at t=2, C₅[t] t=1..3 (β = t²), C₇[2] |
| Graphon transfer d_mono(W_G) = 2β/N² | VERIFIED by reading | the same no-fractional-gap argument as Lemma 2.1 gives measurable-colouring optimum = integral optimum on step graphons; sound |
| Tails (BCL) | CITATION VERIFIED, proof external | BCL arXiv v1 Theorem 2(b),(c): thresholds 0.3197/0.2486 · C(n,2), "for n large enough" — matches use. Note: cited as "Theorem 1.3" (numbering differs) and BCL arXiv v1 is a Eurocomb *extended abstract* with a proof sketch (flag-algebra SDP); the tails carry their own unverified computational burden |
| Assembly (3 regimes, closed band, no gap) | VERIFIED by reading + exact arithmetic | boundary densities in closed band; [F] transfer identities for all n = 1..40 |
| Brute-force ground truth | REPRODUCED INDEPENDENTLY | own C checker (own g6 decoder + Gray-code max cut) vs paper: in-band max d_mono n=9..12 = 0.049383/0.040000/0.049587/0.055556 (paper: 0.0494/0.0400/0.0496/0.0556) — exact match; author's `brute_dmono.py` (geng path patched) agrees on n=9,10 |
| OEIS cross-check | VERIFIED | my a(N), N=5..12 = 1,1,1,2,2,4,4,5 match A389646 b-file exactly; a(5)=1², a(10)=2² as the paper cites; counts 14/38/107/410/1897/12172/105071/1262180 match A006785 |

Author-runnable scripts from the package: `step1_v2_independent_gate.py`
(PASS, 0.1 s — log `logs_step1_gate.txt`) and `brute_dmono.py` (needs external
nauty geng + path patch — log `logs_author_brute_n9_10.txt`). Everything else
(`complete_v2_cert.py`, `moment_gram_lp.py`, `moment_gram_exact_verify.py`,
`g1_exact_psd.py`, `g1_graphon_density.py`) fails on missing imports/caches.

## Discrepancies and caveats (noted, not over-weighted)

1. **The "independent gate" is weaker than its name.** For condition 4 it
   only reads the producer's saved boolean; a7/a8/ε are taken from the
   producer's pickle, and condition 2 is checked on values the producer
   constructed to satisfy it. Its genuinely independent content: δ formula
   re-derivation from raw z, w ≥ 0, threshold comparison. My checker
   reproduces exactly that independent content (plus the elementary layer).
2. **Raw dual needs a post-solve "LEG FIX".** `horn_dual.pkl` violates
   condition 2 for 2 of 107 types; `complete_v2_cert.py` repairs it by adding
   λ ≈ 1.36×10⁻⁸ before checking. Sound (all conditions re-checked after),
   but the shipped dual is not final as-is and the gate doesn't see this.
3. Stale text in the gate docstring: "δ < 5e-5 ⇒ n ≤ 41, N ≤ 205" and
   "extended from N ≤ 55 to N ≤ 205" — wrong; δ < 5×10⁻⁵ gives n = 40 and the
   printed output/paper correctly say N ≤ 200.
4. Paper §6 says Gram support "77 atoms"; the frozen `moment_gram_w.pkl` has
   **87**. Paper §6 says worst residual "−1.02×10⁻⁸"; frozen log says
   −8.812×10⁻⁹. Both consistent with the admitted non-determinism of the
   moment LP — the paper text describes a different run than the frozen
   snapshot it ships.
5. ε = 10⁻⁶ is a flat robustness bump added to δ (not the ~10⁻⁸ residual
   itself); harmless — it only weakens the bound, and is included in δ_final.
6. BCL citation numbering ("Theorem 1.3" vs Theorem 2 in arXiv v1) and its
   extended-abstract status (see table).
7. `brute_dmono.py` hardcodes a Windows `geng.exe` path; nauty not included.
8. README claims the caches are "regenerable from the scripts", but the
   package lacks `prove_cert.py`/`flag_exact.py`; regeneration requires the
   GitHub tree and re-running LP machinery (generation, not verification).

None of these touch the verified arithmetic; items 1–2 are the reasons the
verdict is "partially" rather than "fully" reproduced.

## What I ran (artifacts in compute23/)

- `independent_check.py` — from-scratch checker, 21/21 PASS, 6 s
  (`logs_independent_check.txt`): restricted unpickler; δ re-derivation;
  w ≥ 0; exact closure arithmetic incl. margins; brute-force blow-up lemma;
  transfer/rounding identities for n = 1..40.
- `brute_check.c` — independent C ground truth, n = 5..12 via
  `geng -q -t n | ./brute_check n` (n=12: 4.9 s single-threaded).
- Author's gate + author's brute script (patched geng path), logs saved.
- `upstream/` — producer frozen logs, `prove_cert.py`/`flag_exact.py`,
  BCL PDF, fetched from GitHub/arXiv for the record.

## Formalizability scoping (checker only, not the flag algebra)

Target shape (matches this repo's decide-certificate idioms, no
`native_decide`):

```
-- elementary layer (provable outright, no data)
theorem blowup_mc  : mc (G.blowup t) = t^2 * mc G            -- multilinearity
theorem blowup_bip : β (G.blowup t) = t^2 * β G
theorem integrality (h : (β G : ℚ) ≤ n^2 + (25/2)*n^2*δ)
    (hδ : (25/2)*n^2*δ < 1) : β G ≤ n^2

-- certificate layer (kernel computation on concrete rational data)
theorem cert_ok : CheckCert certData = true                  -- by decide-style eval
-- CheckCert = conditions (1)–(5): a7+a8=1, leg sums, per-state resid ≥ −ε,
--             δ_final formula, δ_final < 1/20000

-- trust boundary (stated hypotheses, NOT formalized now)
-- (H1) envelope/Horn/moment row validity for triangle-free graphons
--      (Lemma 3.1 + Razborov positivity)  ⇒  CheckCert ⇒ band bound
-- (H2) BCL tails (asymptotic) + blow-up transfer

theorem main (H1) (H2) : ∀ n ≤ 40, a (5*n) = n^2
```

Cost estimates:

- **Elementary layer** — small. Blow-up lemma: SimpleGraph blow-up +
  one-coordinate-at-a-time rounding of fractional cuts (pure convexity, no
  measure theory needed if the theorem is phrased finitely); ~300–600 lines
  with Mathlib. Integrality/threshold/transfer: `norm_num`-level; the exact
  δ is a 44/48-digit fraction — trivial for the kernel. The graphon can be
  eliminated from the *statement* entirely by phrasing H1's conclusion
  finitely ("∀ triangle-free H in band, 2β(H)/|H|² ≤ 2/25 + δ"), which is
  exactly what Cor 4.2-style blow-up transfer needs.
- **Certificate data size** — shipped compact form: 6,681 rationalized
  multipliers (denominators ≤ 10⁸) + 87 Gram atoms (dims ≤ 57) + 12,172
  moment-term rationals at ~355 digits each (~9 MB of digits) + 12,172
  R_cbh rationals. As Lean source ≈ 15–30 MB. Fine as a bank file.
- **Kernel work, thin checker** (take R_cbh and mom-term as certificate
  data; check w ≥ 0, a7+a8=1, resid[s] = R_cbh[s] − mom[s] ≥ −ε, δ formula,
  δ < 1/20000): ~13k comparisons + ~13k subtractions of ~350-digit rationals
  ≈ 10⁵–10⁶ bignum ops — comfortably `decide`-feasible with a
  common-denominator integer encoding (the repo's existing idiom). Days of
  work, not months. BUT the thin checker inherits R_cbh/mom-term as data, so
  it certifies only the final inequality assembly, not the row aggregation.
- **Kernel work, faithful checker** (re-derive R_cbh from the 6,359 envelope
  rows and mom-term from the 87 atoms through the order-9→10 lift): needs the
  unshipped state tables (est. 10⁶–10⁷ sparse rational entries, hundreds of
  MB) and ~10⁷–10⁸ big-rational multiply-adds — not realistic under
  kernel-only `decide`; would need serious staging (verified integer
  reflection, per-state witness compression) or a rethink of the certificate
  format upstream. This is where the real formalization cost lives, and it is
  exactly the part whose Python verification is also not reproducible from
  the arXiv package.
- Formalizing H1 itself (envelope soundness + Razborov positivity) is graphon
  /flag-algebra territory — out of scope by instruction, and Mathlib has no
  graphon layer; the finite reformulation above keeps it a clean, honest
  hypothesis.

## Hard stop

Per instructions: no LP extension attempted, no connected-B/Γ-invariant work
started.
